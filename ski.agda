open import Data.String
open import Data.Integer hiding (suc)
open import Data.Nat

Id : Set
Id = ℕ

infixr 20 _⇒_ 

data Type : Set where
  `Int  : Type
  `Unit : Type
  _⇒_  : Type → Type → Type

data Term : Set where
  EUnit : Term
  EInt : ℤ → Term

  EVar : Id → Term

  ELam : Id -> Type → Term → Term
  EApp : Term → Term → Term


data Context : Set where
  · : Context
  _,_⦂_ : Context → Id -> Type → Context

data _⊢_⦂_ : Context → Term -> Type → Set where
  UnitTyping : ∀ {Γ} → Γ ⊢ EUnit ⦂ `Unit
  IntTyping : ∀ {Γ i} → Γ ⊢ EInt i ⦂ `Int

  LastVarTyping : ∀ {Γ A} → ( Γ , 0 ⦂ A ) ⊢ EVar 0 ⦂ A
  NextVarTyping : ∀ {Γ x A B} →
                    Γ         ⊢ EVar x ⦂ A →
                    ( Γ , 0 ⦂ B ) ⊢ EVar (suc x) ⦂ A

  ELamTyping : ∀ {Γ x A B m} → ( Γ , x ⦂ A ) ⊢ m ⦂ B
                           → Γ ⊢ ELam x A m ⦂ (A ⇒ B)

  EAppTyping : ∀ {Γ A B f m} → Γ ⊢ f ⦂ (A ⇒ B)
                             → Γ ⊢ m ⦂ A
                             → Γ ⊢ EApp f m ⦂ B

data SKI : Set where
  SKIUnit : SKI
  SKIInt : ℤ → SKI
  SKIVar : Id → SKI
  SKIApp : SKI → SKI → SKI
  S : SKI 
  K : SKI
  I : SKI

infixl 20 _α_
_α_ = SKIApp

data _⊨_⦂_ : Context -> SKI -> Type -> Set where
  SKIUnitTyping : ∀ {Γ} → Γ ⊨ SKIUnit ⦂ `Unit
  STyping : ∀ {Γ A B C} → Γ ⊨ S ⦂ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  KTyping : ∀ {Γ A B} → Γ ⊨ K ⦂ (A ⇒ B ⇒ A)
  ITyping : ∀ {Γ A} → Γ ⊨ I ⦂ (A ⇒ A)
  SKIIntTyping : ∀ {Γ n} → Γ ⊨ (SKIInt n) ⦂ `Int
  SKILastVarTyping : ∀ {Γ A} → ( Γ , 0 ⦂ A ) ⊨ SKIVar 0 ⦂ A
  SKINextVarTyping : ∀ {Γ x A B} → Γ ⊨ SKIVar x ⦂ A →
                    ( Γ , 0 ⦂ B ) ⊨ SKIVar (suc x) ⦂ A
  SKIAppTyping : ∀ {Γ A B M N} → Γ ⊨ M ⦂ (A ⇒ B)
                             → Γ ⊨ N ⦂ A
                             → Γ ⊨ SKIApp M N ⦂ B


transLam : Id → Type → SKI → SKI
transLam x A SKIUnit = K α SKIUnit
transLam x A (SKIInt n) = K α SKIInt n
transLam zero A (SKIVar zero) = I
transLam zero A (SKIVar (suc n)) = K α (SKIVar n)
transLam x A (SKIVar _) = {!!} -- Should never happen...
transLam x A (SKIApp M N) = S α transLam x A M α transLam x A N
transLam x A S = K α S
transLam x A K = K α K
transLam x A I = K α I

toSKI : Term → SKI
toSKI EUnit = SKIUnit
toSKI (EInt x) = SKIInt x
toSKI (EVar x) = SKIVar x
toSKI (ELam x A M) = transLam x A (toSKI M)
toSKI (EApp M N) = SKIApp (toSKI M) (toSKI N)


lamTransLem : ∀ {Γ x A B M} → (Γ , x ⦂ A) ⊨ M ⦂ B → Γ ⊨ transLam x A M ⦂ (A ⇒ B)
lamTransLem SKIUnitTyping = SKIAppTyping KTyping SKIUnitTyping
lamTransLem STyping = SKIAppTyping KTyping STyping
lamTransLem KTyping = SKIAppTyping KTyping KTyping
lamTransLem ITyping = SKIAppTyping KTyping ITyping
lamTransLem SKIIntTyping = SKIAppTyping KTyping SKIIntTyping
lamTransLem SKILastVarTyping = ITyping
lamTransLem (SKINextVarTyping pf) = SKIAppTyping KTyping pf
lamTransLem (SKIAppTyping pf1 pf2) = SKIAppTyping (SKIAppTyping STyping (lamTransLem pf1)) (lamTransLem pf2)

fundamentalThm : ∀ {Γ M A} → Γ ⊢ M ⦂ A → Γ ⊨ toSKI M ⦂ A
fundamentalThm UnitTyping = SKIUnitTyping
fundamentalThm IntTyping = SKIIntTyping
fundamentalThm LastVarTyping = SKILastVarTyping
fundamentalThm (NextVarTyping pf) = SKINextVarTyping (fundamentalThm pf)
fundamentalThm (ELamTyping pf) = let ih = fundamentalThm pf in lamTransLem ih
fundamentalThm (EAppTyping pf1 pf2) = SKIAppTyping (fundamentalThm pf1) (fundamentalThm pf2)
