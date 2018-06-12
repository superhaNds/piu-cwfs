module Intrinsic.ExpSubCwf where

open import Data.Nat renaming (ℕ to Nat)

data Ctx : Nat → Set
data Ty  : ∀ {n} (Γ : Ctx n) → Set
data Tm  : ∀ {n} (Γ : Ctx n) (A : Ty Γ) → Set
data Sub : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) → Set

data _=T_ : ∀ {n} {Γ Γ' : Ctx n} → Ty Γ → Ty Γ' → Set
data _=t_ : ∀ {n} {Γ Γ' : Ctx n} {A : Ty Γ} {A' : Ty Γ'} → Tm Γ A → Tm Γ' A' → Set
data _=s_ : ∀ {m n} {Δ Δ' : Ctx m} {Γ Γ' : Ctx n} → Sub Δ Γ → Sub Δ' Γ' → Set

infix  5 _=T_
infix  5 _=t_
infix  5 _=s_
infix  20 _[_]T
infix  20 _[_]t
infixl 10 _,_
infixr 15 _∘_ 

data Ctx where
  ⋄    : Ctx 0
  _,_  : ∀ {n} (Γ : Ctx n) → Ty Γ → Ctx (1 + n)

data Ty where
  _[_]T : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n}
          → Ty Γ
          → Sub Δ Γ
          → Ty Δ

  U : ∀ {n} {Γ : Ctx n} → Ty Γ

  Π : ∀ {n} {Γ : Ctx n} (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ

data Sub where
  id : ∀ {n} {Γ : Ctx n} → Sub Γ Γ

  _∘_ : ∀ {m n k} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
        → Sub Γ Δ
        → Sub Θ Γ
        → Sub Θ Δ

  <> : ∀ {n} {Γ : Ctx n} → Sub Γ ⋄

  p : ∀ {n} {Γ : Ctx n} {A : Ty Γ} → Sub (Γ , A) Γ
  
  <_,_> : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ}
          → (γ : Sub Δ Γ)
          → Tm Δ (A [ γ ]T)
          → Sub Δ (Γ , A)

↑ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ} → (γ : Sub Δ Γ)
    → Sub (Δ , A [ γ ]T) (Γ , A)

data _=T_ where
  reflT : ∀ {n} {Γ : Ctx n} {A : Ty Γ} → A =T A
  
  symT : ∀ {n} {Γ : Ctx n} {A A' : Ty Γ}
         → A  =T A'
         → A' =T A
         
  transT : ∀ {n} {Γ : Ctx n} {A A' A'' : Ty Γ}
           → A  =T A'
           → A' =T A''
           → A  =T A''
           
  subIdT : ∀ {n} {Γ : Ctx n} {A : Ty Γ} → A [ id ]T =T A
  
  subCompT : ∀ {m n k} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
               {A : Ty Γ} {γ : Sub Δ Γ} {δ : Sub Θ Δ}
             → A [ γ ]T [ δ ]T =T A [ γ ∘ δ ]T

  subU : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → U [ γ ]T =T U {Γ = Δ}

  subΠ : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n}
           {γ : Sub Δ Γ} {A : Ty Γ} {B : Ty (Γ , A)}
         → (Π A B) [ γ ]T =T Π (A [ γ ]T) (B [ ↑ γ ]T)
                                                      
  cong-subT : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A A' : Ty Γ} {γ γ' : Sub Δ Γ}
              → A =T A'
              → γ =s γ'
              → A [ γ ]T =T A' [ γ' ]T

data Tm where
  q : ∀ {n} {Γ : Ctx n} {A : Ty Γ} → Tm (Γ , A) (A [ p ]T)

  _[_]t : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ}
          → Tm Γ A
          → (γ : Sub Δ Γ)
          → Tm Δ (A [ γ ]T)

  ƛ : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {B : Ty (Γ , A)}
      → Tm (Γ , A) B
      → Tm Γ (Π A B)

  transport : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {A' : Ty Γ}
              → Tm Γ A
              → A =T A'
              → Tm Γ A'

  app : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {B : Ty (Γ , A)}
        → Tm Γ (Π A B)
        → (a : Tm Γ A)
        → Tm Γ (B [ < id , transport a (symT subIdT) > ]T)

↑ γ = < γ ∘ p , transport (q {A = _ [ γ ]T}) subCompT >

data _=s_ where
  refls : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → γ =s γ

  syms : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ γ' : Sub Δ Γ}
         → γ  =s γ'
         → γ' =s γ

  transs : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ γ' γ'' : Sub Δ Γ}
           → γ  =s γ'
           → γ' =s γ''
           → γ  =s γ''

  idZero : id {Γ = ⋄} =s <> {Γ = ⋄}

  lzero : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → <> ∘ γ =s <> {Γ = Δ}

  idExt : ∀ {n} {Γ : Ctx n} {A : Ty Γ} → id {Γ = Γ , A} =s < p {Γ = Γ} {A} , q > 

  idL : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → γ ∘ id =s γ

  idR : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {γ : Sub Δ Γ} → id ∘ γ =s γ

  asso : ∀ {m n k j} {Ξ : Ctx j} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
           {γ₁ : Sub Δ Γ} {γ₂ : Sub Θ Δ} {γ₃ : Sub Ξ Θ}
         → (γ₁ ∘ γ₂) ∘ γ₃ =s γ₁ ∘ (γ₂ ∘ γ₃)

  cons-∘ : ∀ {m n k} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n}
             {γ : Sub Δ Γ} {A : Ty Γ} {a : Tm Δ (A [ γ ]T)} {δ : Sub Θ Δ}
           → < γ , a > ∘ δ =s < γ ∘ δ , transport (a [ δ ]t) subCompT >

  pcons : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ}
            {γ : Sub Δ Γ} {a : Tm Δ (A [ γ ]T)}
          → p ∘ < γ , a > =s γ

  cong-∘ : ∀ {m n k} {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k}
             {γ γ' : Sub Δ Θ} {δ δ' : Sub Γ Δ}
           → γ =s γ'
           → δ =s δ'
           → γ ∘ δ =s γ' ∘ δ'

  cong-cons : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ} {γ γ' : Sub Δ Γ}
                {a : Tm Δ (A [ γ ]T)} {a' : Tm Δ (A [ γ' ]T)}
              → γ =s γ'
              → a =t a'
              → < γ , a > =s < γ' , a' >

data _=t_ where
  reflt : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {a : Tm Γ A} → a =t a
  
  symt  : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {a a' : Tm Γ A}
          → a  =t a'
          → a' =t a

  transt : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {a a' a'' : Tm Γ A}
           → a  =t a'
           → a' =t a''
           → a  =t a''

  subIdt : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {a : Tm Γ A} → a [ id ]t =t a

  subCompt : ∀ {m n k} {Θ : Ctx k} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ}
               {a : Tm Γ A} {γ : Sub Δ Γ} {δ : Sub Θ Δ}
             → a [ γ ]t [ δ ]t =t a [ γ ∘ δ ]t

  subLam : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ} {B : Ty (Γ , A)}
             {a : Tm (Γ , A) B} {γ : Sub Δ Γ}
           → (ƛ a) [ γ ]t =t ƛ (a [ ↑ γ ]t)

  subApp : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ} {B : Ty (Γ , A)}
             {c : Tm Γ (Π A B)} {a : Tm Γ A} {γ : Sub Δ Γ}
           → (app c a) [ γ ]t =t app (transport (c [ γ ]t) subΠ) (a [ γ ]t)

  qcons : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ}
            {γ : Sub Δ Γ} {a : Tm Δ (A [ γ ]T)}
          → q [ < γ , a > ]t =t a
          
  β : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {B : Ty (Γ , A)} {a : Tm (Γ , A) B} {b : Tm Γ A}
      → app (ƛ a) b =t a [ < id , transport b (symT subIdT) > ]t

  η : ∀ {n} {Γ : Ctx n} {A : Ty Γ} {B : Ty (Γ , A)} {a : Tm Γ (Π A B)}
      → ƛ (app (transport (a [ p ]t) subΠ) q) =t a

  cong-subt : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A : Ty Γ}
                {a a' : Tm Γ A} {γ γ' : Sub Δ Γ}
              → a =t a'
              → γ =s γ'
              → a [ γ ]t =t a' [ γ' ]t
