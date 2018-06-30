module ExtPure where

open import Data.Nat renaming (ℕ to Nat)
open import Function using (_$_)

{-

Here I have defined a cwf of explicit substitutions with typed equality judgements,
without lambdas, Π, etc yet.

There are two pairs of four relations with the usual meanings as you know them

- Γ ⊢ 
- Γ ⊢ A
- Γ ⊢ a ∈ A
- Δ ⇒ Γ ⊢ γ (terms are typed in Δ)

- Γ ≡ Γ ⊢
- Γ ⊢ A ≡ A'
- Γ ⊢ a ≡ a' ∈ A
- Δ ⇒ Γ ⊢ γ ≡ γ' 

All of those have to be defined mutually because of the coerce rules that are necessary, i.e. for terms we need

    Γ ⊢ A ≡ A'  Γ ⊢ a ∈ A
  --------------------------- 
         Γ' ⊢ a ∈ A'
   
a similar coerce rule is needed for each of the other three relations of well-formedness


These coerce rules are necessary in order to prove some fundamental admissible laws of the type system, e.g.,

    Γ ≡ Γ' ⊢        Γ ⊢ A ≡ A'
 -------------    -------------     
   Γ ⊢ ∧ Γ' ⊢      Γ ⊢ A ∧ Γ ⊢ A'

And similarly or terms and substitutions

An issue in proving these laws is that we need a lot of annotations on the constructors of our calculus.
For example, there is a need for premises like Γ ⊢ and Γ ⊢ A in the same rule.

I'm not sure whether properties like 

 Γ ⊢ A        Δ ⇒ Γ ⊢ γ
 ------ or  -------------
  Γ ⊢          Δ ⊢ ∧ Γ ⊢

can be mutually proven with the ones I mention above with equality. Odds are, there will be circularity in the proofs, at least in Agda's view.

And are they necessary? Is this related to something called coherence?


Final points:

It's not entirely clear to me how should the calculus be. Maybe it just comes down to choice.

A few possibilities I have seen are:

- Separate terms and types
- use contexts in raw terms (like in TLCA 2015)
- use only four relations with equality and define the wellformdness relations via the other, e.g. for types: Γ ⊢ A = Γ ⊢ A ≡ A 

-}

data Exp : Nat → Set
data Sub : Nat → Nat → Set

data Exp where
  q    : ∀ {n}                               → Exp (1 + n)
  _[_] : ∀ {m n} (a : Exp n) (γ : Sub m n)   → Exp m

data Sub where
  id    : ∀ {n}                                 → Sub n n
  _∘_   : ∀ {k m n} (γ : Sub n k) (δ : Sub m n) → Sub m k
  <>    : ∀ {n}                                 → Sub n 0
  p     : ∀ {n}                                 → Sub (1 + n) n
  <_,_> : ∀ {m n} (γ : Sub m n) (a : Exp m)     → Sub m (1 + n)

data Ctx : Nat → Set where
  ⋄   : Ctx 0
  _,_ : ∀ {n} (Γ : Ctx n) (A : Exp n) → Ctx (suc n)

_⁺ : ∀ {m n} (γ : Sub m n) → Sub (1 + m) (1 + n)
γ ⁺ = < γ ∘ p , q >

mutual

  data _⊢ : ∀ {n} (Γ : Ctx n) → Set where
    c-emp : ⋄ ⊢
    
    c-ext : ∀ {n} {Γ : Ctx n} {A}
            → Γ ⊢
            → Γ ⊢ A
            → Γ , A ⊢

  data _⊢_ : ∀ {n} (Γ : Ctx n) (A : Exp n) → Set where
    ty-sub : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A γ}
             → Γ ⊢ A
             → Δ ⇒ Γ ⊢ γ
             → Δ ⊢ A [ γ ]

    ty-coe : ∀ {n} {Γ Γ' : Ctx n} {A}
             → Γ ≡ Γ' ⊢
             → Γ ⊢ A
             → Γ' ⊢ A

  data _⊢_∈_ : ∀ {n} (Γ : Ctx n) (a : Exp n) (A : Exp n) → Set where
    tm-q : ∀ {n} {Γ : Ctx n} {A}
           → Γ ⊢ A
           → Γ , A ⊢ q ∈ A [ p ]

    tm-sub : ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A a γ}
             → Γ ⊢ a ∈ A
             → Δ ⇒ Γ ⊢ γ
             → Δ ⊢ a [ γ ] ∈ A [ γ ]

    tm-coe : ∀ {n} {Γ Γ' : Ctx n} {A A' a}
             → Γ ⊢ A ≡ A'
             → Γ ⊢ a ∈ A
             → Γ' ⊢ a ∈ A'
   
  data _⇒_⊢_ : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) (γ : Sub m n) → Set where
    sub-id : ∀ {n} {Γ : Ctx n}
             → Γ ⊢
             → Γ ⇒ Γ ⊢ id

    sub-∘ : ∀ {k m n Θ Δ Γ} {γ : Sub n k} {γ' : Sub m n}
            → Γ ⇒ Θ ⊢ γ
            → Δ ⇒ Γ ⊢ γ'
            → Δ ⇒ Θ ⊢ γ ∘ γ'

    sub-<> : ∀ {n} {Γ : Ctx n}
             → Γ ⊢
             → Γ ⇒ ⋄ ⊢ <>

    sub-p : ∀ {n} {Γ : Ctx n} {A}
            → Γ ⊢ A
            → (Γ , A) ⇒ Γ ⊢ p

    sub-<,> : ∀ {m n Δ Γ A a} {γ : Sub m n}
              → Δ ⇒ Γ ⊢ γ
              → Γ ⊢ A
              → Δ ⊢ a ∈ A [ γ ]
              → Δ ⇒ (Γ , A) ⊢ < γ , a >

    sub-coe : ∀ {m n} {Δ Δ' : Ctx m} {Γ Γ' : Ctx n} {γ : Sub m n} 
              → Γ ≡ Γ' ⊢
              → Δ ≡ Δ' ⊢
              → Δ  ⇒ Γ  ⊢ γ
              → Δ' ⇒ Γ' ⊢ γ

  data _≡_⊢ : ∀ {n} (Γ Γ' : Ctx n) → Set where
    c-sym : ∀ {n} {Γ Γ' : Ctx n}
          → Γ  ≡ Γ' ⊢
          → Γ' ≡ Γ ⊢

    c-trans : ∀ {n} {Γ Γ' Γ'' : Ctx n}
            → Γ  ≡ Γ'  ⊢
            → Γ' ≡ Γ'' ⊢
            → Γ  ≡ Γ'' ⊢
 
    c-empteq : ⋄ ≡ ⋄ ⊢

    c-extcong : ∀ {n} {Γ Γ' : Ctx n} {A A'}
              → Γ ≡ Γ' ⊢
              → Γ ⊢ A ≡ A'
              → (Γ , A) ≡ (Γ' , A') ⊢


  data _⊢_≡_ : ∀ {n} (Γ : Ctx n) (A A' : Exp n) → Set where
    ty-sym : ∀ {n} {Γ : Ctx n} {A A'}
             → Γ ⊢ A  ≡ A'
             → Γ ⊢ A' ≡ A

    ty-trans : ∀ {n} {Γ : Ctx n} {A A' A''}
               → Γ ⊢ A  ≡ A'
               → Γ ⊢ A' ≡ A''
               → Γ ⊢ A  ≡ A''

    ty-pres : ∀ {n} {Γ Γ' : Ctx n} {A A'}
              → Γ ≡ Γ' ⊢
              → Γ  ⊢ A ≡ A'
              → Γ' ⊢ A ≡ A'

    ty-congsub : ∀ {m n Δ Γ} {γ γ' : Sub m n} {A A'}
                 → Γ ⊢ A ≡ A'
                 → Δ ⇒ Γ ⊢ γ ≡ γ'
                 → Δ ⊢ A [ γ ] ≡ A' [ γ' ]

    ty-subId : ∀ {n A} {Γ : Ctx n}
               → Γ ⊢
               → Γ ⊢ A
               → Γ ⊢ A [ id ] ≡ A

    ty-subComp : ∀ {k m n Θ Δ Γ A} {γ : Sub n k} {δ : Sub m n}
                 → Γ ⊢ A
                 → Δ ⇒ Γ ⊢ γ
                 → Θ ⇒ Δ ⊢ δ
                 → Θ ⊢ A [ γ ∘ δ ] ≡ (A [ γ ]) [ δ ]

  data _⊢_≡_∈_ : ∀ {n} (Γ : Ctx n) (a a' : Exp n) (A : Exp n) → Set where
    tm-sym : ∀ {n} {Γ : Ctx n} {a a' A}
             → Γ ⊢ a  ≡ a' ∈ A
             → Γ ⊢ a' ≡ a  ∈ A
             
    tm-trans : ∀ {n} {Γ : Ctx n} {a a' a'' A}
               → Γ ⊢ a  ≡ a'  ∈ A
               → Γ ⊢ a' ≡ a'' ∈ A
               → Γ ⊢ a  ≡ a'' ∈ A

    tm-pres : ∀ {n} {Γ Γ' : Ctx n} {a a' A A'}
              → Γ ≡ Γ' ⊢
              → Γ ⊢ A ≡ A'
              → Γ  ⊢ a ≡ a' ∈ A
              → Γ' ⊢ a ≡ a' ∈ A'

    tm-subId : ∀ {n} {Γ : Ctx n} {a A}
               → Γ ⊢
               → Γ ⊢ A
               → Γ ⊢ a ∈ A
               → Γ ⊢ a [ id ] ≡ a ∈ A

    tm-qeq : ∀ {m n Δ Γ} {γ : Sub m n} {a A}
             → Γ ⊢
             → Γ ⊢ A
             → Δ ⇒ Γ ⊢ γ
             → Δ ⊢ a ∈ A [ γ ]
             → Δ ⊢ q [ < γ , a > ] ≡ a ∈ A [ γ ]
           
    tm-subComp : ∀ {k m n a A Θ Δ Γ } {γ : Sub n k} {δ : Sub m n}
                 → Γ ⊢ A
                 → Γ ⊢ a ∈ A
                 → Δ ⇒ Γ ⊢ γ
                 → Θ ⇒ Δ ⊢ δ
                 → Θ ⊢ a [ γ ∘ δ ] ≡ (a [ γ ]) [ δ ] ∈ (A [ γ ]) [ δ ]

    tm-congsub : ∀ {m n Δ Γ} {γ γ' : Sub m n} {a a' A}
                 → Γ ⊢
                 → Δ ⊢
                 → Γ ⊢ A
                 → Γ ⊢ a ≡ a' ∈ A
                 → Δ ⇒ Γ ⊢ γ ≡ γ'
                 → Δ ⊢ a [ γ ] ≡ a' [ γ' ] ∈ A [ γ ]

  data _⇒_⊢_≡_ : ∀ {m n} (Δ : Ctx m) (Γ : Ctx n) (γ γ' : Sub m n) → Set where
     s-sym : ∀ {m n Δ Γ} {γ γ' : Sub m n}
             → Δ ⇒ Γ ⊢ γ  ≡ γ'
             → Δ ⇒ Γ ⊢ γ' ≡ γ

     s-trans : ∀ {m n Δ Γ} {γ γ' γ'' : Sub m n}
               → Δ ⇒ Γ ⊢ γ  ≡ γ'
               → Δ ⇒ Γ ⊢ γ' ≡ γ''
               → Δ ⇒ Γ ⊢ γ  ≡ γ''

     s-pres : ∀ {m n Δ Δ' Γ Γ'} {γ γ' : Sub m n}
              → Γ ≡ Γ' ⊢
              → Δ ≡ Δ' ⊢
              → Δ  ⇒ Γ  ⊢ γ ≡ γ'
              → Δ' ⇒ Γ' ⊢ γ ≡ γ'

     s-id⋄ : ∀ {n} {Γ : Ctx n} → ⋄ ⇒ ⋄ ⊢ id ≡ <>

     s-idExt : ∀ {n} {Γ : Ctx n} {A}
               → Γ ⊢
               → Γ ⊢ A
               → (Γ , A) ⇒ (Γ , A) ⊢ id {1 + n} ≡ < p , q >

     s-lzero : ∀ {m n Δ Γ} {γ : Sub m n}
               → Γ ⊢
               → Δ ⊢
               → Δ ⇒ Γ ⊢ γ
               → Δ ⇒ ⋄ ⊢ <> ∘ γ ≡ <>

     s-ext : ∀ {m n Δ Γ} {γ γ' : Sub m n} {a a' A}
             → Γ ⊢
             → Γ ⊢ A
             → Δ ⊢ A [ γ ]
             → Δ ⇒ Γ ⊢ γ ≡ γ'
             → Δ ⊢ a ≡ a' ∈ (A [ γ ])
             → Δ ⇒ (Γ , A) ⊢ < γ , a > ≡ < γ' , a' >

     s-extComp : ∀ {k m n Δ Γ Θ} {γ : Sub n k} {δ : Sub m n} {a A}
                 → Θ ⊢ A
                 → Γ ⊢ a ∈ A [ γ ]
                 → Δ ⇒ Γ ⊢ δ
                 → Γ ⇒ Θ ⊢ γ
                 → Δ ⇒ (Θ , A) ⊢ < γ , a > ∘ δ ≡ < γ ∘ δ , a [ δ ] >

     s-congcomp : ∀ {k m n Θ Δ Γ} {γ γ' : Sub n k} {δ δ' : Sub m n}
                  → Δ ⇒ Γ ⊢ δ ≡ δ'
                  → Γ ⇒ Θ ⊢ γ ≡ γ'
                  → Δ ⇒ Θ ⊢ γ ∘ δ ≡ γ' ∘ δ'

     s-p-∘ : ∀ {m n Δ Γ} {γ : Sub m n} {a A}
             → Γ ⊢ A
             → Δ ⇒ Γ ⊢ γ
             → Δ ⊢ a ∈ A [ γ ]
             → Δ ⇒ Γ ⊢ p ∘ < γ , a > ≡ γ

     s-assoc : ∀ {j k m n} {Ξ : Ctx j} {Θ : Ctx k}
                 {Δ : Ctx m} {Γ : Ctx n} {θ δ γ}
               → Γ ⇒ Θ ⊢ θ
               → Δ ⇒ Γ ⊢ δ
               → Ξ ⇒ Δ ⊢ γ
               → Ξ ⇒ Θ ⊢ (θ ∘ δ) ∘ γ ≡ θ ∘ (δ ∘ γ)

     s-idR : ∀ {m n Δ Γ} {γ : Sub m n}
             → Γ ⊢
             → Δ ⊢
             → Δ ⇒ Γ ⊢ γ
             → Δ ⇒ Γ ⊢ γ ∘ id ≡ γ

     s-idL : ∀ {m n Δ Γ} {γ : Sub m n}
             → Γ ⊢
             → Δ ⊢
             → Δ ⇒ Γ ⊢ γ
             → Δ ⇒ Γ ⊢ id ∘ γ ≡ γ

infix 5 _⊢
infix 5 _⊢_
infix 5 _⊢_∈_
infix 5 _⇒_⊢_

infix 5 _⊢_≡_
infix 5 _≡_⊢
infix 5 _⊢_≡_∈_
infix 5 _⇒_⊢_≡_

ty-refl : ∀ {n} {Γ : Ctx n} {A}
          → Γ ⊢
          → Γ ⊢ A
          → Γ ⊢ A ≡ A
ty-refl Γ⊢ ⊢A = ty-trans (ty-sym $ ty-subId Γ⊢ ⊢A) (ty-subId Γ⊢ ⊢A)          

c-refl : ∀ {n} {Γ : Ctx n}
         → Γ ⊢
         → Γ ≡ Γ ⊢
c-refl {Γ = ⋄}     c-emp         = c-empteq
c-refl {Γ = Γ , A} (c-ext Γ⊢ ⊢A) =
  c-extcong (c-refl Γ⊢) (ty-trans (ty-sym (ty-subId Γ⊢ ⊢A)) (ty-subId Γ⊢ ⊢A))

tm-refl : ∀ {n} {Γ : Ctx n} {a A}
          → Γ ⊢
          → Γ ⊢ A
          → Γ ⊢ a ∈ A
          → Γ ⊢ a ≡ a ∈ A
tm-refl Γ⊢ ⊢A ⊢a = tm-trans (tm-sym $ tm-subId Γ⊢ ⊢A ⊢a) (tm-subId Γ⊢ ⊢A ⊢a)          

s-refl : ∀ {m n Δ Γ} {γ : Sub m n}
         → Γ ⊢
         → Δ ⊢ 
         → Δ ⇒ Γ ⊢ γ
         → Δ ⇒ Γ ⊢ γ ≡ γ
s-refl Γ⊢ Δ⊢ ⊢γ = s-trans (s-sym $ s-idR Γ⊢ Δ⊢ ⊢γ) (s-idR Γ⊢ Δ⊢ ⊢γ)         

emptySub : ∀ {m Δ} {γ : Sub m 0}
           → Δ ⊢ 
           → Δ ⇒ ⋄ ⊢ γ
           → Δ ⇒ ⋄ ⊢ γ ≡ <>
emptySub {Δ = Δ} Δ⊢ ⊢γ =
  s-trans (s-sym $ s-idL c-emp Δ⊢ ⊢γ)
          (s-trans (s-congcomp (s-refl c-emp Δ⊢ ⊢γ) (s-id⋄ {Γ = Δ}))
                   (s-lzero c-emp Δ⊢ ⊢γ))

wk-sub-ext : ∀ {m n Γ Δ} {γ : Sub m n} {A a}
             → Δ ⊢
             → Δ ⊢ A
             → Γ ⇒ Δ ⊢ γ
             → Γ ⊢ a ∈ A [ γ ]
             → Γ ⊢ (A [ p ]) [ < γ , a > ] ≡ A [ γ ]
wk-sub-ext Δ⊢ ⊢A ⊢γ ⊢a =
  ty-trans (ty-sym $ ty-subComp ⊢A (sub-p ⊢A) (sub-<,> ⊢γ ⊢A ⊢a))
           (ty-congsub (ty-refl Δ⊢ ⊢A) (s-p-∘ ⊢A ⊢γ ⊢a))             

wf⁻¹ : ∀ {n} {Γ : Ctx n} {A} → Γ , A ⊢ → Γ ⊢
wf⁻¹ (c-ext Γ⊢ _) = Γ⊢

wf⁻² : ∀ {n} {Γ : Ctx n} {A} → Γ , A ⊢ → Γ ⊢ A
wf⁻² (c-ext _ ⊢A) = ⊢A

-- Equality implies well-formedness

c-eq₁ : ∀ {n} {Γ Γ' : Ctx n} → Γ ≡ Γ' ⊢ → Γ ⊢
c-eq₂ : ∀ {n} {Γ Γ' : Ctx n} → Γ ≡ Γ' ⊢ → Γ' ⊢

ty-eq₁ : ∀ {n} {Γ : Ctx n} {A A'} → Γ ⊢ A ≡ A' → Γ ⊢ A
ty-eq₂ : ∀ {n} {Γ : Ctx n} {A A'} → Γ ⊢ A ≡ A' → Γ ⊢ A'

tm-eq₁ : ∀ {n} {Γ : Ctx n} {a a' A} → Γ ⊢ a ≡ a' ∈ A → Γ ⊢ a ∈ A
tm-eq₂ : ∀ {n} {Γ : Ctx n} {a a' A} → Γ ⊢ a ≡ a' ∈ A → Γ ⊢ a' ∈ A

sub-eq₁ : ∀ {m n Δ Γ} {γ γ' : Sub m n} → Δ ⇒ Γ ⊢ γ ≡ γ' → Δ ⇒ Γ ⊢ γ
sub-eq₂ : ∀ {m n Δ Γ} {γ γ' : Sub m n} → Δ ⇒ Γ ⊢ γ ≡ γ' → Δ ⇒ Γ ⊢ γ'

c-eq₁ (c-sym x)       = c-eq₂ x
c-eq₁ (c-trans x _)   = c-eq₁ x
c-eq₁ c-empteq        = c-emp
c-eq₁ (c-extcong x y) = c-ext (c-eq₁ x) (ty-eq₁ y)
c-eq₂ (c-sym x)       = c-eq₁ x
c-eq₂ (c-trans x y)   = c-eq₂ y
c-eq₂ c-empteq        = c-emp
c-eq₂ (c-extcong x y) = c-ext (c-eq₂ x) (ty-coe x (ty-eq₂ y))

ty-eq₁ (ty-sym x)         = ty-eq₂ x
ty-eq₁ (ty-trans x y)     = ty-eq₁ x
ty-eq₁ (ty-pres x y)      = ty-coe x (ty-eq₁ y)
ty-eq₁ (ty-congsub x y)   = ty-sub (ty-eq₁ x) (sub-eq₁ y)
ty-eq₁ (ty-subId x y)     = ty-sub y (sub-id x)
ty-eq₁ (ty-subComp x y z) = ty-sub x (sub-∘ y z)
ty-eq₂ (ty-sym x)         = ty-eq₁ x
ty-eq₂ (ty-trans x y)     = ty-eq₂ y
ty-eq₂ (ty-pres x y)      = ty-coe x (ty-eq₂ y)
ty-eq₂ (ty-congsub x y)   = ty-sub (ty-eq₂ x) (sub-eq₂ y)
ty-eq₂ (ty-subId x y)     = y
ty-eq₂ (ty-subComp x y z) = ty-sub (ty-sub x y) z

sub-eq₁ (s-sym x)           = sub-eq₂ x
sub-eq₁ (s-trans x y)       = sub-eq₁ x
sub-eq₁ (s-pres x y z)      = sub-coe x y (sub-eq₁ z)
sub-eq₁ s-id⋄               = sub-id c-emp
sub-eq₁ (s-idExt z x)       = sub-id (c-ext (z) x)
sub-eq₁ (s-lzero w z x)     = sub-∘ (sub-<> (w)) x
sub-eq₁ (s-ext _ x _ y z)   = sub-<,> (sub-eq₁ y) x (tm-eq₁ z)
sub-eq₁ (s-extComp x y z w) = sub-∘ (sub-<,> w x y) z
sub-eq₁ (s-congcomp x y)    = sub-∘ (sub-eq₁ y) (sub-eq₁ x)
sub-eq₁ (s-p-∘ x y z)       = sub-∘ (sub-p x) (sub-<,> y x z)
sub-eq₁ (s-assoc x y z)     = sub-∘ (sub-∘ x y) z
sub-eq₁ (s-idR z w x)       = sub-∘ x (sub-id (w))
sub-eq₁ (s-idL z w x)       = sub-∘ (sub-id (z)) x

sub-eq₂ (s-sym x)           = sub-eq₁ x
sub-eq₂ (s-trans x y)       = sub-eq₂ y
sub-eq₂ (s-pres x y z)      = sub-coe x y (sub-eq₂ z)
sub-eq₂ s-id⋄               = sub-<> c-emp
sub-eq₂ (s-idExt w x)       = sub-<,> (sub-p x) x (tm-q x)
sub-eq₂ (s-lzero r w x)     = sub-<> w
sub-eq₂ (s-ext w x r y z)   = sub-<,> (sub-eq₂ y) x (tm-coe (ty-congsub (ty-refl w x) y) (tm-eq₂ z))
sub-eq₂ (s-extComp x y z w) = sub-<,> (sub-∘ w z) x (tm-coe (ty-sym (ty-subComp x w z)) (tm-sub y z)) 
sub-eq₂ (s-congcomp x y)    = sub-∘ (sub-eq₂ y) (sub-eq₂ x)
sub-eq₂ (s-p-∘ x y z)       = y
sub-eq₂ (s-assoc x y z)     = sub-∘ x (sub-∘ y z)
sub-eq₂ (s-idR z w x)       = x
sub-eq₂ (s-idL z w x)       = x

tm-eq₁ (tm-sym x)             = tm-eq₂ x
tm-eq₁ (tm-trans x y)         = tm-eq₁ x
tm-eq₁ (tm-subId x y z)       = tm-coe (ty-subId x y) (tm-sub z (sub-id x)) 
tm-eq₁ (tm-qeq w x y z)       = tm-coe (wk-sub-ext w x y z) (tm-sub (tm-q x) (sub-<,> y x z))
tm-eq₁ (tm-subComp w x y z)   = tm-coe (ty-subComp w y z) (tm-sub x (sub-∘ y z))
tm-eq₁ (tm-congsub _ _ _ x y) = tm-sub (tm-eq₁ x) (sub-eq₁ y)
tm-eq₁ (tm-pres x y z)        = tm-coe y (tm-eq₁ z)

tm-eq₂ (tm-sym x)             = tm-eq₁ x
tm-eq₂ (tm-trans x y)         = tm-eq₂ y
tm-eq₂ (tm-pres x y z)        = tm-coe  y (tm-eq₂ z)
tm-eq₂ (tm-subId _ _ x)       = x
tm-eq₂ (tm-qeq _ x y z)       = z
tm-eq₂ (tm-subComp _ x y z)   = tm-sub (tm-sub x y) z
tm-eq₂ (tm-congsub w _ t x y) = tm-coe (ty-congsub (ty-refl w t) (s-sym y)) (tm-sub (tm-eq₂ x) (sub-eq₂ y)) 
