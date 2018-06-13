module Iso where

open import Data.Nat renaming (ℕ to Nat)
open import Data.Product using (Σ)
open import Extrinsic.ExpSubLam renaming (Tm to RTm ; Sub to RSub)
open import Extrinsic.ExpSubTy
open import Intrinsic.ExpSubCwf renaming (Ctx to Ctx⋆ ; _∘_ to _∘⋆_)

mutual

  stripctx : ∀ {n} (Γ : Ctx⋆ n) → Ctx n
  stripctx ⋄       = ⋄
  stripctx (Γ , A) = stripctx Γ ∙ stripty A

  stripty : ∀ {n} {Γ : Ctx⋆ n} (A : Ty Γ) → RTm n
  stripty (A [ γ ]T) = stripty A [ stripsub γ ]
  stripty U          = U
  stripty (Π A B)    = Π (stripty A) (stripty B)

  striptm : ∀ {n} {Γ : Ctx⋆ n} {A : Ty Γ} (a : Tm Γ A) → RTm n
  striptm q                = q
  striptm (a [ γ ]t)       = striptm a [ stripsub γ ]
  striptm (ƛ a)            = ƛ (striptm a)
  striptm (transport a eq) = striptm a
  striptm (app c a)        = app (striptm c) (striptm a)

  stripsub : ∀ {m n} {Δ : Ctx⋆ m} {Γ : Ctx⋆ n} (γ : Sub Δ Γ) → RSub m n
  stripsub id        = id
  stripsub (γ ∘⋆ γ') = stripsub γ ∘ stripsub γ'
  stripsub <>        = <>
  stripsub p         = p
  stripsub < γ , a > = < stripsub γ , striptm a >

  striptyeq : ∀ {n} {Γ : Ctx⋆ n} {A A' : Ty Γ} → A =T A' → stripty A ~ stripty A'
  striptyeq reflT                 = refl~
  striptyeq (symT A=A')           = sym~ (striptyeq A=A')
  striptyeq (transT A=A' A=A'')   = trans~ (striptyeq A=A') (striptyeq A=A'')
  striptyeq (subIdT )             = subId
  striptyeq subCompT              = sym~ subComp
  striptyeq subU                  = subU
  striptyeq subΠ                  = subΠ
  striptyeq (cong-subT A=A' γ=γ') = cong-sub (striptyeq A=A') (stripsubeq γ=γ')

  striptmeq : ∀ {n} {Γ : Ctx⋆ n} {A : Ty Γ} {a a' : Tm Γ A} → a =t a' → striptm a ~ striptm a'
  striptmeq reflt                 = refl~
  striptmeq (symt a=a')           = sym~ (striptmeq a=a')
  striptmeq (transt a=a' a=a'')   = trans~ (striptmeq a=a') (striptmeq a=a'')
  striptmeq β                     = β
  striptmeq (cong-subt a=a' γ=γ') = cong-sub (striptmeq a=a') (stripsubeq γ=γ')

  stripsubeq : ∀ {m n} {Δ : Ctx⋆ m} {Γ : Ctx⋆ n} {γ γ' : Sub Δ Γ} → γ =s γ' → stripsub γ ≈ stripsub γ'
  stripsubeq refls                 = refl≈
  stripsubeq (syms γ=γ')           = sym≈ (stripsubeq γ=γ')
  stripsubeq (transs γ=γ' γ=γ'')   = trans≈ (stripsubeq γ=γ') (stripsubeq γ=γ'')
  stripsubeq idZero                = id-zero
  stripsubeq lzero                 = left-zero
  stripsubeq idExt                 = idExt
  stripsubeq idL                   = idR
  stripsubeq idR                   = idL
  stripsubeq asso                  = ∘-asso
  stripsubeq cons-∘                = compExt
  stripsubeq pcons                 = p-∘
  stripsubeq (cong-∘ γ=γ' γ=γ'')   = cong-∘ (stripsubeq γ=γ') (stripsubeq γ=γ'')
  stripsubeq (cong-cons {a = a} {a'} γ=γ' a=a') = cong-<,> {! !} (stripsubeq γ=γ')
    where a'' = transport a (cong-subT reflT γ=γ')

mutual

  typingctx : ∀ {n} (Γ : Ctx⋆ n) → stripctx Γ ⊢
  typingctx ⋄       = c-emp
  typingctx (Γ , A) = c-ext (typingctx Γ) (typingty A)

  typingty : ∀ {n} {Γ : Ctx⋆ n} (A : Ty Γ) → stripctx Γ ⊢ stripty A
  typingty (U)         = ty-U (typingctx _)
  typingty (A [ γ ]T)  = ty-sub (typingty A) (typingsub γ)  
  typingty (Π A B)     = ty-Π-F (typingty A) (typingty B)

  typingtm : ∀ {n} {Γ : Ctx⋆ n} {A : Ty Γ} (a : Tm Γ A) → stripctx Γ ⊢ striptm a ∈ stripty A
  typingtm q                 = tm-q (typingty _)
  typingtm (a [ γ ]t)        = tm-sub (typingtm a) (typingsub γ)
  typingtm (ƛ a)             = tm-Π-I (typingty _) (typingty _) (typingtm a)
  typingtm (transport a eq)  = tm-conv (typingty _) (typingtm a) (sym~ (striptyeq eq)) 
  typingtm (app c a)         = tm-app (typingty _) (typingty _) (typingtm c) (typingtm a)

  typingsub : ∀ {m n} {Δ : Ctx⋆ m} {Γ : Ctx⋆ n} (γ : Sub Δ Γ) → stripctx Γ ⊢ stripsub γ ∈s stripctx Δ
  typingsub (id {Γ = Γ}) = ⊢id (typingctx Γ)
  typingsub (γ ∘⋆ γ')    = ⊢∘ (typingsub γ) (typingsub γ')
  typingsub (<> {Γ = Γ}) = ⊢<> (typingctx Γ)
  typingsub (p {A = A})  = ⊢p (typingty A)
  typingsub < γ , a >    = ⊢<,> (typingsub γ) (typingty _) (typingtm a)

mutual

  joinctx : ∀ {n} → Σ (Ctx n) (_⊢) → Ctx⋆ n
  joinctx (⋄ Σ., _)                 = ⋄
  joinctx ((Γ ∙ A) Σ., c-ext Γ⊢ ⊢A) = (joinctx (Γ Σ., Γ⊢)) , {!!}

  jointy : ∀ {n} {Γ : Ctx n} (s : Σ (RTm n) (Γ ⊢_)) → Ty (joinctx (Γ Σ., lemma-1 (Σ.proj₂ s))) -- that's one ugly type
  jointy s = {!!}

