/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BorelMoore
public import WeilConjectures.TraceFormula.ProperPushforward
public import WeilConjectures.TraceFormula.TraceClass

/-!

# Kernel maps of a proper pushforward diagram

Let `(f, g) : (C, c) ⟶ (D, b)` be a proper pushforward diagram of an endocorrespondence `c` of
`(X, K)`, with `K' = Rf_* K`, the induced proper map of fixed loci `h : Fix(c) ⟶ Fix(b)` and
`q = f × f : X ⨯ X ⟶ Y ⨯ Y`. This file defines the remaining maps of blueprint
`def-trf-kernel-pushforward-maps` (the trace `τ_f`, the multiplication `μ_f`, the composition
isomorphism `Ξ` and the exchange `E` are in `WeilConjectures.TraceFormula.ProperPushforward`):

* the *dual pushforward* `χ_f : Rf_* D_X K ⟶ D_Y K'` (`lowerStarVerdierDualMap`);
* the *Künneth map* `Π_f : K' ⊠ Rf_* D_X K ⟶ Rq_* (K ⊠ D_X K)` (`prodLowerStarExternalProduct`),
  the adjoint of the counits; for proper `f` it is the inverse of the `!`-Künneth isomorphism
  `Ku_!` of `def-sf-kv-maps` (i) under `Rq_* ≅ Rq_!`, and it is invertible by the relative
  product theorem (blueprint `thm-sf-kunneth-relative`, sorried input
  `isIso_prodLowerStarExternalProduct`);
* the *kernel pushforward* `ρ_f = (1 ⊠ χ_f) ∘ Π_f⁻¹ : Rq_* P_X ⟶ P_Y` (`kernelPushforward`);
* the *kernel class* `[u]_P : Rc_! ℚ̄_ℓ,C ⟶ P_X` (`Correspondence.kernelClass`), the exceptional
  adjoint of the mate of `u` followed by the external duality isomorphism;
* the *support isomorphism* `ζ_c : Rι_* ω_Fix(c) ≅ Rc^! RΔ_* ω_X`
  (`Correspondence.FixedLocus.supportIso`);

and the *proper pushforward of the trace class* `h_* Tr_c(u)`
(`Correspondence.ProperPushforwardDiagram.traceClassPushforward`, blueprint
`sk-d-proper-pushforward`, `lem-trf-fixed-map-proper`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Maps along proper morphisms -/

section ProperMaps

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *dual pushforward* `χ_f : Rf_* D_X K ⟶ D_Y (Rf_* K)` along a proper morphism (blueprint
`def-trf-kernel-pushforward-maps`, item 4): the tensor–hom transpose of
```
Rf_* K ⊗ Rf_* D_X K --μ_f--> Rf_* (K ⊗ D_X K) --Rf_* ev--> Rf_* ω_X --τ_f--> ω_Y.
```
-/
noncomputable def lowerStarVerdierDualMap (f : X ⟶ Y) [IsProper f.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar _ ℓ f).obj (verdierDual ℓ (toPoint X) K) ⟶
      verdierDual ℓ (toPoint Y) ((boundedConstructibleLowerStar _ ℓ f).obj K) :=
  curry (lowerStarTensorMap ℓ f K _ ≫
    (boundedConstructibleLowerStar _ ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)) ≫
    lowerStarDualizingComplexTrace ℓ f)

variable {X₁ X₂ Y₁ Y₂ : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]

/-- The counit of `Lf^* ⊣ Rf_*` transported to a product: `Lq^* Lp_i^* Rf_i* B ⟶ Lp_i^* B` for
`q ≫ p_i = p_i ≫ f_i`. -/
noncomputable def prodUpperStarCounit {P P' : Over (Spec (.of k))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
    {q : P ⟶ P'} {p : P ⟶ X₁} {p' : P' ⟶ Y₁} {f₁ : X₁ ⟶ Y₁} (w : q ≫ p' = p ≫ f₁)
    (B : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ q).obj ((boundedConstructibleUpperStar _ ℓ p').obj
        ((boundedConstructibleLowerStar _ ℓ f₁).obj B)) ⟶
      (boundedConstructibleUpperStar _ ℓ p).obj B :=
  (boundedConstructibleUpperStarComp _ ℓ q p').inv.app _ ≫ eqToHom (by rw [w]) ≫
    (boundedConstructibleUpperStarComp _ ℓ p f₁).hom.app _ ≫
    (boundedConstructibleUpperStar _ ℓ p).map
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ f₁).counit.app B)

/-- The *Künneth map* `Π : Rf₁* B₁ ⊠ Rf₂* B₂ ⟶ R(f₁ × f₂)_* (B₁ ⊠ B₂)` (blueprint
`def-trf-kernel-pushforward-maps`, item 5): the adjoint for `Lq^* ⊣ Rq_*`, `q = f₁ × f₂`, of
```
Lq^* (Lp₁^* Rf₁* B₁ ⊗ Lp₂^* Rf₂* B₂) ≅ Lq^* Lp₁^* Rf₁* B₁ ⊗ Lq^* Lp₂^* Rf₂* B₂
  ⟶ Lp₁^* B₁ ⊗ Lp₂^* B₂,
```
the monoidal structure of `Lq^*` followed by the counits. For proper `f_i` it is the inverse of
the `!`-Künneth isomorphism `Ku_!` of `def-sf-kv-maps` (i) under `Rq_* ≅ Rq_!`. -/
noncomputable def prodLowerStarExternalProduct (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ ((boundedConstructibleLowerStar _ ℓ f₁).obj B₁)
        ((boundedConstructibleLowerStar _ ℓ f₂).obj B₂) ⟶
      (boundedConstructibleLowerStar _ ℓ (prod.map f₁ f₂)).obj (externalProduct ℓ B₁ B₂) :=
  (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (prod.map f₁ f₂)).homEquiv _ _
    ((Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (prod.map f₁ f₂)) _ _).inv ≫
      (prodUpperStarCounit ℓ (prod.map_fst f₁ f₂) B₁ ⊗ₘ
        prodUpperStarCounit ℓ (prod.map_snd f₁ f₂) B₂))

/-- **The relative product theorem for proper morphisms** (blueprint `thm-sf-kunneth-relative`,
compatibility with `Rf_! ≅ Rf_*` for proper `f`, as used in `def-sf-kv-maps` (i)): for proper
`f₁`, `f₂` the Künneth map `Rf₁* B₁ ⊠ Rf₂* B₂ ⟶ R(f₁ × f₂)_* (B₁ ⊠ B₂)` is an isomorphism. -/
instance isIso_prodLowerStarExternalProduct (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [IsProper f₁.left]
    [IsProper f₂.left] (B₁ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B₂ : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (prodLowerStarExternalProduct ℓ f₁ f₂ B₁ B₂) :=
  sorry

/-- The *kernel pushforward* `ρ_f = (1 ⊠ χ_f) ∘ Π_f⁻¹ : Rq_* (K ⊠ D_X K) ⟶ K' ⊠ D_Y K'` along a
proper morphism `f`, `q = f × f`, `K' = Rf_* K` (blueprint `def-trf-kernel-pushforward-maps`,
item 5). -/
noncomputable def kernelPushforward (f : X ⟶ Y) [IsProper f.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar _ ℓ (prod.map f f)).obj
        (externalProduct ℓ K (verdierDual ℓ (toPoint X) K)) ⟶
      externalProduct ℓ ((boundedConstructibleLowerStar _ ℓ f).obj K)
        (verdierDual ℓ (toPoint Y) ((boundedConstructibleLowerStar _ ℓ f).obj K)) :=
  inv (prodLowerStarExternalProduct ℓ f f K (verdierDual ℓ (toPoint X) K)) ≫
    (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
      (lowerStarVerdierDualMap ℓ f K))

end ProperMaps

/-! ### Kernel classes and support isomorphisms -/

variable {ℓ} {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

/-- The *kernel class* `[u]_P : Rc_! ℚ̄_ℓ,C ⟶ K ⊠ D_X K` of an endocorrespondence (blueprint
`def-trf-kernel-pushforward-maps`, item 7): the exceptional adjoint of
`ℚ̄_ℓ,C --ũ--> 𝓗_c(K) ≅ Rc^! (K ⊠ D_X K)`. -/
noncomputable def kernelClass :
    (boundedConstructibleLowerShriek _ ℓ c.support).obj (𝟙_ _) ⟶
      externalProduct ℓ K (verdierDual ℓ (toPoint X) K) :=
  ((boundedConstructibleUpperShriekAdjunction _ ℓ c.support).homEquiv _ _).symm
    (c.mate ≫ c.verdierDualityIso.hom)

namespace FixedLocus

variable {c} (F : c.FixedLocus)

/-- The *support isomorphism* `ζ_c : Rι_* ω_Fix(c) ≅ Rc^! RΔ_* ω_X` (blueprint
`def-trf-kernel-pushforward-maps`, item 8): the inverse of the right-adjoint form of base change
in the fixed square followed by `Rd^! ω_X ≅ ω_Fix(c)`. -/
noncomputable def supportIso :
    (boundedConstructibleLowerStar _ ℓ F.ι).obj (dualizingComplex' ℓ F.F) ≅
      (boundedConstructibleUpperShriek _ ℓ c.support).obj
        ((boundedConstructibleLowerStar _ ℓ (diag X)).obj (dualizingComplex' ℓ X)) :=
  (F.upperShriekLowerStarIso.app (dualizingComplex' ℓ X) ≪≫
    (boundedConstructibleLowerStar _ ℓ F.ι).mapIso (dualizingComplexComp ℓ F.d)).symm

end FixedLocus

/-- By construction, the trace morphism is `ζ_c⁻¹ ∘ Rc^! δ_K ∘ ξ` (blueprint
`def-trf-kernel-pushforward-maps`, last paragraph). -/
lemma traceMap_eq (F : c.FixedLocus) :
    c.traceMap F = c.verdierDualityIso.hom ≫
      (boundedConstructibleUpperShriek _ ℓ c.support).map (evaluationKernel ℓ K) ≫
      F.supportIso.inv :=
  rfl

namespace ProperPushforwardDiagram

variable {c} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y) (Fc : c.FixedLocus)
  (Fb : P.pushforward.FixedLocus)

/-- The *proper pushforward of the trace class* `h_* Tr_c(u) : ℚ̄_ℓ,Fix(b) ⟶ ω_Fix(b)` along the
induced proper map of fixed loci `h : Fix(c) ⟶ Fix(b)` (blueprint `sk-d-proper-pushforward`,
`lem-trf-fixed-map-proper`): the Borel–Moore pushforward of the trace class. -/
noncomputable def traceClassPushforward : BorelMooreSection ℓ Fb.F :=
  BorelMooreSection.pushforward (P.fixMap Fc Fb) (c.traceClass Fc)

end ProperPushforwardDiagram

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
