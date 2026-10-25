/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClass

/-!

# The trace class as an exceptional adjoint along the fixed locus

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)` with fixed locus
`ι : Fix(c) ⟶ C`, `d = ι ≫ c₁ : Fix(c) ⟶ X`, and put `P = K ⊠ D_X K`. The *supported class*
of `u` is the exceptional adjoint `ũ : Rc_! ℚ̄_ℓ,C ⟶ P` of `ℚ̄_ℓ,C --mate--> 𝓗_c(K) ≅ Rc^! P`
(`ProEtale.CondensedRing.Correspondence.supportedClass`, blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 1). The trace class is the exceptional adjoint
along `d` of
```
h : Rd_! Lι^* ℚ̄_ℓ,C ≅ LΔ^* Rc_! ℚ̄_ℓ,C --LΔ^* ũ--> LΔ^* P ≅ K ⊗ D_X K --ev--> ω_X,
```
the inverse of compact-support base change in the fixed square, `LΔ^*` of the supported class
and the evaluation (`ProEtale.CondensedRing.Correspondence.traceClass_eq_homEquiv`, blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 2).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- Composing an adjoint with a conjugate transformation is the adjoint of the composite with
the original transformation: for `α : L₂ ⟶ L₁` and `f : L₁ M ⟶ N`,
`adj₁.homEquiv f ≫ (conjugateEquiv adj₁ adj₂ α).app N = adj₂.homEquiv (α.app M ≫ f)`. -/
lemma Adjunction.homEquiv_comp_conjugateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {M : C} {N : D} (f : L₁.obj M ⟶ N) :
    adj₁.homEquiv M N f ≫ (conjugateEquiv adj₁ adj₂ α).app N =
      adj₂.homEquiv M N (α.app M ≫ f) := by
  rw [conjugateEquiv_apply_app, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← adj₂.unit_naturality_assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  rw [α.naturality_assoc, Functor.map_comp, Category.assoc, adj₁.counit_naturality,
    adj₁.left_triangle_components_assoc]

/-- `Adjunction.homEquiv_comp_conjugateEquiv_app` for composite adjunctions and the conjugate of
the inverse of an isomorphism of composite left adjoints. -/
lemma Adjunction.homEquiv_homEquiv_comp_conjugateIsoEquiv_app {C₁ C₂ C₃ C₄ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] {A : C₁ ⥤ C₂} {A' : C₂ ⥤ C₁}
    {B : C₂ ⥤ C₃} {B' : C₃ ⥤ C₂} {E : C₁ ⥤ C₄} {E' : C₄ ⥤ C₁} {G : C₄ ⥤ C₃} {G' : C₃ ⥤ C₄}
    (a : A ⊣ A') (b : B ⊣ B') (e : E ⊣ E') (g : G ⊣ G') (σ : A ⋙ B ≅ E ⋙ G) {M : C₁}
    {N : C₃} (f : B.obj (A.obj M) ⟶ N) :
    a.homEquiv M (B'.obj N) (b.homEquiv (A.obj M) N f) ≫
        ((conjugateIsoEquiv (a.comp b) (e.comp g) σ.symm).app N).hom =
      e.homEquiv M (G'.obj N) (g.homEquiv (E.obj M) N (σ.inv.app M ≫ f)) := by
  have h := homEquiv_comp_conjugateEquiv_app (a.comp b) (e.comp g) σ.inv f
  simp only [comp_homEquiv] at h
  exact h

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

/-- The *supported class* `ũ : Rc_! ℚ̄_ℓ,C ⟶ K ⊠ D_X K` of the coefficient map `u` (blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 1): the exceptional adjoint of the mate of `u`
read through the external duality isomorphism `𝓗_c(K) ≅ Rc^! (K ⊠ D_X K)`. -/
noncomputable def supportedClass :
    (boundedConstructibleLowerShriek _ ℓ c.support).obj (𝟙_ _) ⟶
      externalProduct ℓ K (verdierDual ℓ (toPoint X) K) :=
  ((boundedConstructibleUpperShriekAdjunction _ ℓ c.support).homEquiv _ _).symm
    (c.mate ≫ c.verdierDualityIso.hom)

/-- The mate of `u`, read through the external duality isomorphism, is the exceptional adjoint
of the supported class (blueprint `lem-trf-trace-class-diagonal-pairing`, Step 1). -/
lemma mate_comp_verdierDualityIso_hom :
    c.mate ≫ c.verdierDualityIso.hom =
      (boundedConstructibleUpperShriekAdjunction _ ℓ c.support).homEquiv _ _
        c.supportedClass := by
  rw [supportedClass, Equiv.apply_symm_apply]

/-- **The supported class is the Künneth–Verdier inverse of the class of `u`** (blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 1): `ũ = κ_{K,K}⁻¹ ∘ [u]`, where `[u]` is the class of
`u` read through `Lc₂^* = Lc^* Lp₂^*` and `Rc₁^! = Rc^! Rp₁^!`. -/
lemma supportedClass_eq :
    c.supportedClass =
      (Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
          (boundedConstructibleExceptionalProjection _ ℓ c.support) _ _).symm
          ((eqToIso (by rw [support_snd]) ≪≫
              (boundedConstructibleUpperStarComp _ ℓ c.support prod.snd).app K).inv ≫ c.u ≫
            (eqToIso (by rw [support_fst]) ≪≫
              (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c.support prod.fst).app K).hom) ≫
        inv (kunnethVerdierMap ℓ K K) := by
  unfold supportedClass mate verdierDualityIso traceClassSourceIso exceptionalHomIso
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
  exact Verdier.homEquiv_symm_curry'_comp_exceptionalHomMap _ _ _ _ c.u _ _ _

variable {c} (F : c.FixedLocus)

/-- The morphism `h : Rd_! Lι^* ℚ̄_ℓ,C ⟶ ω_X` whose exceptional adjoint along `d` is the trace
class (blueprint `lem-trf-trace-class-diagonal-pairing`, Step 2): the inverse of compact-support
base change `LΔ^* Rc_! ≅ Rd_! Lι^*` in the fixed square, `LΔ^*` of the supported class, the
identification `LΔ^* (K ⊠ D_X K) ≅ K ⊗ D_X K` and the evaluation. -/
noncomputable def diagonalSpecialization :
    (boundedConstructibleLowerShriek _ ℓ F.d).obj
        ((boundedConstructibleUpperStar _ ℓ F.ι).obj (𝟙_ _)) ⟶
      dualizingComplex' ℓ X :=
  F.lowerShriekBaseChangeIso.inv.app (𝟙_ _) ≫
    (boundedConstructibleUpperStar _ ℓ (diag X)).map c.supportedClass ≫
    (diagUpperStarExternalProductIso ℓ K _).hom ≫ (ihom.ev K).app (dualizingComplex' ℓ X)

set_option maxHeartbeats 800000 in
-- `erw` matches the composition up to the instance arguments of the bounded constructible
-- categories, which takes more than the default budget.
/-- **The trace class is an exceptional adjoint along the fixed locus** (blueprint
`lem-trf-trace-class-diagonal-pairing`, Step 2): `Tr_c(u)` is the exceptional adjoint along
`d : Fix(c) ⟶ X` of `diagonalSpecialization`, read through `ℚ̄_ℓ,Fix(c) ≅ Lι^* ℚ̄_ℓ,C` and the
composition isomorphism `Rd^! ω_X ≅ ω_Fix(c)`. -/
theorem traceClass_eq_homEquiv :
    c.traceClass F =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
        (boundedConstructibleUpperShriekAdjunction _ ℓ F.d).homEquiv _ _
          (diagonalSpecialization F) ≫
        (dualizingComplexComp ℓ F.d).hom := by
  rw [traceClass]
  refine congrArg (_ ≫ ·) ?_
  rw [Equiv.symm_apply_eq, traceMap, ← Category.assoc, ← Category.assoc,
    mate_comp_verdierDualityIso_hom, ← Adjunction.homEquiv_naturality_right]
  conv_rhs => rw [Adjunction.homEquiv_naturality_right]
  unfold evaluationKernel
  have e1 : c.supportedClass ≫
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X)).homEquiv _ _
        ((diagUpperStarExternalProductIso ℓ K _).hom ≫ (ihom.ev K).app (dualizingComplex' ℓ X)) =
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X)).homEquiv _ _
        ((boundedConstructibleUpperStar _ ℓ (diag X)).map c.supportedClass ≫
          (diagUpperStarExternalProductIso ℓ K _).hom ≫ (ihom.ev K).app (dualizingComplex' ℓ X)) :=
    (Adjunction.homEquiv_naturality_left _ _ _).symm
  erw [e1]
  unfold FixedLocus.upperShriekLowerStarIso
  erw [reassoc_of% (Adjunction.homEquiv_homEquiv_comp_conjugateIsoEquiv_app
      (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X))
      (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ F.ι)
      (boundedConstructibleUpperShriekAdjunction _ ℓ F.d) F.lowerShriekBaseChangeIso
      ((boundedConstructibleUpperStar _ ℓ (diag X)).map c.supportedClass ≫
        (diagUpperStarExternalProductIso ℓ K _).hom ≫
        (ihom.ev K).app (dualizingComplex' ℓ X)))]
  rfl

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
