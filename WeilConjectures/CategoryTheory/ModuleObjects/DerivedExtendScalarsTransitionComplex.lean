/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTransition

/-!
# The transition between reductions on K-flat complexes

Let `φ' : R ⟶ S'`, `ψ : S' ⟶ S` and `φ : R ⟶ S` be morphisms of commutative algebra objects with
`φ' ≫ ψ = φ`. On a K-flat complex `P`, the transition `t : S' ⊗ᴸ_R P ⟶ S ⊗ᴸ_R P` of
`Mod.derivedReductionTransition` is computed by the levelwise map `S' ⊗_R P ⟶ S ⊗_R P`
(`Mod.derivedReductionTransition_app_Q_obj_comp`). As a consequence, if
`0 ⟶ R --k'--> R --φ'--> S' ⟶ 0` and `0 ⟶ R --k--> R --φ--> S ⟶ 0` are short exact with
`k' = m * k`, the connecting morphisms of the natural reduction triangles satisfy `t ≫ δ = δ' ≫ m`
(`Mod.derivedReductionTransition_app_comp_derivedExtendScalarsTriangleδ`): on a complex of flat
modules, `(m, 1, S' ⊗ P ⟶ S ⊗ P)` is a map of short exact sequences from
`P --k'--> P ⟶ S' ⊗ P` to `P --k--> P ⟶ S ⊗ P`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S' S : C} [MonObj R] [MonObj S'] [MonObj S] [IsCommMonObj R] [IsCommMonObj S']
  [IsCommMonObj S] (φ' : R ⟶ S') [IsMonHom φ'] (ψ : S' ⟶ S) [IsMonHom ψ] (φ : R ⟶ S)
  [IsMonHom φ] (h : φ' ≫ ψ = φ)

/-! ### The levelwise transition -/

/-- The levelwise transition `S' ⊗_R M ⟶ S ⊗_R M`, as a map of `S'`-modules: the unit of
extension of scalars along `ψ`, followed by the transitivity isomorphism. -/
noncomputable def extendScalarsTransition : extendScalars φ' ⟶ extendScalars φ ⋙ comap ψ :=
  Functor.whiskerLeft (extendScalars φ') (extendRestrictAdjunction ψ).unit ≫
    Functor.whiskerRight ((extendScalarsComp φ' ψ).symm ≪≫ extendScalarsIsoOfEq h).hom (comap ψ)

/-- The levelwise transition `S' ⊗_R M ⟶ S ⊗_R M`, as a map of `R`-modules. -/
noncomputable def extendComapTransition :
    extendScalars φ' ⋙ comap φ' ⟶ extendScalars φ ⋙ comap φ :=
  Functor.whiskerRight (extendScalarsTransition φ' ψ φ h) (comap φ') ≫
    Functor.whiskerLeft (extendScalars φ) ((comapComp φ' ψ).symm ≪≫ comapCongr h).hom

/-- The levelwise transition is compatible with the units: `M ⟶ S' ⊗_R M ⟶ S ⊗_R M` is the unit
`M ⟶ S ⊗_R M`. -/
@[reassoc]
lemma extendRestrictAdjunction_unit_app_comp_extendComapTransition_app (M : Mod C R) :
    (extendRestrictAdjunction φ').unit.app M ≫ (extendComapTransition φ' ψ φ h).app M =
      (extendRestrictAdjunction φ).unit.app M := by
  sorry

/-- The levelwise transition `S' ⊗_R P ⟶ S ⊗_R P` on complexes. -/
noncomputable abbrev extendComapComplexTransition :
    extendComapComplexFunctor φ' ⟶ extendComapComplexFunctor φ :=
  NatTrans.mapHomologicalComplex (extendComapTransition φ' ψ φ h) (ComplexShape.up ℤ)

/-- The levelwise transition on complexes is compatible with the units. -/
@[reassoc]
lemma extendUnitComplexHom_comp_extendComapComplexTransition_app
    (P : CochainComplex (Mod C R) ℤ) :
    extendUnitComplexHom φ' P ≫ (extendComapComplexTransition φ' ψ φ h).app P =
      extendUnitComplexHom φ P := by
  ext i : 1
  simp only [HomologicalComplex.comp_f, extendUnitComplexHom_f,
    NatTrans.mapHomologicalComplex_app_f]
  rw [← extendRestrictAdjunction_unit_app, ← extendRestrictAdjunction_unit_app]
  exact extendRestrictAdjunction_unit_app_comp_extendComapTransition_app φ' ψ φ h (P.X i)

/-! ### The transition on K-flat complexes -/

/-- **The transition on a K-flat complex** `P` is the levelwise map `S' ⊗_R P ⟶ S ⊗_R P`, read
through the comparisons `Mod.derivedExtendComapComparison`. -/
lemma derivedReductionTransition_app_Q_obj_comp (P : CochainComplex (Mod C R) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (derivedReductionTransition φ' ψ φ h).app (DerivedCategory.Q.obj P) ≫
        derivedExtendComapComparison φ P =
      derivedExtendComapComparison φ' P ≫
        DerivedCategory.Q.map ((extendComapComplexTransition φ' ψ φ h).app P) := by
  sorry

variable {φ' φ} (k' k m : ℤ) (hk : k' = m * k) (w' : (k' • 𝟙 R) ≫ φ' = 0)
  (hφ' : (ShortComplex.mk _ _ w').ShortExact) (w : (k • 𝟙 R) ≫ φ = 0)
  (hφ : (ShortComplex.mk _ _ w).ShortExact)

include hk in
/-- **The transition and the connecting morphisms of the reduction triangles**: if
`0 ⟶ R --k'--> R --φ'--> S' ⟶ 0` and `0 ⟶ R --k--> R --φ--> S ⟶ 0` are short exact and
`k' = m * k`, then `t ≫ δ = δ' ≫ m`, where `δ` and `δ'` are the connecting morphisms of the
natural reduction triangles (`Mod.derivedExtendScalarsTriangleδ`). -/
lemma derivedReductionTransition_app_comp_derivedExtendScalarsTriangleδ
    (K : DerivedCategory (Mod C R)) :
    (derivedReductionTransition φ' ψ φ h).app K ≫ (derivedExtendScalarsTriangleδ k w hφ).app K =
      (derivedExtendScalarsTriangleδ k' w' hφ').app K ≫ (m • 𝟙 K)⟦(1 : ℤ)⟧' := by
  sorry

end CategoryTheory.Mod
