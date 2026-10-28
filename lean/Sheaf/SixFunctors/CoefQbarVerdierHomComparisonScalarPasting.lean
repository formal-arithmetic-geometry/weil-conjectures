/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents

/-! # Pasting the finite Hom scalar square into the common-stage component square

Source: blueprint thm-coef-qbar-verdier, retained proof step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier.HomComparison
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem scalar_evaluation_transport
    {C : Type u} [Category.{v} C] {D' : Type u} [Category.{v} D']
    (T : C × C ⥤ C) (U : D' × D' ⥤ D') (F : C ⥤ D')
    (d : Cᵒᵖ ⥤ C) (e : D'ᵒᵖ ⥤ D') (w : C) (z : D')
    (ev : ∀ K, T.obj (K, d.obj (op K)) ⟶ w)
    (ew : ∀ K, U.obj (K, e.obj (op K)) ⟶ z)
    (t : T ⋙ F ≅ F.prod F ⋙ U)
    (β : ∀ K, F.obj (d.obj (op K)) ≅ e.obj (op (F.obj K)))
    (ω : F.obj w ≅ z)
    (he : ∀ K,
      U.map (Prod.mkHom (𝟙 (F.obj K)) ((β K).hom)) ≫ ew (F.obj K) =
        t.inv.app (K, d.obj (op K)) ≫ F.map (ev K) ≫ ω.hom)
    (K P : C) (h : P ⟶ d.obj (op K)) :
    U.map (Prod.mkHom (𝟙 (F.obj K)) (F.map h ≫ (β K).hom)) ≫ ew (F.obj K) =
      t.inv.app (K, P) ≫ F.map (T.map (Prod.mkHom (𝟙 K) h) ≫ ev K) ≫ ω.hom := by
  calc
    _ = U.map (Prod.mkHom (𝟙 (F.obj K)) (F.map h)) ≫
        (U.map (Prod.mkHom (𝟙 (F.obj K)) ((β K).hom)) ≫ ew (F.obj K)) := by
      rw [← U.map_comp_assoc]
      congr 2
      simp
    _ = _ := by
      rw [he]
      have ht := t.inv.naturality (Prod.mkHom (𝟙 K) h)
      simp only [Functor.comp_map, Functor.prod_map] at ht
      rw [F.map_id] at ht
      rw [reassoc_of% ht]
      simp only [Functor.map_comp, Category.assoc]

/-- Expanded scalar-pasting square for the chosen local comparison components.
Source: coefficient-transport paragraph of blueprint thm-coef-qbar-verdier,
retained proof step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded).

This is the component-level calculation obtained after expanding `component` to
`localComparison`; it is the finite-stage square that the outer theorem packages.
-/
theorem component_extension_expanded
    (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω K.stage) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h)
      (B.finite.omega K.stage) (B.finite.omega L)
      (B.finite.datum K.stage) (B.finite.datum L)
      (B.finite.hom K.stage) (B.finite.hom L)) :
    B.duality.dual.map ((stageSystem l Ω X).isoToStage K h).hom.op ≫
        (localComparison l Ω X D hl B K.stage).hom.app (op K.obj) =
      (component l Ω X D hl B ((inclusion L).obj (K.toStage h))).hom ≫
        (homDual l Ω X B.omega (fun M ↦
          allPairs l Ω X D hl B.finite M B.omega)).map
          ((stageSystem l Ω X).isoToStage K h).hom.op := by
  sorry

theorem component_extension_of_scalar_compatibility
    (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω K.stage) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h)
      (B.finite.omega K.stage) (B.finite.omega L)
      (B.finite.datum K.stage) (B.finite.datum L)
      (B.finite.hom K.stage) (B.finite.hom L)) :
    B.duality.dual.map ((stageSystem l Ω X).isoToStage K h).hom.op ≫
        (component l Ω X D hl B K).hom =
      (component l Ω X D hl B ((inclusion L).obj (K.toStage h))).hom ≫
        (homDual l Ω X B.omega (fun M ↦
          allPairs l Ω X D hl B.finite M B.omega)).map
          ((stageSystem l Ω X).isoToStage K h).hom.op := by
  simpa only [component, GeneralAlgebraicallyClosedCoefficients.inclusion,
    StageSystem.ι_obj, Functor.comp_map, Functor.op_map, Iso.app_hom,
    Functor.comp_obj, Functor.op_obj, Quiver.Hom.unop_op] using
    component_extension_expanded D l hl Ω X B K L h hs

end WeilConjectures.CoefQbarVerdier.HomComparison
