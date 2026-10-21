/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction

/-! # Scalar extension and restriction to a pro-etale slice

Source: Stacks Project, Modules on Sites, Tag 03EL; Cohomology on Sites,
Tags 06YS, 0G7E and 06YY
(blueprint: lem-per-proetale-scalar-slice-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Literal restriction of module sheaves to a pro-etale site object.
Source: Stacks 00XZ and 03EL
(blueprint: lem-per-proetale-scalar-slice-comparison). -/
abbrev proEtaleSliceModules {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcModules X R ⥤ pbcModules U.left
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) :=
  letI : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  SheafOfModules.pushforward (F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop)
    (J := ProEt.topology U.left) (K := ProEt.topology X) (𝟙 _)

private theorem exact_moduleRestriction
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.IsCocontinuous J K] [F.IsLeftAdjoint]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) [IsIso φ] :
    (SheafOfModules.pushforward.{u} φ).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) :=
    preservesFiniteLimits_of_reflects_of_preserves _ T
  have : (SheafOfModules.pushforward.{u} φ).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso φ
  refine ⟨?_, inferInstance, inferInstance⟩
  constructor
  intro M N f g
  apply SheafOfModules.hom_ext
  ext V m
  rfl

/-- Exactness of literal restriction, including nonnoetherian U.
Source: Stacks 00XZ, 03EL and 03CZ
(blueprint: lem-per-proetale-scalar-slice-comparison).
Proof: the forgetful functor from module sheaves to module presheaves reflects
finite limits, and presheaf restriction preserves them. Composition with U is
cocontinuous and is left adjoint to base change, so module restriction is itself
a left adjoint and preserves colimits. Additivity follows on sections. No
coefficient flatness, boundedness or noetherian hypothesis on U is used. -/
theorem proEtaleSliceModules_exact {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleSliceModules U R).Additive ∧ PreservesFiniteLimits (proEtaleSliceModules U R) ∧
      PreservesFiniteColimits (proEtaleSliceModules U R) := by
  let G := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  let : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let : G.IsCocontinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap U.prop
  let : G.IsLeftAdjoint :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial).isLeftAdjoint
  exact exact_moduleRestriction (F := G) (𝟙 _)

instance proEtaleSliceModules_additive {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleSliceModules U R).Additive := (proEtaleSliceModules_exact U R).1

instance proEtaleSliceModules_limits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleSliceModules U R) := (proEtaleSliceModules_exact U R).2.1

instance proEtaleSliceModules_colimits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleSliceModules U R) := (proEtaleSliceModules_exact U R).2.2

/-- The ordinary and unbounded derived scalar comparisons, with tensor and counit
normalizations. Source: Stacks Tags 03EL and 06YY
(blueprint: lem-per-proetale-scalar-slice-comparison). -/
structure ProEtaleScalarSliceComparison {Y : Scheme.{u}} (U : Y.ProEt)
    (R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (c : R ⟶ S) where
  ordinary : pbcExtend c ⋙ proEtaleSliceModules U S ≅
    proEtaleSliceModules U R ⋙
      pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).map c)
  sections : ∀ (M : pbcModules Y R)
      (V : U.left.ProEtᵒᵖ) (s : S.obj.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)))
      (m : M.val.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))),
    (ordinary.hom.app M).val.app V (pbcTensorSection c M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) s m) =
      pbcTensorSection ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c) ((proEtaleSliceModules U _).obj M) V s m
  complex : (pbcExtend c).mapHomologicalComplex (.up ℤ) ⋙
      (proEtaleSliceModules U S).mapHomologicalComplex (.up ℤ) ≅
    (proEtaleSliceModules U R).mapHomologicalComplex (.up ℤ) ⋙
      (pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  scalar_derived : pbcDerivedExtend c ⋙ (proEtaleSliceModules U S).mapDerivedCategory ≅
    (proEtaleSliceModules U R).mapDerivedCategory ⋙
      pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)
  normalization : ∀ P : CochainComplex (pbcModules Y R) ℤ,
    ((proEtaleSliceModules U S).mapDerivedCategory).map (pbcComplexCounit c P) ≫
        (proEtaleSliceModules U S).mapDerivedCategoryFactors.hom.app
          (((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complex.hom.app P) =
      scalar_derived.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)).map
          ((proEtaleSliceModules U _).mapDerivedCategoryFactors.hom.app P) ≫
        pbcComplexCounit ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)
          (((proEtaleSliceModules U _).mapHomologicalComplex (.up ℤ)).obj P)

/-- Restriction to a site object commutes with scalar extension and its unbounded
left derived functor, preserving the specified tensor sections and counit.

Source: Stacks Project, Modules on Sites, Tag 03EL; Cohomology on Sites,
Tags 06YS, 0G7E and 06YY
(blueprint: lem-per-proetale-scalar-slice-comparison).

Proof: identify the pro-etale site of U with the slice at U. The sectionwise tensor
presheaf restricts to the tensor presheaf of the restricted modules. Restriction
commutes with sheafification, with the comparison fixed by the sheafification units.
This gives the ordinary natural isomorphism and the displayed formula on pure tensors.
Apply it degreewise to get the complex comparison and its components. Choose a
flat-term K-flat resolution of a complex over R. Exact restriction preserves its
quasi-isomorphism and preserves flat-term K-flat complexes. Thus both derived
composites are computed by the ordinary tensor comparison on this resolution.
Naturality on resolutions and the universal property of the two left derived
functors extend this comparison uniquely to the derived categories. Its defining
commutation with the universal counits is exactly the displayed normalization.
The identity, zero ring and empty scheme cases use the same universal properties;
no flatness of c, noetherianity of U or boundedness of complexes is required. -/
theorem proEtaleScalarExtensionSliceComparison {Y : Scheme.{u}} (U : Y.ProEt)
    (R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (c : R ⟶ S) :
    Nonempty (ProEtaleScalarSliceComparison U R S c) := by sorry

end AlgebraicGeometry.Scheme
