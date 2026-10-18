/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# Canonical realization and constant-coefficient direct image

Source: Stacks Project, Tags 00YV and 03D1; Weil blueprint, order 1466
(blueprint: def-weil-proetale-inverse-image).
The normalization on the scalar-unit sections fixes the comparison, including its direction.

## Main definitions

- `sfIntrinsicDerivedEquivalence`: the specified realization on derived categories.
- `sfIntrinsicDirectImageComparison` and `sfIntrinsicDerivedDirectImageComparison`:
  the comparisons uniquely normalized on sections and K-injective representatives.
- `sfIntrinsicConstantModuleAdjunction`: the transported inverse-image adjunction.
- `AlgebraicGeometry.ProEtale.sfFixedDerivedPullback`: exact termwise inverse image.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The derived equivalence induced by the recorded canonical coefficient realization.
Source: Stacks Tag 00YV (blueprint: def-weil-proetale-inverse-image). -/
noncomputable def sfIntrinsicDerivedEquivalence (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ≌
      proEtaleDerivedCategory T A :=
  (sfIntrinsicModuleEquivalence T A).mapDerivedCategory

/-- The scalar-unit section of the canonical associated module sheaf.
Source: Stacks Tag 00YV (blueprint: def-weil-proetale-inverse-image). -/
noncomputable def sfIntrinsicRealizationUnit (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : T.ProEtᵒᵖ) (m : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence T A).functor.obj M).val.obj W :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)).obj M.obj)).app
        W m

/-- The unique section-normalized comparison of direct images in the two coefficient
presentations. Source: Stacks Tags 00YV and 03D1
(blueprint: def-weil-proetale-inverse-image).
Proof: restriction of scalars along the constant-scalar unit identifies both underlying
module sheaves with V ↦ M(X ×_Y V). The two scalar-unit maps agree on constants, and local
surjectivity of that unit extends the identity uniquely to locally constant scalars.
Module sheafification gives the displayed linear isomorphism; the scalar-unit sections
locally generate, so the displayed equation determines it uniquely. -/
theorem sfIntrinsicDirectImageComparison_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ∃! e : (sfIntrinsicModuleEquivalence X A).functor ⋙
          proEtaleConstantModuleDirectImage f A ≅
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
          (sfIntrinsicModuleEquivalence Y A).functor,
      ∀ (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
        (W : Y.ProEtᵒᵖ) (m : M.obj.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app M).val.app W
            (sfIntrinsicRealizationUnit X A M ((proEtaleBaseChange f).op.obj W) m) =
          sfIntrinsicRealizationUnit Y A
            ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj M) W m := by
  sorry

/-- The actual comparison, selected by its unique scalar-section normalization.
Source: Stacks Tag 03D1 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable def sfIntrinsicDirectImageComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :=
  (sfIntrinsicDirectImageComparison_existsUnique f A).exists.choose

/-- The uniquely normalized derived direct-image comparison.
Source: Stacks Tags 00YV and 07A5 (blueprint: def-weil-proetale-inverse-image).
Proof: the realization equivalence preserves K-injective complexes. Resolve a fixed-scalar
complex by such a complex J. Both derived images are then their ordinary images, and the
underived comparison above gives the stated equality. Naturality on complexes and roofs
makes this a natural isomorphism. Every object has a K-injective resolution, so its values
on these representatives determine the natural isomorphism uniquely. -/
theorem sfIntrinsicDerivedDirectImageComparison_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ∃! e : (sfIntrinsicDerivedEquivalence X A).functor ⋙
          proEtaleConstantDerivedDirectImage f A ≅
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor,
      ∀ (J : CochainComplex
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
        [J.IsKInjective],
        e.hom.app (DerivedCategory.Q.obj J) ≫
            (sfIntrinsicDerivedEquivalence Y A).functor.map
              ((ProEtale.lowerStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctorObjQIso J).hom ≫
            (sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategoryFactors.hom.app
              (((ProEtale.lowerStar
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapHomologicalComplex (.up ℤ)).obj J) =
          (proEtaleConstantDerivedDirectImage f A).map
              ((sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategoryFactors.hom.app J) ≫
            ((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorObjQIso
              (((sfIntrinsicModuleEquivalence X A).functor.mapHomologicalComplex
                (.up ℤ)).obj J)).hom ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex
                (sfIntrinsicDirectImageComparison f A).hom (.up ℤ)).app J) := by
  sorry

/-- The actual derived comparison determined on K-injective representatives.
Source: Stacks Tag 07A5 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable def sfIntrinsicDerivedDirectImageComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :=
  (sfIntrinsicDerivedDirectImageComparison_existsUnique f A).exists.choose

/-- The actual inverse-image/direct-image adjunction, conjugated through the canonical
section-normalized comparison. This fixes the units and counits of inverse image.
Source: Stacks Tags 00YV and 03D3 (blueprint: def-weil-proetale-inverse-image). -/
noncomputable def sfIntrinsicConstantModuleAdjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicPullback A f ⊣ proEtaleConstantModuleDirectImage f A :=
  (((sfIntrinsicModuleEquivalence Y A).symm.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)).comp
      (sfIntrinsicModuleEquivalence X A).toAdjunction).ofNatIsoRight
        (Functor.isoWhiskerLeft _ (sfIntrinsicDirectImageComparison f A).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso _ ≪≫
          Functor.leftUnitor _)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Exact termwise inverse image, in fixed-scalar coordinates.
Source: Stacks Tag 04JC (blueprint: def-weil-proetale-inverse-image). -/
noncomputable abbrev sfFixedDerivedPullback (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory

end AlgebraicGeometry.ProEtale
