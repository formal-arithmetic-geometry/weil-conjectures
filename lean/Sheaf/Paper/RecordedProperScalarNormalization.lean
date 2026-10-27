/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.EtaleProEtaleCoefficientTransport
public import Sheaf.Paper.EtaleProEtaleScalarMateData
import all Sheaf.Paper.RecordedOpenScalarNormalization
import Sheaf.Paper.RecordedRestrictionNormalization
import Sheaf.Paper.FiniteRealizationMateAlgebra
import all Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.SecSmoothPurity.ProperScalarCounitSquare

/-! # Realization normalization for the proper scalar factor

Source: Stacks Tags 00YV, 03D3 and 07A6; the proper-factor argument in
`lem-sp-recorded-compact-scalar-fixed-normalization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  sfIntrinsicModuleEquivalence directImagePresentation scalarPresentation
  directImageScalarComparison
attribute [local implicit_reducible] proEtaleConstantRingMap scalarExtensionFunctor
  sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory Functor.mapHomologicalComplex

set_option maxHeartbeats 600000 in
-- This cube transposition checks several large derived-adjunction comparison types.
/-- Realization identifies the intrinsic geometric scalar mate with the fixed-module
geometric scalar mate, before any open extension is composed with it.

Source: Stacks Project, Tags 00YV, 03D3 and 07A6; proper-factor part of Step 1 of
`lem-sp-recorded-compact-scalar-fixed-normalization`.
(blueprint: lem-sp-recorded-proper-scalar-fixed-normalization).

Proof: the unit-normalized ordinary pullback comparison in directImagePresentation
has as its right-adjoint comparison the section-identity identification of the two
constant-ring direct images. Derive that comparison and compose with the specified
K-injective-normalized realization square. Scalar restriction commutes with these
ordinary comparisons because each preserves the constant scalar-unit sections.
Resolve a B-complex and its scalar restriction by K-injectives; the corresponding
derived restriction square follows by naturality of the resolution arrows and
cancellation of their quasi-isomorphisms. Transpose this square under the scalar
adjunctions. Their realization comparison is scalarPresentation: its defining
left-adjoint uniqueness equation preserves the scalar units. The intrinsic scalar
transpose is directImageScalarComparison, by the iterated-mates identity applied to
the canonical inverse restriction/pullback comparison. The same identity identifies
the fixed scalar transpose with the geometric mate of scalarPullbackProEtaleIso.
These transposes give the displayed square. This argument uses neither properness
nor a lower bound; for zero rings and empty schemes the same adjunction equations
apply. Only presentation isomorphisms are inverted. -/
theorem recordedProperScalar_fixed_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (directImageScalarComparison φ g).app
          ((sfIntrinsicDerivedEquivalence Z A).functor.obj K) ≫
        (directImageConstantPush B g).map ((scalarPresentation φ Z).hom.app K) ≫
        (directImagePresentation B g).hom.app ((liftedScalarExtension φ Z).obj K) =
      (scalarExtensionFunctor φ Y).map ((directImagePresentation A g).hom.app K) ≫
        (scalarPresentation φ Y).hom.app
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor.obj K) ≫
        (sfIntrinsicDerivedEquivalence Y B).functor.map
          ((mateEquiv
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g)
            (TwoSquare.mk _ _ _ _
              (scalarPullbackProEtaleIso (uliftRingHom φ) g).hom)).natTrans.app K) := by
  let : EssentiallySmall.{u + 1} Z.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let a := uliftRingHom φ
  let b (T : Scheme.{u}) := Adjunction.ofIsRightAdjoint
    (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
      (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance a)
  have hn (T : Scheme.{u}) (M : DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
      (pbcDerivedScalarAdjunction (FiniteCompactScalar.scalarRingMap φ T)).unit.app
          ((sfIntrinsicDerivedEquivalence T A).functor.obj M) ≫
        (pbcDerivedRestrict (FiniteCompactScalar.scalarRingMap φ T)).map
          ((FiniteCompactScalar.realizationScalarIso φ T).hom.app M) ≫
        (FiniteCompactScalar.realizationRestrictionIso φ T).hom.app
          ((liftedScalarExtension φ T).obj M) =
      (sfIntrinsicDerivedEquivalence T A).functor.map ((b T).unit.app M) := by
    let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    simpa only [FiniteCompactScalar.realizationScalarIso,
      FiniteCompactScalar.realizationRestrictionIso,
      FiniteCompactScalar.realizationRestrictionRightIso, liftedScalarExtension,
      pbcFixedScalarExtension,
      pbcDerivedRestrict, pbcRestrict, FiniteCompactScalar.scalarRingMap,
      proEtaleConstantRingMap, proEtaleCoefficientRestrictScalars, sfFixedRestriction,
      Sheaf.restrictScalars, Sheaf.derivedRestrictScalars, Functor.id_obj,
      Functor.comp_obj, eq_mpr_eq_cast, cast_eq, id_eq, a, b, uliftRingHom] using
      realizationScalar_unit (sfIntrinsicDerivedEquivalence T A)
        (sfIntrinsicDerivedEquivalence T B)
        (pbcDerivedScalarAdjunction (FiniteCompactScalar.scalarRingMap φ T)) (b T)
        (FiniteCompactScalar.realizationRestrictionRightIso φ T) M
  have hs : (mateEquiv (b Y) (b Z) (scalarPullbackProEtaleIso a g).inv).natTrans =
      (leftDerivedUpperStarRestrictScalarsIso a g).hom := by
    change (mateEquiv (b Y) (b Z))
      ((mateEquiv (b Y) (b Z)).symm
        (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a g).hom)) = _
    exact Equiv.apply_symm_apply _ _
  have hm := scalarTranspose_inverse_mate
    (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g)
    (b Y) (b Z) (leftDerivedUpperStarRestrictScalarsIso a g)
    (scalarPullbackProEtaleIso a g).symm
    (fixedScalarRestrictionDirectImage a g) hs (by rfl) K
  have h := scalarTranspose_realization_cube
    (pbcDerivedScalarAdjunction (FiniteCompactScalar.scalarRingMap φ Z))
    (pbcDerivedScalarAdjunction (FiniteCompactScalar.scalarRingMap φ Y)) (b Z) (b Y)
    (FiniteCompactScalar.realizationScalarIso φ Z)
    (FiniteCompactScalar.realizationScalarIso φ Y)
    (FiniteCompactScalar.realizationRestrictionIso φ Z)
    (FiniteCompactScalar.realizationRestrictionIso φ Y)
    (directImagePresentation A g) (directImagePresentation B g)
    (directImageScalarRestrictionIso φ g) (fixedScalarRestrictionDirectImage a g)
    (hn Z) (hn Y) (recordedRestriction_directImage_cube φ g) K
  simp only [Functor.id_obj] at hm h
  rw [hm] at h
  rw [← scalarPresentation_eq φ Z, ← scalarPresentation_eq φ Y] at h
  have hi (M : proEtaleDerivedCategory Z A) :
      ((directImageScalarAdjunction φ Y).homEquiv _ _).symm
        ((directImageConstantPush A g).map
            ((directImageScalarAdjunction φ Z).unit.app M) ≫
          (directImageScalarRestrictionIso φ g).hom.app
            ((scalarExtensionFunctor φ Z).obj M)) =
        (directImageScalarComparison φ g).app M := by
    apply ((directImageScalarAdjunction φ Y).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    apply Eq.symm
    apply scalar_unit_of_counit (directImageScalarAdjunction φ Y)
      (directImageScalarAdjunction φ Z) (directImageConstantPush A g)
      (directImageConstantPush B g) (directImageScalarComparison φ g)
      (directImageScalarRestrictionIso φ g).hom
    intro N
    exact ((properScalarCounitSquare φ g).2.2.1 N).2
  change ((directImageScalarAdjunction φ Y).homEquiv _ _).symm
        ((directImageConstantPush A g).map
            ((directImageScalarAdjunction φ Z).unit.app _) ≫
          (directImageScalarRestrictionIso φ g).hom.app _) ≫
      (directImageConstantPush B g).map ((scalarPresentation φ Z).hom.app K) ≫
      (directImagePresentation B g).hom.app ((liftedScalarExtension φ Z).obj K) = _ at h
  erw [hi] at h
  exact h

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
