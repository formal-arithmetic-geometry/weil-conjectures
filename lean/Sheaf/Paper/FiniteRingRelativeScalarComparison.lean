/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import all Sheaf.Paper.FiniteCoefficientDirectImage
import all Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite-ring scalar comparison from relative cohomological dimension

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-direct-image.proof.md, finite rings paragraph; Stacks 0F10 and 0F12
(blueprint: lem-sfb-finite-ring-relative-scalar-comparison).

All categories and tensor products are ordinary and uncompleted. The pro-etale scalar
mate below is the adjunct of scalar extension of the counit. The etale scalar mate and
all normalization maps are the previously published constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The pro-etale coefficient/direct-image comparison, defined by the actual pullback
comparison and the two geometric adjunctions. Its transpose is the pullback comparison
followed by scalar extension of the A-counit.
Source: blueprint latest, scalar-six direct-image proof, finite rings paragraph
(blueprint: lem-sfb-finite-ring-relative-scalar-comparison). -/
def finiteRingScalarDirectImageMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R(lowerStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology Y) a ⟶
      pbcFixedScalarExtension (Scheme.ProEt.topology X) a ⋙
        R(lowerStar (ModuleCat.{u + 1} B) f) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso a f).hom)).natTrans

/-- Finite-ring scalar extension commutes with direct image on constructible finite-Tor
complexes, with the specified restriction/projection and etale/pro-etale normalizations.
The isomorphism `eA` is the canonical beta_A: its hom is required to be the published
comparison map. This records its inverse without imposing a separate qcqs hypothesis.
Source: blueprint latest, scalar-six direct-image proof, finite rings paragraph;
Stacks Tags 0F10, 0F12, 06YT, 06YY and 0GL6
(blueprint: lem-sfb-finite-ring-relative-scalar-comparison).

Proof:
1. On each cohomology stratum, finite_models_of_fixed_lisse supplies finite constant
   models. Fixed-module sheaf descent and bounded constructible derived descent give
   an etale origin J. Translate its constructibility predicate by the existing bridge.
2. Reflect the Tor interval from K through its origin isomorphism and the fixed-module
   comparison. Scalar extension has the resulting lower bound by its tensor presentation
   and reflection of cohomology vanishing under exact scalar restriction.
3. A finite ring is Noetherian and additively torsion, and B is finitely presented over A.
   The existing module-valued relative cohomological-dimension theorem supplies a uniform
   bound for f over the arbitrary field k. Apply finiteConstantProjectionComponent_isIso,
   then identify its constant coefficient with scalarCoefficient by naturality.
4. The proved scalarMate_isIso_of_projection helper makes the etale scalar mate invertible.
   Compose the scalar/tensor comparison, the invertible projection component and the
   coefficient pullback comparison. This identifies restriction of the scalar extension
   of Rf_*J with Rf_* of restriction of J_B, hence gives its lower bound by exactness,
   left t-exactness and reflection. The normalized scalar/projection identity now applies.
5. Cancel the structure morphism to show f is quasi-compact and separated, hence qcqs.
   Apply etaleProEtale_scalar_mate to J and J_B. Its beta and delta components and the
   etale mate are invertible. Cancel the image of delta_X to obtain invertibility on
   nu*J, then use naturality along nu*J isomorphic to K. Keep the very same transport
   equality and take eA to be the canonical directImageComparisonAmbientIso. -/
theorem finiteRingRelativeScalarComparison
    (k : Type u) [Field k] (p l : ℕ) [CharP k p]
    (_hp : p.Prime) (_hl : l.Prime) (_hlp : l ≠ p)
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B)
    (_hA : ∃ n : ℕ, 0 < n ∧ (l ^ n : ℕ) • (1 : A) = 0)
    (_hB : ∃ n : ℕ, 0 < n ∧ (l ^ n : ℕ) • (1 : B) = 0)
    (K : _root_.DerivedCategory.Bounded
      (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)))
    (_hK : ∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X.left A
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)) i).obj K.obj))
    (_hTor : _root_.DerivedCategory.finiteTorAmplitude
      (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)) K.obj) :
    ∃ J : _root_.DerivedCategory.Bounded
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} A)) i).obj J.obj)) ∧
      _root_.DerivedCategory.finiteTorAmplitude
        (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} A)) J.obj ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.obj
        J.obj ≅ K.obj) ∧
      (∃ n : ℤ, ((pbcFixedScalarExtension X.left.smallEtaleTopology a).obj J.obj).IsGE n) ∧
      (∃ n : ℤ, ((pbcFixedScalarExtension Y.left.smallEtaleTopology a).obj
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f.left).obj J.obj)).IsGE n) ∧
      IsIso ((mateEquiv
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f.left)
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f.left)
            (TwoSquare.mk _ _ _ _ (scalarPullbackEtaleIso a f.left).hom)).natTrans.app J.obj) ∧
      IsIso ((finiteRingScalarDirectImageMate a f.left).app K.obj) ∧
      ((Sheaf.derivedRestrictScalars Y.left.smallEtaleTopology a).map
          ((mateEquiv
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f.left)
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f.left)
            (TwoSquare.mk _ _ _ _ (scalarPullbackEtaleIso a f.left).hom)).natTrans.app J.obj) ≫
        (Etale.scalarRestrictionDirectImageMap a f.left).app
          ((Etale.scalarExtension a X.left).obj J.obj) =
        (Etale.scalarTensorIso a Y.left).hom.app
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f.left).obj J.obj) ≫
          ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f.left).app
            J.obj).app (Etale.scalarCoefficient a Y.left) ≫
          R(Etale.lowerStar (ModuleCat.{u + 1} A) f.left).map
            (((Etale.derivedTensor (ModuleCat.{u + 1} A) X.left).obj J.obj).map
                (Etale.scalarCoefficientPullbackIso a f.left).hom ≫
              (Etale.scalarTensorIso a X.left).inv.app J.obj)) ∧
      ∃ eA : (comparisonUpperStar (ModuleCat.{u + 1} A) Y.left).mapDerivedCategory.obj
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f.left).obj J.obj) ≅
          R(lowerStar (ModuleCat.{u + 1} A) f.left).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.obj J.obj),
        eA.hom = (directImageComparisonAmbient A f.left).app J.obj ∧
        (finiteRingScalarDirectImageMate a f.left).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.obj J.obj) ≫
          R(lowerStar (ModuleCat.{u + 1} B) f.left).map
            ((pbcComparisonReduction X.left a).hom.app J.obj) =
        (pbcFixedScalarExtension (Scheme.ProEt.topology Y.left) a).map eA.inv ≫
          (pbcComparisonReduction Y.left a).hom.app
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f.left).obj J.obj) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} B) Y.left).mapDerivedCategory.map
            ((mateEquiv
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f.left)
            (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f.left)
            (TwoSquare.mk _ _ _ _ (scalarPullbackEtaleIso a f.left).hom)).natTrans.app J.obj) ≫
          (directImageComparisonAmbient B f.left).app
            ((pbcFixedScalarExtension X.left.smallEtaleTopology a).obj J.obj) := by
  classical
  have hH (i : ℤ) : IsConstructible A
      ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj) := by
    obtain ⟨S, _, _, hS⟩ := _hK i
    exact ⟨S, fun j ↦ Scheme.finite_models_of_fixed_lisse (S.domain j) A _ (hS j)⟩
  obtain ⟨Je, hJe, ⟨e⟩⟩ := DerivedCategory.boundedConstructible_of_homology A K.property
    (fun i ↦ exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A (hH i))
  let J : _root_.DerivedCategory.Bounded
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨Je, hJe.1⟩
  have hJc (i : ℤ) : Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ i).obj J.obj) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hJe.2 i)
  obtain ⟨c, d, ht⟩ := _hTor
  have hct : _root_.DerivedCategory.torAmplitudeIn _ c d
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.obj J.obj) :=
    (_root_.DerivedCategory.torAmplitudeIn _ c d).prop_of_iso e.symm ht
  have hJt : _root_.DerivedCategory.torAmplitudeIn _ c d J.obj :=
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c d J.obj).mp hct
  have hTor : Etale.DerivedCategory.hasTorAmplitudeIn A X.left c d J.obj :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr hJt
  have hJB : ((pbcFixedScalarExtension X.left.smallEtaleTopology a).obj J.obj).IsGE c :=
    Etale.scalarExtension_lowerBound a X.left J.obj c d hTor
  obtain ⟨N, hN⟩ := Etale.hasFiniteCohomologicalDimensionMorphism A
    (isAddTorsion_of_finite) X.hom Y.hom f.left (Over.w f)
  let M := (ModuleCat.restrictScalars a).obj (ModuleCat.of B B)
  have : Finite M := inferInstanceAs (Finite B)
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have hp := Etale.finiteConstantProjectionComponent_isIso A f.left N.toNat
    (fun F q hq ↦ hN F q (by omega)) J.obj
    (by
      obtain ⟨b, hb⟩ := J.property.2
      exact ⟨b, (_root_.DerivedCategory.isLE_iff J.obj b).mp hb⟩) M
  let eM : Etale.scalarCoefficient a Y.left ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) :=
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (Etale.scalarCoefficientSheafIsoConstant a Y.left)
  have hproj : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) f.left).app J.obj).app (Etale.scalarCoefficient a Y.left)) :=
    (NatTrans.isIso_app_iff_of_iso
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f.left).app J.obj)
      eM).mpr hp
  obtain ⟨b, hb⟩ := J.property.1
  have : J.obj.IsGE b := hb
  have het : IsIso ((Etale.scalarMate a f.left).app J.obj) :=
    Etale.scalarMate_isIso_of_projection a f.left J.obj c b
  let rx := Sheaf.derivedRestrictScalars Y.left.smallEtaleTopology a
  let st := Etale.scalarExtension a X.left
  let sx := Etale.scalarExtension a Y.left
  let rf := R(Etale.lowerStar (ModuleCat.{u + 1} A) f.left)
  let rt := Sheaf.derivedRestrictScalars X.left.smallEtaleTopology a
  let tensor := (Etale.derivedTensor (ModuleCat.{u + 1} A) X.left).obj J.obj
  let eq : rx.obj (sx.obj (rf.obj J.obj)) ≅ rf.obj (rt.obj (st.obj J.obj)) :=
    (Etale.scalarTensorIso a Y.left).app (rf.obj J.obj) ≪≫
      asIso (((Etale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} A) f.left).app J.obj).app (Etale.scalarCoefficient a Y.left)) ≪≫
      rf.mapIso (tensor.mapIso (Etale.scalarCoefficientPullbackIso a f.left) ≪≫
        (Etale.scalarTensorIso a X.left).symm.app J.obj)
  have hr : (rt.obj (st.obj J.obj)).IsGE c :=
    (Sheaf.restrictScalars X.left.smallEtaleTopology a).isGE_mapDerivedCategory_obj _ c
  have hrr : (rf.obj (rt.obj (st.obj J.obj))).IsGE c :=
    Etale.isGE_rightDerivedLowerStar_obj A f.left _ c
  have hQ : (sx.obj (rf.obj J.obj)).IsGE c := by
    have hres : (rx.obj (sx.obj (rf.obj J.obj))).IsGE c :=
      _root_.DerivedCategory.TStructure.t.isGE_of_iso eq.symm c
    apply (_root_.DerivedCategory.isGE_iff _ c).mpr
    intro q hq
    apply Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (Sheaf.restrictScalars Y.left.smallEtaleTopology a)
    exact (_root_.DerivedCategory.isGE_iff _ c).mp hres q hq
  have hrestrict := Etale.scalarMate_restrict_eq_projection a f.left
    ⟨J.obj, J.property.1⟩ ⟨⟨st.obj J.obj, ⟨c, hJB⟩⟩, rfl⟩
    ⟨⟨sx.obj (rf.obj J.obj), ⟨c, hQ⟩⟩, rfl⟩
  have : QuasiCompact (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : IsSeparated (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  let eA := directImageComparisonAmbientIso A f.left J.obj J.property.1
  have htransport := etaleProEtale_scalar_mate a f.left J.obj J.property.1 ⟨c, hJB⟩
  have : IsIso ((directImageComparisonAmbient B f.left).app
      ((pbcFixedScalarExtension X.left.smallEtaleTopology a).obj J.obj)) :=
    directImageComparisonAmbient_isIso B f.left _ ⟨c, hJB⟩
  have hcomp : IsIso ((finiteRingScalarDirectImageMate a f.left).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.obj J.obj) ≫
      R(lowerStar (ModuleCat.{u + 1} B) f.left).map
        ((pbcComparisonReduction X.left a).hom.app J.obj)) := by
    rw [show (finiteRingScalarDirectImageMate a f.left).app _ ≫ _ = _ from htransport]
    have hmate : IsIso ((mateEquiv
        (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f.left)
        (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f.left)
        (TwoSquare.mk _ _ _ _ (scalarPullbackEtaleIso a f.left).hom)).natTrans.app J.obj) :=
      het
    infer_instance
  have hpro : IsIso ((finiteRingScalarDirectImageMate a f.left).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X.left).mapDerivedCategory.obj J.obj)) :=
    IsIso.of_isIso_comp_right _
      (R(lowerStar (ModuleCat.{u + 1} B) f.left).map
        ((pbcComparisonReduction X.left a).hom.app J.obj))
  have hKiso : IsIso ((finiteRingScalarDirectImageMate a f.left).app K.obj) :=
    (NatTrans.isIso_app_iff_of_iso (finiteRingScalarDirectImageMate a f.left) e).mp hpro
  exact ⟨J, hJc, ⟨c, d, hJt⟩, ⟨e⟩, ⟨c, hJB⟩, ⟨c, hQ⟩, het, hKiso,
    hrestrict, eA, rfl, htransport⟩

end AlgebraicGeometry.ProEtale
