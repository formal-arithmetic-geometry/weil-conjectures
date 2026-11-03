/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.AlgebraicGeometry.RelativeTangentBundle.RelativeTangentBundle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.Algebra.CharP.Algebra
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothNormalizedExistence
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # The normalized smooth diagonal orientation

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-prop-sp-orientation/
_section.md and sk-prop-sp-orientation.proof.md
(blueprint: sk-prop-sp-orientation).

The ordinary finite-coefficient orientation retains the actual diagonal, normalized
Rees deformation and inverse vector-integration equation. Its pro-etale realization
is specified using the comparison-adjunction unit, with both endpoints in Dctf.
The field is finite or algebraically closed; no fixed finite-field closure is imposed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale

private theorem ordinaryUnitCtf
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    DerivedCategory.boundedConstructibleFiniteTor A T (𝟙_ _) := by
  let U := 𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat A))
  have hbc := DerivedCategory.boundedConstructible_singleFunctor_obj U 0
  have ht := torAmplitudeIn_singleFunctor_zero_of_flat (ModuleCat A) U
    (ObjectProperty.prop_unit (ObjectProperty.flat (A := Sheaf T.smallEtaleTopology
      (ModuleCat A))))
  let e := singleFunctorObjUnitIso (ModuleCat A) T
  exact ⟨(DerivedCategory.boundedConstructible (ModuleCat A) T).prop_of_iso e hbc,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e ⟨0, 0, ht⟩⟩

private theorem normalizedOrientation_unique
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (G : FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit (N : Γ(X, ⊤)))
    {α β : dualizingComplex A f ≅ line A N hA X d}
    (hα : OrientationNormalized A N hN hA f d G hX α)
    (hβ : OrientationNormalized A N hN hA f d G hX β) : α = β := by
  let := G
  obtain ⟨κ, hκ, sq, ha⟩ := hα
  obtain ⟨κ', hκ', sq', hb⟩ := hβ
  have hk : κ' = κ :=
    (FiniteRingSectionDeformation.existsUnique_normalized N hN A hA hX d
      (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).unique hκ' hκ
  subst κ'
  have := normalSectionMap_isIso A d (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) sq N hN hA hX
  have := (FiniteRingSectionDeformation.bundleAdjoint_isIso
    N hN A hA X hX d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
  apply Iso.ext
  exact (cancel_mono
    (FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA X hX d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
        normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
          (pullback.diagonal_fst f) sq)).mp (ha.symm.trans hb)

/-- The canonical orientation of a separated smooth morphism of pure dimension d.
The coefficient is the existing size presentation of Z/(ell^n), and the target is
its ordered root-line tensor power shifted by +2d. The pro-etale exceptional object
is the finite etale computation of the recorded relative dualizing complex.

`OrientationNormalized` is the actual equation of the diagonal base-change factor
and the unique t=1-normalized Rees specialization with the vector-bundle adjoint,
including its associated-graded cone transport and zero-section restriction.
The displayed comparison-unit equation fixes the pro-etale arrow itself.

Source: latest blueprint sk-prop-sp-orientation, statement and displayed composite
(blueprint: sk-prop-sp-orientation).

Proof plan:
1. The self-product projection is smooth of dimension d and separated finite type.
   Its closed diagonal is a regular section. Centred coordinates identify Sym of
   its conormal with its associated graded, including the augmentation; the canonical
   conormal identification with Omega identifies this normal bundle with T_(X/Y).
   This gives the Geometry certificate, also for d=0 and the empty source.
2. Apply smooth exceptional self-product base change at the unit and restrict by
   the diagonal. The derived composition and identity comparisons give the first
   factor from omega_f to the diagonal pullback of omega_p1, in that direction.
3. Apply finite-ring section deformation at N=ell^n. Its unique family comparison
   is the identity at t=1. Invert its zero-fibre restriction and transport through
   the homogeneous-normalized Rees/associated-graded and conormal comparisons.
4. Pull back inverse integration-normalized vector purity along zero. The root-line
   pullback comparison identifies its target with Lambda_X(d)[2d]. This composite
   satisfies OrientationNormalized. Uniqueness follows by cancellation of the bundle
   adjoint and uniqueness of the normalized family. Rank-zero integration is identity.
5. Finite etale/pro-etale comparison preserves these counits and transposes. The
   comparison-adjunction unit supplies finiteGeneralRingDualizingUnitMap. Its inverse
   followed by the comparison image of the ordinary orientation gives theta and the
   displayed equation. The root line is bounded constructible with finite Tor
   amplitude; the isomorphism gives the same properties for omega_f. Fullness and
   faithfulness transport uniqueness to the actual small pro-etale category.
-/
theorem existsUnique_smoothDiagonalOrientation
    (ell : ℕ) [Fact ell.Prime] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (p : ℕ) [Fact p.Prime] [CharP k p] (hEll : ell ≠ p)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] (d : ℕ)
    [SmoothOfRelativeDimension d f.left] :
    letI := isNoetherian_of_locallyOfFiniteType X.hom
    letI := isNoetherian_of_locallyOfFiniteType Y.hom
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
    letI : QuasiCompact f.left := inferInstance
    letI : HasCompactification f.left := HasCompactification.of_over f
    let A := coefficient.{u} ell n
    let hA : ((ell ^ n : ℕ) : A) = 0 := CharP.cast_eq_zero _ _
    ∃ hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)),
      ∃ G : Etale.FiniteRingSectionDeformation.Geometry d
          (pullback.fst f.left f.left) (pullback.diagonal f.left),
        ∃! theta : (exceptional A f.left).obj (finiteGeneralRingUnit A Y.left) ≅
            (comparison A X.left).obj (line A (ell ^ n) hA X.left d),
          ∃ alpha : Etale.dualizingComplex A f.left ≅ line A (ell ^ n) hA X.left d,
            OrientationNormalized A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
                hA f.left d G hX alpha ∧
            IsCtf A X.left
                ((exceptional A f.left).obj (finiteGeneralRingUnit A Y.left)) ∧
            IsCtf A X.left ((comparison A X.left).obj (line A (ell ^ n) hA X.left d)) ∧
            finiteGeneralRingDualizingUnitMap A f.left ≫ theta.hom =
              (comparison A X.left).map alpha.hom := by
  classical
  have _ := hn
  have _ := hbase
  let := isNoetherian_of_locallyOfFiniteType X.hom
  let := isNoetherian_of_locallyOfFiniteType Y.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiCompact f.left := inferInstance
  let : HasCompactification f.left := HasCompactification.of_over f
  let A := coefficient.{u} ell n
  let hA : ((ell ^ n : ℕ) : A) = 0 := CharP.cast_eq_zero _ _
  have hl : IsUnit (ell : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime) hEll.symm)
  have hY : IsUnit ((ell ^ n : ℕ) : Γ(Y.left, ⊤)) := by
    simpa only [map_natCast, Nat.cast_pow] using
      (hl.map ((Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appTop).hom).pow n
  have hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)) := by
    simpa only [map_natCast, Nat.cast_pow] using
      (hl.map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom).pow n
  have : HasInvertibleExponent A Y.left :=
    ⟨ell ^ n, pow_pos (Fact.out : ell.Prime).pos n, hA, hY⟩
  obtain ⟨G, alpha, hnorm⟩ := generalRingNormalizedOrientation A (ell ^ n)
    (pow_pos (Fact.out : ell.Prime).pos n) hA f.left d hX
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) Y.left
    (Etale.ordinaryFiniteUnit A Y.left) ⟨0, inferInstance⟩
  have : IsIso (finiteGeneralRingDualizingUnitMap A f.left) := by
    unfold finiteGeneralRingDualizingUnitMap
    infer_instance
  let theta := (asIso (finiteGeneralRingDualizingUnitMap A f.left)).symm ≪≫
    (comparison A X.left).mapIso alpha
  have htheta : finiteGeneralRingDualizingUnitMap A f.left ≫ theta.hom =
      (comparison A X.left).map alpha.hom := by
    dsimp only [theta, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    exact IsIso.hom_inv_id_assoc _ _
  have homega : IsCtf A X.left ((comparison A X.left).obj
      (Etale.dualizingComplex A f.left)) :=
    comparisonCtf A X.left _ (ordinaryExceptionalCtf A f.left d _ (ordinaryUnitCtf A _))
  have htarget : IsCtf A X.left ((comparison A X.left).obj (line A (ell ^ n) hA X.left d)) :=
    isCtfOfIso A X.left ((comparison A X.left).mapIso alpha) homega
  refine ⟨hX, G, theta, ⟨alpha, hnorm, isCtfOfIso A X.left theta.symm htarget,
    htarget, htheta⟩, ?_⟩
  intro theta' htheta'
  obtain ⟨alpha', hnorm', _, _, heq'⟩ := htheta'
  have ha : alpha' = alpha :=
    normalizedOrientation_unique A (ell ^ n) (pow_pos (Fact.out : ell.Prime).pos n)
      hA f.left d G hX hnorm' hnorm
  apply Iso.ext
  apply (cancel_epi (finiteGeneralRingDualizingUnitMap A f.left)).mp
  exact heq'.trans (ha ▸ htheta.symm)

end AlgebraicGeometry.ProEtale
