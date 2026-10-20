/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-! # Smooth base change for the finite-level exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-smb-extraordinary.md and its proof (blueprint: lem-pur-smb-extraordinary).

The exceptional functors are the recorded finite-level composites ν^* f× Rν_*.
The canonical arrow is pasted from the comparison-site mate and the ordinary etale
exceptional mate. No right adjoint on the ambient pro-etale category is assumed.

## Main declarations

- `smoothExceptionalComparisonMate`: the unit-square-counit comparison-site mate.
- `smoothExceptionalProEtaleBaseChangeMap`: the canonical exceptional comparison.
- `smoothExceptionalBaseChangeStatement`: its invertibility on Dᵇ_ctf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale
open Scheme

/-- Finiteness at the positive coefficient level of the fixed purity setting.
Source: blueprint main-20261015, def-pur-conventions, finite-stage convention;
lem-pur-smb-extraordinary, proof opening (blueprint: lem-pur-smb-extraordinary). -/
noncomputable instance smoothExceptionalCoefficientFinite
    (P : WeilConjectures.PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The canonical comparison v_e^* Rν_Y,* → Rν_Y',* v_p^*.
This is the mate of the inverse comparison-pullback square: first the comparison
unit, then Rν_* of that square, and finally Rν_* of the pulled-back counit.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md, comparison
of actual adjoints and transport of counits (blueprint: lem-pur-smb-extraordinary). -/
noncomputable def smoothExceptionalComparisonMate (A : Type u) [CommRing A]
    {U V : Scheme.{u}} (v : U ⟶ V)
    (K : DerivedCategory
      (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) v).mapDerivedCategory.obj
        ((comparisonLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V).rightDerivedFunctor.obj K) ⟶
      (comparisonLowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).rightDerivedFunctor.obj
          ((sfFixedDerivedPullback A v).obj K) :=
  (derivedComparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).unit.app _ ≫
    (comparisonLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).rightDerivedFunctor.map
        ((sfDerivedComparisonPullbackIso A v).inv.app _ ≫
          (sfFixedDerivedPullback A v).map
            ((derivedComparisonAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V).counit.app K))

/-- The specified comparison Lu^* Rf^! K → Rf'^! Lv^* K, in canonical fixed-scalar
coordinates. Its factors are the comparison-pullback square, the ordinary etale
exceptional counit-transpose, and f'^× applied to the comparison-site mate.
The target compactification is the base change of c. Quasi-compactness of f'
is derived from the Cartesian square, so v is arbitrary.
Source: blueprint main-20261015, lem-pur-smb-extraordinary.proof.md, transport
of the specified canonical map (blueprint: lem-pur-smb-extraordinary). -/
noncomputable def smoothExceptionalProEtaleBaseChangeMap
    (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {u' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {v : Y' ⟶ Y}
    (sq : IsPullback u' f' f v) [QuasiCompact f] (c : Compactification f)
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfFixedDerivedPullback A u').obj ((sfFiniteExceptionalFixed A c).obj K) ⟶
      (sfFiniteExceptionalFixed A (c.ofIsPullback sq)).obj
        ((sfFixedDerivedPullback A v).obj K) :=
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  letI := c.hasCompactification
  letI := (c.ofIsPullback sq).hasCompactification
  (sfDerivedComparisonPullbackIso A u').hom.app
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj
        ((comparisonLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).rightDerivedFunctor.obj K)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X').mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ u').inv.app _ ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap (ULift.{u + 1, u} A) sq).app
          ((comparisonLowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).rightDerivedFunctor.obj K) ≫
        (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f').map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ v).hom.app _ ≫
            smoothExceptionalComparisonMate A v K))

private theorem smoothExceptional_invertibleExponent
    (P : WeilConjectures.PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) : HasInvertibleExponent P.Coefficient T := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  have hd := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hl : (l : O) ∈ m := by
    apply (hd.2.1 (l : O)).mpr
    change Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l]
    change spectralNorm ℚ_[l] E (algebraMap ℚ_[l] E (l : ℚ_[l])) < 1
    rw [spectralNorm_extends (K := ℚ_[l]) (L := E)]
    exact Padic.norm_p_lt_one
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set O) = m :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  refine ⟨l ^ P.level, pow_pos (Nat.Prime.pos Fact.out) _, ?_, ?_⟩
  · apply ULift.ext
    change ((l ^ P.level : ℕ) : Padic.coefficientExtensionRing l E P.level) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E P.level)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    change (l : O) ^ P.level ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set O) ^ P.level
    rw [hgen]
    exact Ideal.pow_mem_pow hl _
  · apply T.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    change IsUnit ((T.presheaf.germ ⊤ x hx).hom _)
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      (P.coefficientPrime_isUnit_stalk T a x).pow P.level

private theorem smoothExceptional_origin
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} P.Ring))))
    (hK : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos Y K) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Y K := by
  classical
  let R := finiteCoefficientIntrinsicRealization Y P.Ring
  have : R.IsEquivalence := (finiteCoefficientIntrinsicRealization_exact Y P.Ring).1
  have : R.Additive := finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have hi := hK.1
  obtain ⟨a, ha⟩ := hi.1.bddBelow
  obtain ⟨b, hb⟩ := hi.1.bddAbove
  have hv (i : ℤ) (h : i < min a b ∨ max a b < i) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj (R.mapDerivedCategory.obj K)) := by
    by_contra hn
    rcases h with h | h
    · exact (not_lt_of_ge (ha hn)) (lt_of_lt_of_le h (min_le_left _ _))
    · exact (not_lt_of_ge (hb hn)) (lt_of_le_of_lt (le_max_right _ _) h)
  obtain ⟨L, ⟨e⟩⟩ := ((Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1
    (R.mapDerivedCategory.obj K)).mpr ⟨hi.2, min a b, max a b, min_le_max, hv⟩
  let C := comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let e' : C.mapDerivedCategory.obj L.obj ≅ K := R.mapDerivedCategory.preimageIso
    ((Functor.mapDerivedCategoryCompIso C R).symm.app L.obj ≪≫ e)
  obtain ⟨c, d, _, hz⟩ := L.property.2
  exact ⟨L.obj, ⟨c, (DerivedCategory.isGE_iff L.obj c).mpr
    (fun i hi ↦ hz i (Or.inl hi))⟩, ⟨e'⟩⟩

private theorem smoothExceptional_counit_isIso
    (A : Type u) [CommRing A] {Y : Scheme.{u}}
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hK : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y K) :
    IsIso ((derivedComparisonAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).counit.app K) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := hK
  let adj := derivedComparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y G hG
  have : IsIso (adj.counit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        Y).mapDerivedCategory.obj G)) := by
    exact isIso_of_hom_comp_eq_id
      ((comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.map
          (adj.unit.app G)) (adj.left_triangle_components G)
  have he := adj.counit.naturality e.inv
  dsimp at he
  have : IsIso (adj.counit.app K ≫ e.inv) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.inv

private theorem smoothExceptional_mate_isIso
    (A : Type u) [CommRing A] {U V : Scheme.{u}} (v : U ⟶ V)
    (K : DerivedCategory
      (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hK : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V K) :
    IsIso (smoothExceptionalComparisonMate A v K) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have hR : DerivedCategory.TStructure.t.plus
      ((comparisonLowerStar B V).rightDerivedFunctor.obj K) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      ((comparisonLowerStar B V).rightDerivedFunctorPlusCompatibility.app ⟨K, hK.plus⟩)
      ((comparisonLowerStar B V).rightDerivedFunctorPlus.obj ⟨K, hK.plus⟩).property
  obtain ⟨n, hn⟩ := hR
  have := hn
  have hu : DerivedCategory.TStructure.t.plus
      ((Etale.upperStar B v).mapDerivedCategory.obj
        ((comparisonLowerStar B V).rightDerivedFunctor.obj K)) :=
    ⟨n, (Etale.upperStar B v).isGE_mapDerivedCategory_obj _ n⟩
  have := isIso_derivedComparisonAdjunction_unit_app B U _ hu
  have := smoothExceptional_counit_isIso A K hK
  unfold smoothExceptionalComparisonMate
  infer_instance

/-- Smooth arbitrary base change for the canonical finite-level exceptional comparison.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-smb-extraordinary.md and its proof (blueprint: lem-pur-smb-extraordinary).

Proof: use the displayed factorization of the specified canonical comparison.

1. The coefficient prime ell belongs to the maximal ideal (varpi_E) of the DVR O_E.
Thus ell^n annihilates O_E/(varpi_E^n). It is invertible on every scheme over the
fixed field, giving the ordinary etale theorem's invertible-exponent hypothesis.
2. Intrinsic bounded constructibility gives a bounded constructible etale complex G
whose comparison inverse image is isomorphic to K, by finite-ring derived origin.
The intrinsic realization is an exact equivalence, so the isomorphism lifts back
to the fixed coefficient presentation. In particular G is bounded below.
3. Site comparison makes the unit at G invertible. The left triangle identity then
makes the counit at its comparison inverse image invertible; naturality transports
this to K. The right derived comparison restriction of K is bounded below, and
exact etale inverse image preserves that bound. The unit at this latter object is
therefore also invertible. These facts make every factor of the specified
comparison-site mate invertible.
4. Base change preserves smoothness of pure relative dimension and quasi-compactness.
The compactifications c and its base change supply the ordinary exceptional
functors. Local finite type over the field makes the base locally Noetherian,
hence quasi-separated. Apply ordinary canonical smooth exceptional base change.
5. In the defining factorization of the pro-etale comparison, the comparison-pullback
maps and the exact/derived pullback identifications are isomorphisms. The ordinary
exceptional comparison and the comparison-site mate are invertible by steps 3–4.
Functoriality and composition preserve their invertibility, proving the assertion.

This follows the ordinary smooth-base-change input of the unit, through affine-space
adjunctions and etale charts. It imposes no condition on the horizontal base change
beyond the stated domain, and applies to empty schemes, K = 0, and relative dimension zero.
-/
theorem smoothExceptionalBaseChangeStatement
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of P.field.k))]
    [X.Over (Spec (CommRingCat.of P.field.k))]
    [Y'.Over (Spec (CommRingCat.of P.field.k))]
    [Y.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    [u'.IsOver (Spec (CommRingCat.of P.field.k))]
    [f'.IsOver (Spec (CommRingCat.of P.field.k))]
    [f.IsOver (Spec (CommRingCat.of P.field.k))]
    [v.IsOver (Spec (CommRingCat.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : ChosenCartesianSquare u' f' f v)
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f)
    (K : DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} P.Ring))))
    (_hK : WeilConjectures.finiteTorConstructibleProEtaleModule
      P.coefficients.l P.extension P.level P.level_pos Y K) :
    SmoothOfRelativeDimension d f' ∧
      IsIso (smoothExceptionalProEtaleBaseChangeMap P.Ring
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd) c K) := by
  -- Use the displayed factorization of the canonical map to shorten the DAG plan above.
  let hsq := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  have := c.hasCompactification
  have := (c.ofIsPullback hsq).hasCompactification
  have : Finite P.Coefficient :=
    inferInstanceAs (Finite (ULift.{u + 1, u} P.Ring))
  have : HasInvertibleExponent P.Coefficient X :=
    smoothExceptional_invertibleExponent P
      (X ↘ Spec (.of P.field.k))
  have := smoothOfRelativeDimension_isStableUnderBaseChange d
  have hs : SmoothOfRelativeDimension d f' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) hsq inferInstance
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  refine ⟨hs, ?_⟩
  have hBC : IsIso (Etale.rightDerivedUpperShriekBaseChangeMap
      (ULift.{u + 1, u} P.Ring) hsq) :=
    Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
      P.Coefficient f d hsq
  have := smoothExceptional_mate_isIso P.Ring v K (smoothExceptional_origin P Y K _hK)
  dsimp only [smoothExceptionalProEtaleBaseChangeMap]
  infer_instance

end AlgebraicGeometry.ProEtale
