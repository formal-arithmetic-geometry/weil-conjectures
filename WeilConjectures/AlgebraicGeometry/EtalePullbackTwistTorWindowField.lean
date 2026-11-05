/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtalePullbackTwistTorWindow
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Etale.EtalePullbackLineFlatModel
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-! # Etale pullback and finite twists over finite or algebraically closed fields

Source: Stacks Project, Tags 03TT, 0963, 095I and Section 03PK;
the chart calculation in blueprint det-sp-reduction-exceptional.
(blueprint: lem-sp-etale-pullback-twist-tor-window).

This states the corrected field domain, including algebraically closed fields of
characteristic zero, using the published termwise and derived twist constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

/-- Transport a model's constructible cohomology and Tor window to its represented object.
Boundedness follows by testing Tor amplitude against the tensor unit.
Source: Stacks Project Tag 03TT, lemma-when-ctf
(blueprint: lem-sp-etale-pullback-twist-tor-window). -/
private theorem boundedConstructible_of_model_field
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (a b : ℤ) (hab : a ≤ b)
    (hc : ∀ j, Scheme.IsConstructibleEtaleModuleSheaf (Q.homology j))
    (hTor : DerivedCategory.hasTorAmplitudeIn R X a b (_root_.DerivedCategory.Q.obj Q))
    (L : DerivedCategoryModule R X) (e : _root_.DerivedCategory.Q.obj Q ≅ L) :
    DerivedCategory.isBoundedConstructible R X L ∧
      DerivedCategory.hasTorAmplitudeIn R X a b L := by
  have ht := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
    (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hTor)
  have hh := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht
  refine ⟨⟨?_, a, b, hab, ?_⟩,
    DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 ht⟩
  · intro j
    have : Scheme.IsConstructibleSheaf (Q.homology j) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc j)
    let eh := ((_root_.DerivedCategory.homologyFunctorFactors _ j).app Q).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ j).mapIso e
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (Scheme.IsConstructibleSheaf.of_iso (F := Q.homology j) eh)
  · intro j hj
    rcases hj with hj | hj
    · exact (_root_.DerivedCategory.isGE_iff L a).1 hh.1 j hj
    · exact (_root_.DerivedCategory.isLE_iff L b).1 hh.2 j hj

/-- Invert the canonical model comparison and move the shift out of its second factor.
Source: Stacks Project Tags 0963 and 0FNH
(blueprint: lem-sp-etale-pullback-twist-tor-window). -/
private noncomputable def lineModelIso_field
    (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (K : DerivedCategoryModule R Y) (e : _root_.DerivedCategory.Q.obj P ≅ K)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (s : ℤ)
    (h : etaleLineRepresentativeComparisonIsIsoOnSite (ModuleCat.{u + 1} R) X
      (((upperStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).obj P)
      ((upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K)
      (etalePullbackRepresentative R f P K e) E s) :
    _root_.DerivedCategory.Q.obj (etalePullbackLineModel R f P E s) ≅
      (((derivedTensor (ModuleCat.{u + 1} R) X).obj
        ((upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj E))⟦s⟧ :=
  have : IsIso (etalePullbackLineComparison R f P K e E s) := h
  (asIso (etalePullbackLineComparison R f P K e E s)).symm ≪≫
    ((((derivedTensor (ModuleCat.{u + 1} R) X).obj
      ((upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K)).commShiftIso s).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj E))

/-- Pullback, finite nonnegative Tate twist, and shift carry every specified flat
constructible representative in [a,b] to a K-flat representative in [a-s,b-s].
The represented object is bounded constructible with that same Tor interval.
The last clause applies to every bounded constructible K, independently of a chosen P.

Source: Stacks Project, Tags 03TT (lemma-when-ctf), 0963 (lemma-pullback-ctf),
095I (lemma-tensor-product-constructible) and Section 03PK (section-kummer)
(blueprint: lem-sp-etale-pullback-twist-tor-window).

Proof:
1. A field is Noetherian. Apply lem-weil-pbc-finite-type-over-noetherian to the
   structure maps of T and T' to obtain Noetherian schemes.
2. The prime ell differs from ringChar k, so N = ell^n is invertible in k
   and every local ring of T', including characteristic zero and n=0. Apply
   lem-asd-finite-etale-twist-line to obtain the locally trivial rank-one module
   R(c), including the zeroth twist; R need not be flat over Z/N.
3. Apply lem-sp-etale-pullback-line-flat-model to P, its representing isomorphism,
   the morphism f and that line. It gives flat constructible terms, K-flatness,
   and support [a-s,b-s]. The chain-shift comparison of
   lem-weil-pbc-total-tensor-integer-shifts and localization identify the represented
   object with the shift of the whole derived tensor, as in def-kun-derived-tensor.
   In degree j the term comes from P in degree j+s, fixing the endpoint signs.
4. The line-model theorem gives constructible cohomology and vanishing after
   tensor with every degree-zero module outside [a-s,b-s]. These are precisely
   constructibility and def-kun-tor-amplitude; finite support gives boundedness.
5. For an arbitrary bounded constructible K in the given Tor interval, use
   lem-sf-etale-flat-constructible directly to obtain P. Apply
   the line-model theorem with the constant R line and zero shift; multiplication
   identifies tensor with R with the original pullback, preserving [a,b]. -/
theorem etale_pullback_twist_tor_window_finite_or_algClosed
    (k : Type u) [Field k] (_hbase : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) (_hell : ell.Prime) (_hne : ringChar k ≠ ell)
    (T T' : Over (Spec (CommRingCat.of k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [IsSeparated T'.hom] [LocallyOfFiniteType T'.hom] [QuasiCompact T'.hom]
    (f : T' ⟶ T) (n : ℕ)
    (R : Type (u + 1)) [CommRing R] [Finite R] (hR : ((ell ^ n : ℕ) : R) = 0)
    (a b : ℤ) (_hab : a ≤ b) :
    (∀ (K : DerivedCategoryModule R T.left),
      DerivedCategory.isBoundedConstructible R T.left K →
      DerivedCategory.hasTorAmplitudeIn R T.left a b K →
      ∀ (P : CochainComplex (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ),
      Nonempty (_root_.DerivedCategory.Q.obj P ≅ K) →
      (∀ i : ℤ, exactFunctor _ _
        (@tensorRight _ _ (Sheaf.monoidalCategory T.left.smallEtaleTopology
          (ModuleCat.{u + 1} R)) (P.X i))) →
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i)) →
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) →
      ∀ (c : ℕ) (s : ℤ),
      (∀ j : ℤ, exactFunctor _ _
        (@tensorRight _ _ (Sheaf.monoidalCategory T'.left.smallEtaleTopology
          (ModuleCat.{u + 1} R)) ((pullbackTwistComplex R f.left (ell ^ n) hR P c s).X j))) ∧
      (∀ j : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((pullbackTwistComplex R f.left (ell ^ n) hR P c s).X j)) ∧
      (∀ j : ℤ, (j < a - s ∨ b - s < j) →
        IsZero ((pullbackTwistComplex R f.left (ell ^ n) hR P c s).X j)) ∧
      @MorphismProperty.kFlat _ _ (pullbackTwistComplexMonoidal R T'.left)
        (HomologicalComplex.quasiIso
          (Sheaf T'.left.smallEtaleTopology (ModuleCat.{u + 1} R)) (.up ℤ))
        (pullbackTwistComplex R f.left (ell ^ n) hR P c s) ∧
      Nonempty (_root_.DerivedCategory.Q.obj
        (pullbackTwistComplex R f.left (ell ^ n) hR P c s) ≅
          pullbackTwistDerived R f.left (ell ^ n) hR K c s) ∧
      DerivedCategory.isBoundedConstructible R T'.left
        (pullbackTwistDerived R f.left (ell ^ n) hR K c s) ∧
      DerivedCategory.hasTorAmplitudeIn R T'.left (a - s) (b - s)
        (pullbackTwistDerived R f.left (ell ^ n) hR K c s)) ∧
    (∀ K : DerivedCategoryModule R T.left,
      DerivedCategory.isBoundedConstructible R T.left K →
      DerivedCategory.hasTorAmplitudeIn R T.left a b K →
      DerivedCategory.isBoundedConstructible R T'.left
        ((upperStar (ModuleCat.{u + 1} R) f.left).mapDerivedCategory.obj K) ∧
      DerivedCategory.hasTorAmplitudeIn R T'.left a b
        ((upperStar (ModuleCat.{u + 1} R) f.left).mapDerivedCategory.obj K)) := by
  classical
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : IsNoetherian T.left := ⟨⟩
  have : IsLocallyNoetherian T'.left := LocallyOfFiniteType.isLocallyNoetherian T'.hom
  have : CompactSpace T'.left := QuasiCompact.compactSpace_of_compactSpace T'.hom
  have : IsNoetherian T'.left := ⟨⟩
  have hN : 0 < ell ^ n := pow_pos _hell.pos n
  have hk : IsUnit ((ell ^ n : ℕ) : k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.2 (CharP.cast_ne_zero_of_ne_of_prime k _hell
      _hne)).pow n
  have hInv : ∀ t : T'.left, IsUnit ((ell ^ n : ℕ) : T'.left.presheaf.stalk t) := by
    intro t
    let φ := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T'.hom.appTop ≫
      T'.left.presheaf.germ ⊤ t (by trivial)
    simpa only [map_natCast] using hk.map φ.hom
  have main : ∀ (K : DerivedCategoryModule R T.left)
      (P : CochainComplex (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
      (e : _root_.DerivedCategory.Q.obj P ≅ K),
      (∀ i : ℤ, exactFunctor _ _ (tensorRight (P.X i))) →
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i)) →
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) →
      ∀ (c : ℕ) (s : ℤ),
      ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage T'.left,
        etalePullbackLineAssertions R f.left P K e
          (Scheme.finiteEtaleTateTwist T'.left (ell ^ n) R hR c) s a b V := by
    intro K P e hf hc hz c s
    obtain ⟨V, hV⟩ := (Scheme.finite_etale_torsion_twist_line
      T'.left (ell ^ n) hN hInv R hR c).1
    refine ⟨V, etale_pullback_line_flat_model R f.left P a b _hab hf hc hz K e
      (Scheme.finiteEtaleTateTwist T'.left (ell ^ n) R hR c) s V ?_⟩
    intro i
    obtain ⟨ei⟩ := hV i
    let U := V.etalePrecoverageToEtale i
    let cst := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
      (T'.left.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} R)
      Over.mkIdTerminal
    exact ⟨(Scheme.overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} R) U _).symm ≪≫
      (Scheme.Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapIso ei ≪≫
      cst.app (ModuleCat.of R R)⟩
  constructor
  · intro K _hK _hTor P he hf hc hz c s
    obtain ⟨e⟩ := he
    obtain ⟨V, hmodel⟩ := main K P e hf hc hz c s
    obtain ⟨hflat, hcons, hzero, hkflat, hcomp, hcoh, htor, -⟩ := hmodel
    let eL := lineModelIso_field R f.left P K e
      (Scheme.finiteEtaleTateTwist T'.left (ell ^ n) R hR c) s hcomp
    have hbc := boundedConstructible_of_model_field R T'.left _ (a - s) (b - s)
      (by omega) hcoh htor _ eL
    exact ⟨hflat, hcons, hzero, hkflat, ⟨eL⟩, hbc⟩
  · intro K hK hTor
    obtain ⟨P, hf, hc, hz, ⟨e⟩⟩ :=
      (hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel R T.left a b _hab K hK).1
        hTor
    obtain ⟨V, hmodel⟩ := main K P e (fun i ↦ (hf i).tensorRight) hc hz 0 0
    obtain ⟨-, -, -, -, hcomp, hcoh, htor, -⟩ := hmodel
    let eL := lineModelIso_field R f.left P K e
      (Scheme.finiteEtaleTateTwist T'.left (ell ^ n) R hR 0) 0 hcomp
    let L := (upperStar (ModuleCat.{u + 1} R) f.left).mapDerivedCategory.obj K
    let eu : _root_.DerivedCategory.Q.obj
        (etalePullbackLineModel R f.left P
          (Scheme.finiteEtaleTateTwist T'.left (ell ^ n) R hR 0) 0) ≅ L :=
      eL ≪≫ (shiftFunctorZero _ ℤ).app _ ≪≫
        whiskerLeftIso L (_root_.DerivedCategory.singleFunctorObjUnitIso _) ≪≫ ρ_ L
    simpa only [sub_zero] using
      boundedConstructible_of_model_field R T'.left _ (a - 0) (b - 0) (by omega)
        hcoh htor L eu


end AlgebraicGeometry.Etale
