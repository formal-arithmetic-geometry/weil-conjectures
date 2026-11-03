/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Compactification
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.LowerShriek.Formalism.Compactification
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor

/-! # Canonical finite-ring Frobenius compact-support transport

Source: latest blueprint, lem-trf-frobenius-operator-compact-description, power clause;
released finite-ring repair P1 (blueprint: lem-trf-compact-frobenius-transport-composition).
Compactifications below are computational representatives quantified in the conclusion,
never additional data of a Weil pair. All functors are ordinary and uncompleted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.CompactFrobeniusTransport

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (D : FiniteFieldDatum.{u})

variable (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]

omit hsep in
/-- Cartesian structure square for the actual power maps.
Source: Weil II (1.1.7), (1.1.14)
(blueprint: lem-trf-compact-frobenius-transport-composition).
Proof: the defining projection equation gives commutativity for r=1. Induction
and associativity give the equation for r; both horizontal arrows are isomorphisms,
so a commuting square with these horizontal maps is Cartesian. -/
theorem square (r : ℕ) : IsPullback ((D.geometricFrobenius X₀) ^ r).hom
    (D.geometricFiber X₀).hom (D.geometricFiber X₀).hom ((point D) ^ r).hom := by
  have h : (D.geometricFrobenius X₀).hom ≫ (D.geometricFiber X₀).hom =
      (D.geometricFiber X₀).hom ≫ (point D).hom := by
    exact (D.galoisMap_projections X₀.hom _).2
  apply IsPullback.of_horiz_isIso
  constructor
  induction r with
  | zero =>
    change (𝟙 _) ≫ (D.geometricFiber X₀).hom = (D.geometricFiber X₀).hom ≫ 𝟙 _
    simp
  | succ r ih =>
    simpa only [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc] using
      calc
        (D.geometricFrobenius X₀).hom ≫
            ((D.geometricFrobenius X₀) ^ r).hom ≫ (D.geometricFiber X₀).hom =
            (D.geometricFrobenius X₀).hom ≫
              (D.geometricFiber X₀).hom ≫ ((point D) ^ r).hom := by rw [ih]
        _ = (D.geometricFiber X₀).hom ≫ (point D).hom ≫ ((point D) ^ r).hom := by
          rw [← Category.assoc, h, Category.assoc]

private theorem isIso_of_comp_iso_eq_id {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) (e : Y ≅ X) (h : f ≫ e.hom = 𝟙 X) : IsIso f := by
  have hf : f = e.inv := (cancel_mono e.hom).1 (h.trans e.inv_hom_id.symm)
  rw [hf]
  infer_instance

omit [Finite A] in
private theorem insertion_isIso (r : ℕ)
    (L : FiniteRingCompactSupport.Category A (Spec (CommRingCat.of D.k))) :
    IsIso ((insertion A D r).app L) := by
  have h (F : Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of D.k)))
      (ModuleCat.{u + 1} A)) :
      IsIso ((globalSectionsToUpperStar (ModuleCat.{u + 1} A)
        ((point D) ^ r).hom).app F) := by
    exact isIso_of_comp_iso_eq_id _
      ((globalSectionsUpperStarIso (ModuleCat.{u + 1} A) ((point D) ^ r)).app F)
      (globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso
        (ModuleCat.{u + 1} A) ((point D) ^ r) F)
  have := Functor.isIso_mapDerivedCategoryNatTrans_app
    (globalSectionsToUpperStar (ModuleCat.{u + 1} A) ((point D) ^ r).hom) L (fun n ↦ h _)
  dsimp only [insertion, NatTrans.comp_app]
  infer_instance

include hsep in
/-- Direct Frobenius transport is invertible, including at exponent zero.
Source: the point-insertion identity and canonical finite-ring base change
(blueprint: lem-trf-compact-frobenius-transport-composition).
Proof: restriction along a point automorphism is inverse to the canonical invariance
of sections under its pullback. Exact localization preserves this isomorphism. The
constructible finite-Tor input has bounded-below etale origin, so finite-ring base
change makes the compact-support exchange invertible. Apply exact sections to that
exchange and compose the two isomorphisms. -/
theorem transport_isIso (c : Compactification (D.geometricFiber X₀).hom) (r : ℕ)
    (K : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left K) :
    IsIso (transport A D X₀ c r K hK) := by
  let : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom _))
  let : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom _))
  have := insertion_isIso A D r ((FiniteRingCompactSupport.support A c).obj K)
  have := ((FiniteRingCompactSupport.canonical_finite_ring_base_change A).2.2.2.2
    (square D X₀ r) c c c c K hK.plusEtaleOrigin
      (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK).plusEtaleOrigin).1
  dsimp only [transport]
  infer_instance

include hsep in
/-- Changes of computational compactification conjugate the actual transport maps.
Source: canonical finite-ring base change and naturality of point insertion
(blueprint: lem-trf-compact-frobenius-transport-composition).
Proof: the exchange compatibility square identifies pullback of the source comparison
followed by exchange for c with exchange for d followed by the target comparison.
Apply sections, and use naturality of the specified insertion to move the source
comparison across insertion. Cancel the target comparison against its inverse. -/
theorem transport_change (c d : Compactification (D.geometricFiber X₀).hom) (r : ℕ)
    (K : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left K) :
    transport A D X₀ d r K hK =
      (sections A D).map (FiniteRingCompactSupport.change A d c K hK.plusEtaleOrigin).hom ≫
        transport A D X₀ c r K hK ≫
        (sections A D).map (FiniteRingCompactSupport.change A d c
          ((pullback A D X₀ r).obj K)
          (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK).plusEtaleOrigin).inv := by
  let : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom _))
  let : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom _))
  have he := ((FiniteRingCompactSupport.canonical_finite_ring_base_change A).2.2.2.2
    (square D X₀ r) d c d c K hK.plusEtaleOrigin
      (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK).plusEtaleOrigin).2
  have hn := (insertion A D r).naturality
    (FiniteRingCompactSupport.change A d c K hK.plusEtaleOrigin).hom
  dsimp only [Functor.comp_map] at hn
  dsimp only [transport]
  rw [Category.assoc, ← Category.assoc ((sections A D).map _) ((insertion A D r).app _),
    hn, Category.assoc]
  simp only [← Functor.map_comp]
  rw [← Category.assoc, he]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

include hsep in
private theorem transport_recurrence
    (c : Compactification (D.geometricFiber X₀).hom) (m : ℕ)
    (K : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left K) :
    transport A D X₀ c (m + 1) K hK =
      transport A D X₀ c m K hK ≫
        transport A D X₀ c 1 ((pullback A D X₀ m).obj K)
          (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK) ≫
        (cohomology A D X₀ c).map ((compositor A D X₀ m).hom.app K) := by
  let : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom _))
  let : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom _))
  have hi := derivedPointRestriction_composition A _ (point D) m
    ((FiniteRingCompactSupport.support A c).obj K)
  have he := FiniteRingCompactSupport.finiteRingCompactExchange_power A
    (D.geometricFrobenius X₀) (point D) (square D X₀) c m K hK
  dsimp only [transport, cohomology, Functor.comp_map]
  change (derivedPointRestriction A _ (point D) (m + 1)).app _ ≫ _ = _
  rw [hi]
  simp only [Category.assoc]
  dsimp only [derivedPointCompositor]
  rw [← Functor.map_comp, he]
  simp only [Functor.map_comp]
  have hn := (insertion A D 1).naturality
    (FiniteRingCompactSupport.exchange A (square D X₀ m) c c K
      (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK).plusEtaleOrigin)
  dsimp only [Functor.comp_map, pointPullback] at hn
  change (insertion A D m).app _ ≫ (insertion A D 1).app _ ≫ _ = _
  rw [← Category.assoc ((insertion A D 1).app _) ((sections A D).map _)]
  erw [← hn]
  simp only [Category.assoc, compositor, pullback, pointPullback]
  rfl

include hsep in
/-- The direct transport is invertible, composes with its actual normalized
compositor, and is independent of every computational compactification.
Source: latest blueprint lem-trf-frobenius-operator-compact-description, power clause,
and released repair P1 (blueprint: lem-trf-compact-frobenius-transport-composition).

Proof: finite comparison identifies every ctf object with a bounded etale-origin
complex; ordinary pullback preserves constructibility and its finite Tor interval.
Nagata gives representatives, and square supplies the Cartesian power squares.
The finite torsion etale proper/open exchange pasting identity, transported through
site comparison, gives the exchange identity with the inverse derived compositor.
The sectionwise restriction-colimit-sheafification-tensor-unit calculus gives the
same power identity for insertion and its invertibility. Exact sections and
localization preserve these identities. Apply the categorical exchange-transport
composition lemma, obtaining the displayed recurrence. Induction on m therefore
identifies direct transport with m successive degree-one transports, with precisely
these compositors. Finally the canonical common-refinement comparison conjugates
the exchanged arrows; naturality of insertion cancels the comparison in the middle
and gives the final displayed conjugacy. The cocycle law for the comparisons makes
this a single canonical object independent of a chosen compactification. The Weil
isomorphism is retained as part of the specified domain; transport is geometric
and its construction does not use that isomorphism. -/
theorem compact_frobenius_transport_composition (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ D.p) (_hA : ∃ N : ℕ, 1 ≤ N ∧ (ell : A) ^ N = 0)
    (K : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left K)
    (_phi : (pullback A D X₀ 1).obj K ≅ K) :
    (∀ (c : Compactification (D.geometricFiber X₀).hom) (r : ℕ)
      (M : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
      (hM : ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left M), 1 ≤ r →
      IsIso (transport A D X₀ c r M hM)) ∧
    (∀ (c : Compactification (D.geometricFiber X₀).hom) (m : ℕ), 1 ≤ m →
      transport A D X₀ c (m + 1) K hK =
        transport A D X₀ c m K hK ≫
        transport A D X₀ c 1 ((pullback A D X₀ m).obj K)
          (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK) ≫
        (cohomology A D X₀ c).map ((compositor A D X₀ m).hom.app K)) ∧
    (∀ (c : Compactification (D.geometricFiber X₀).hom) (n : ℕ),
      transport A D X₀ c (n + 1) K hK = successive A D X₀ c K hK n) ∧
    (∀ (c d : Compactification (D.geometricFiber X₀).hom) (r : ℕ)
      (M : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
      (hM : ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left M), 1 ≤ r →
      transport A D X₀ d r M hM =
        (sections A D).map (FiniteRingCompactSupport.change A d c M hM.plusEtaleOrigin).hom ≫
        transport A D X₀ c r M hM ≫
        (sections A D).map (FiniteRingCompactSupport.change A d c
          ((pullback A D X₀ r).obj M)
          (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hM).plusEtaleOrigin).inv) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c r M hM _
    exact transport_isIso A D X₀ c r M hM
  · intro c m _
    exact transport_recurrence A D X₀ c m K hK
  · intro c n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [transport_recurrence A D X₀ c (n + 1) K hK, ih, successive]
  · intro c d r M hM _
    exact transport_change A D X₀ c d r M hM

end WeilConjectures.CompactFrobeniusTransport
