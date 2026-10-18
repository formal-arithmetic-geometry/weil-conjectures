/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ModuleObjects
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The window isomorphisms for proper direct image

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-proper-unbounded-window/sk-lem-proper-unbounded-window-iso.md
(blueprint: det-proper-unbounded-window-iso).

The two canonical arrows are asserted to be isomorphisms in the ambient module category.
All three objects are also asserted to be ind-constructible. Since IndCons is full, this
is exactly the assertion that these arrows are isomorphisms in IndCons.

The dimension bound uses all nonnegative integers below the extended Krull dimension.
It expresses dim <= d for an integer d, including negative d and empty geometric fibres,
without converting d to a natural number and thereby losing the empty-fibre case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical degree-q window maps for a finite subextension of the chosen algebraic closure.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window-iso, both displayed maps
(blueprint: det-proper-unbounded-window-iso).

Proof:
1. On the small pro-etale sites, lem-weil-pbc-ring-sheaves-grothendieck and
lem-sfb-grothendieck-k-injective give K-injective resolutions. The functor
CondensedRing.lowerStar is additive (def-sfb-module-lower-star), so its total right
 derived functor is triangulated by lem-pc-right-derived-functor-triangulated.
2. Set A = tau_le_q K and B = tau_ge_(q+1) K. Their cohomology is that of K in
 the retained ranges and zero elsewhere (def-kun-truncations), so both lie in Dic.
Apply the derived pushforward to A -> K -> B -> A[1], the canonical triangle of
lem-sf-derived-truncation-triangle. By the lower bound of
det-proper-unbounded-window-arbitrary, H^(q-1)(Rp_*B) and H^q(Rp_*B) vanish.
The cohomology sequence of lem-sf-derived-homology-long-exact gives
0 -> H^q(Rp_*A) -> H^q(Rp_*K) -> 0, so the first canonical map is an isomorphism.
3. Put r = q-2d-2, L = tau_le_r A and W = tau_ge_(r+1) A. They lie in Dic by
 the same truncation formulas. Apply Rp_* to L -> A -> W -> L[1]. The upper bound
of det-proper-unbounded-window-arbitrary puts Rp_*L in degrees <= r+2d+1 = q-1.
Thus H^q(Rp_*L) and H^(q+1)(Rp_*L) vanish. The same cohomology sequence gives
0 -> H^q(Rp_*A) -> H^q(Rp_*W) -> 0. This is the second displayed canonical map,
with W = tau_ge_(q-2d-1) tau_le_q K. The same amplitude theorem puts the direct
images of K, A and W in Dic, giving all three IndCons membership assertions.
Fullness puts the ambient inverses in IndCons as well. -/
theorem proper_unbounded_window_iso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K)))) := by
  sorry

/-- The canonical degree-q window maps for the condensed algebraic closure.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window-iso, both displayed maps
(blueprint: det-proper-unbounded-window-iso).

Proof:
1. On the small pro-etale sites, lem-weil-pbc-ring-sheaves-grothendieck and
lem-sfb-grothendieck-k-injective give K-injective resolutions. The functor
CondensedRing.lowerStar is additive (def-sfb-module-lower-star), so its total right
 derived functor is triangulated by lem-pc-right-derived-functor-triangulated.
2. Set A = tau_le_q K and B = tau_ge_(q+1) K. Their cohomology is that of K in
 the retained ranges and zero elsewhere (def-kun-truncations), so both lie in Dic.
Apply the derived pushforward to A -> K -> B -> A[1], the canonical triangle of
lem-sf-derived-truncation-triangle. By the lower bound of
det-proper-unbounded-window-arbitrary, H^(q-1)(Rp_*B) and H^q(Rp_*B) vanish.
The cohomology sequence of lem-sf-derived-homology-long-exact gives
0 -> H^q(Rp_*A) -> H^q(Rp_*K) -> 0, so the first canonical map is an isomorphism.
3. Put r = q-2d-2, L = tau_le_r A and W = tau_ge_(r+1) A. They lie in Dic by
 the same truncation formulas. Apply Rp_* to L -> A -> W -> L[1]. The upper bound
of det-proper-unbounded-window-arbitrary puts Rp_*L in degrees <= r+2d+1 = q-1.
Thus H^q(Rp_*L) and H^(q+1)(Rp_*L) vanish. The same cohomology sequence gives
0 -> H^q(Rp_*A) -> H^q(Rp_*W) -> 0. This is the second displayed canonical map,
with W = tau_ge_(q-2d-1) tau_le_q K. The same amplitude theorem puts the direct
images of K, A and W in Dic, giving all three IndCons membership assertions.
Fullness puts the ambient inverses in IndCons as well. -/
theorem proper_unbounded_window_iso_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        ↥(pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y)) → (n : ℤ) ≤ d)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)) (q : ℤ) :
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj K)) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncLE q).obj K))) ∧
    ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)).obj
            ((DerivedCategory.TStructure.t.truncLE q).obj K)))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K)))) := by
  sorry

end AlgebraicGeometry.ProEtale
