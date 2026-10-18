/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Sheaf.SixFunctors.ProperBaseChangeModules
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Proper direct image preserves finite Tor amplitude

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-tor.md`
(blueprint: det-ctf-finite-proper-tor); Stacks Project, Tags 0F0G and 0F12.

Membership in `Dctf` with a specified Tor interval is expressed by bounded
constructibility together with `hasTorAmplitudeIn` for that interval. This already
includes finite Tor amplitude, both in the hypothesis and in the conclusion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Proper direct image preserves bounded constructible complexes of finite Tor amplitude,
with upper Tor bound increased by a bound for the geometric fibres' ℓ-cohomological dimensions.
Source: blueprint `sec-six-functors-basics/sk-prop-ctf-finite-proper/`
`sk-prop-ctf-finite-proper-tor.md` (blueprint: det-ctf-finite-proper-tor).

Proof plan:
1. The coefficient convention holds for N = ℓ^r on both schemes because p ≠ ℓ.
   Apply lem-fin-proper-bounded-constructible to obtain bounded constructibility of Rp_*C.
2. For any A-module N, inverse image of its constant sheaf is exact
   (prop-weil-pbc-inverse-image-modules-exact). The input Tor interval bounds
   C ⊗ᴸ p⁻¹N_Y. The proper projection formula
   (lem-etale-proper-projection-formula-finite, Stacks 0F0G) identifies its direct image
   with Rp_*C ⊗ᴸ N_Y, without finiteness or flatness assumptions on N.
3. Apply det-properbasechange-modules to this bounded-below complex at each geometric
   point. Exact inverse image preserves its interval. The exact geometric-point section
   equivalence identifies the stalk with derived global sections of the fibre complex
   (lem-weil-pbc-geometric-point-pullback-stalk). Choose a bounded-below K-injective
   representative using lem-weil-pbc-module-sheaves-enough-injectives and
   lem-weil-pbc-dplus-injective-representative to compute this identification.
4. Module sheaves are Grothendieck abelian and direct image is additive and left exact
   (lem-weil-pbc-module-sheaves-grothendieck-abelian,
   lem-weil-pbc-module-direct-image-left-exact). Apply thm-sp-truncation-e2 to the fibre
   complex. Its E₂ page is H^s(X_y, H^t(E)); underlying module cohomology agrees with
   abelian cohomology by lem-weil-pbc-etale-module-cohomology-forget. Since ℓ^r kills
   these sheaves, the fibre bound and the input interval confine E₂ to
   0 ≤ s ≤ d, a ≤ t ≤ b. Subsequent pages vanish outside that rectangle. For a total
   degree outside [a,b+d], every graded piece of the finite exhaustive separated
   abutment filtration vanishes. Successively identifying adjacent filtration steps,
   from the zero end to the exhaustive end, makes the abutment zero.
5. For an arbitrary module sheaf M on Y and a geometric point y, use
   lem-sfb-etale-derived-tensor-stalk to identify the stalk of Rp_*C ⊗ᴸ M with
   (Rp_*C)_y ⊗ᴸ M_y. Take N = M_y; lem-weil-pbc-constant-sheaf-geometric-stalk
   identifies N with (N_Y)_y. Steps 3-4 give the required vanishing. Exact pullback and
   lem-weil-pbc-exact-functor-complex-cohomology identify these with stalks of the
   cohomology sheaves. Geometric-stalk conservativity
   (lemma-weil-pbc-geometric-stalk-conservative) makes those sheaves zero. This is
   def-kun-tor-amplitude for the output interval. -/
theorem isBoundedConstructible_hasTorAmplitudeIn_rightDerivedLowerStar_of_proper
    (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ℓ ^ r : ℕ) • (1 : A) = 0)
    (d : ℕ)
    (hd : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
      (F : Sheaf (pullback f y).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (U : (pullback f y).Etale) (s : F.obj.obj (op U)),
        ∃ n : ℕ, (ℓ ^ n) • s = 0) →
      ∀ i : ℤ, (d : ℤ) < i →
        IsZero ((cohomology AddCommGrpCat.{u + 1} (pullback f y) i).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
    (a b : ℤ) (hab : a ≤ b) (C : DerivedCategoryModule A X)
    (hC : DerivedCategory.isBoundedConstructible A X C)
    (hCab : DerivedCategory.hasTorAmplitudeIn A X a b C) :
    DerivedCategory.isBoundedConstructible A Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj C) ∧
    DerivedCategory.hasTorAmplitudeIn A Y a (b + (d : ℤ))
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj C) := by
  sorry

end AlgebraicGeometry.Etale
