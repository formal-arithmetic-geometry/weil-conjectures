/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-! # A finite affine section cover in one positive tensor power

Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph;
Properties, Definition 01PS.
(blueprint: lem-weil-pbc-ample-finite-common-power-cover).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Ampleness gives finitely many affine section loci in one positive tensor power.

Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph;
Properties, Definition 01PS.
(blueprint: lem-weil-pbc-ample-finite-common-power-cover).

Proof:
1. Choose an affine nonvanishing locus of a positive-degree section through each point,
   using absolute ampleness. Quasi-compactness gives a finite subcover.
2. Take the product m of their positive degrees. Raise each section to the quotient
   m / n of degrees, and transport it by the tensor-power exponent isomorphism.
   Locally in a rank-one trivialization, its coefficient is raised to a positive power;
   a coefficient is a unit exactly when that positive power is a unit. Thus the loci
   remain unchanged and affine, and they still cover.
3. A global section corresponds to a morphism from the structure module by evaluation
   at one. For an invertible module its nonvanishing germ locus equals the complement
   of the support of its zero locus: in a rank-one stalk both say the coefficient is a
   unit. Use this identification to express the cover in the source library's convention.
4. Enumerate the finite nonempty family by ULift (Fin (r + 1)). If the scheme is empty,
   instead use degree one and a single zero section; its locus is the empty affine open,
   which is also the top open of the empty scheme. This handles the empty subcover. -/
theorem IsAmple.exists_finite_common_power_cover (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible] (hL : IsAmple X L) :
    ∃ (m : ℕ) (_ : 0 < m) (r : ℕ)
      (s : ULift.{u} (Fin (r + 1)) → (𝟙_ X.Modules ⟶ L.tensorPow m)),
      (∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl) ∧
      (⨆ i, (Hom.zeroLocus (s i)).support.compl) = ⊤ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
