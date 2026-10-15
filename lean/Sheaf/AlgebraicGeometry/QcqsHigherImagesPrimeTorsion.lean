/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.GeometricStalkColimits
import Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Qcqs higher direct images preserve a fixed set of torsion primes

Source: Stacks Project, Tags 0DDD (1) and 0DDC (1), fixed-prime refinement
(blueprint: lem-sbc-qcqs-higher-images-prime-torsion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Higher direct images along a quasi-compact quasi-separated scheme morphism preserve
stalkwise torsion whose annihilators have prime divisors in a fixed set `P`.
Only prime members of `P : Set ℕ` are tested, so this encodes an arbitrary set of primes.
Source: Stacks Project, Tags 0DDD (1) and 0DDC (1), fixed-prime refinement.
(blueprint: lem-sbc-qcqs-higher-images-prime-torsion)

Proof:
1. Take an affine pointed etale neighbourhood W of the target geometric point. The scheme Z = U
×_V W is qcqs by lem-weil-pbc-qcqs-morphism-permanence and lem-weil-pbc-qcqs-over-affine. Its
pulled-back sheaf G has the same allowed-prime stalk torsion by lemma-openclosed-stalk-upperstar.
No global qcqs condition on U or V is needed.

2. Order the positive integers with prime divisors in P by divisibility. This is a nonempty
directed set (1 is an index and nm bounds n and m). Form G[n] = ker(n : G → G) using
def-pur-abelian-sheaf-kernel. Divisibility gives inclusions and a cocone to G. The colimit C
exists by lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact; the indices form a subset of
the natural numbers.

3. The map C → G is an isomorphism on stalks: prop-weil-pbc-geometric-stalks-exact identifies
stalks of G[n] with kernels and lem-kun-stalks-commute-colimits identifies stalks of C with their
colimit. The hypothesis supplies surjectivity. Represent a colimit element by a kernel element
using lem-weil-pbc-filtered-colimit-modules-elementwise over the integers; if it maps to zero,
the representative is zero by the subgroup inclusion. Thus the stalk map is bijective. Apply
lemma-weil-pbc-geometric-stalk-conservative to conclude that G is the colimit of G[n] with the
actual inclusion maps.

4. Apply lem-weil-pbc-etale-directed-cohomology-colimit on Z to this directed diagram. Every
cohomology class of G comes from H^q(Z, G[n]) for some allowed n, by
lem-weil-pbc-filtered-colimit-modules-elementwise over the integers. There is no uniform
annihilator assumption.

5. Sectionwise kernels give n id of G[n] equal to zero. Cohomology is the right derived sections
functor by def-weil-pbc-sites-and-cohomology, and its degree functors are additive by
lem-weil-pbc-right-derived-universal-delta-functor. Hence n kills H^q(Z, G[n]); the
inclusion-induced group homomorphism shows that n kills the represented class in H^q(Z, G).

6. Use sbc-lem-higher-direct-image-presheaf and lem-weil-pbc-sheafification-geometric-stalk to
express the target stalk as the filtered colimit of cohomology over pointed etale neighbourhoods.
The index is filtered by lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered. Use
lem-weil-pbc-filtered-colimit-modules-elementwise to represent the chosen stalk element on a
neighbourhood; lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink refines it to an affine one
without changing the stalk class. Work in a common universe, or a small equivalent index
category.

7. Apply steps 1–5 to this affine representative. The map to the stalk is a group homomorphism,
so its positive allowed-prime annihilator also kills the original stalk element. This works for
every nonnegative degree and every target geometric point. -/
theorem qcqs_higherDirectImages_prime_torsion
    {U V : Scheme.{u}} (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f]
    (P : Set ℕ) (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U)
      (x : (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P)
    (q : ℕ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ V)
    (y : (((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))))) :
    ∃ m : ℕ, 0 < m ∧ m • y = 0 ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ∈ P := by
  sorry

end AlgebraicGeometry.Etale
