/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.ArtinSchreierSequence
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherent
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Sheaf.AlgebraicGeometry.EtaleZariskiCohomology
import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.Paper.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.LinearAlgebra.SemilinearFrobenius
import Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift

/-!
# Artin–Schreier vanishing on a smooth connected curve

Source: blueprint, `sec-curve-estimates/sk-prop-cd/lem-sc-artin-schreier-dimension`;
Stacks Project, Tag 0A3N, dimension one (blueprint: lem-sc-artin-schreier-dimension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: blueprint `sec-curve-estimates/sk-prop-cd/lem-sc-artin-schreier-dimension`;
Stacks Project, Tag 0A3N (blueprint: lem-sc-artin-schreier-dimension).
For a smooth separated connected curve over an algebraically closed field of positive
characteristic `p`, the constant étale sheaf `ℤ/p` has zero cohomology in degrees above one.

Proof: The Artin–Schreier short exact sequence `0 → ℤ/p → G_a → G_a → 0`
(lem-sc-as-sequence) gives the long exact sequence for derived global sections, by
lem-weil-pbc-abelian-etale-sheaves-grothendieck, lem-sp-grothendieck-enough-injectives,
lem-sp-kinjective-computes and lem-weil-pbc-right-derived-universal-delta-functor.
By lem-sc-ga-cohomology, the cohomology of `G_a` vanishes in degrees at least two.
Thus degrees at least three vanish, and degree two is the cokernel of `F - 1` on
`H¹(C, G_a)`. Compactification (lem-sc-compactification) and lem-sc-affine-open-proper
show that the curve is either proper or affine. In the affine case,
lem-sc-etale-affine-qcoherent makes `H¹(C, G_a)` zero, so its cokernel is zero.
In the proper case, multiplication by field elements on `G_a` induces a vector-space
structure on `H¹(C, G_a)`, since cohomology is additive. Frobenius induces a `p`-linear
endomorphism, and the Artin–Schreier map induces this endomorphism minus the identity.
The structure sheaf is coherent, and lem-pc-coherent-hi and pqf-def-cohomology give
finite-dimensional Zariski `H¹(C, O_C)`. The comparison of
lem-sc-etale-zariski-qcoh-comparison is natural in multiplication by scalars, so identifies
it linearly with `H¹(C, G_a)`. Finally lem-sc-lang-steinberg makes `F - 1` surjective,
so the degree-two cokernel vanishes as well. -/
theorem isZero_etaleCohomology_constantZMod_of_one_lt_of_charP
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj
      ((DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        (C.constantZMod p))) := by
  sorry

end AlgebraicGeometry
