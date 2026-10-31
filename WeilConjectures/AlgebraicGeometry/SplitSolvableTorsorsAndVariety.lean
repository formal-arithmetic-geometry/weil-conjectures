/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Semisimple
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.MvPolynomial.Basic

import WeilConjectures.AlgebraicGeometry.AffineSpaceInvertibleTrivial
import WeilConjectures.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import WeilConjectures.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Split solvable torsors and the underlying variety

Source: Milne, Algebraic Groups (2017), Proposition 16.55(c), Corollaries 16.53
and 16.56, and Appendix A.79.
(blueprint: lem-sfb-split-solvable-torsors-and-variety)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Torsors under a split solvable group are Zariski locally trivial; its variety
is an affine space times a split torus, and its Picard group remains trivial after
every field extension. Over an algebraically closed field every smooth connected
affine solvable group is split. The last assertion does not assume splitness.

Source: Milne, Proposition 16.55(c), Corollaries 16.53 and 16.56, Appendix A.79.
(blueprint: lem-sfb-split-solvable-torsors-and-variety).

Proof:
1. For G_a, additive affine torsor descent gives a section on every affine open
(`lem-sfb-additive-affine-torsor-section`). For G_m, the rank-one case of
`lem-sfb-split-torus-torsor-frame-geometry` identifies torsors with frames of
invertible modules. A local basis is a section. Translation by a section gives
an equivariant trivialization, whose inverse is furnished by the torsor square.
2. Induct on the supplied split series, simultaneously proving local triviality
and existence of a global section over an affine scheme with trivial Picard group.
At length zero the torsor diagonal is an isomorphism. Its projection is a flat
locally finitely presented monomorphism, hence an open immersion by
`lem-pe-flat-lfp-monomorphism-open`, and surjectivity makes it an isomorphism.
For positive length, `lem-sfb-affine-normal-quotient-geometry` makes H/H_1 a
represented fppf quotient G_a or G_m. Apply
`lem-sfb-normal-extension-torsor-reduction`: P/H_1 is a torsor for this quotient.
Choose its sections locally by step 1 and lift them through the H_1-torsors by
induction. Over an affine Picard-trivial base both choices can be global.
3. Affine space over any field is Noetherian by
`lem-weil-pbc-finite-type-over-noetherian` and `pqf-def-locnoeth`. Its coordinate
ring is factorial by `lem-sfb-polynomial-field-ufd`, and its stalks are factorial
by `lem-weil-pbc-affine-open-stalk-localization` and
`lem-sfb-ufd-prime-localizations`. By
`lem-sfb-invertible-extension-factorial-complement`, an invertible module on any
open extends to affine space. The extension is trivial by
`lem-sfb-affine-space-invertible-trivial`. In particular G_a and G_m are affine
and Picard-trivial. This includes dimension zero and the empty open.
4. Induct again on the series. The quotient H/H_1 is G_a or G_m and has trivial
Picard group by step 3. The global assertion of step 2 trivializes its H_1-torsor
H, giving H isomorphic as a scheme to (H/H_1) times H_1. Append an affine-line
or multiplicative-group factor to the inductive product. The length-zero product
has both dimensions zero. No group homomorphism splitting is asserted.
5. Base change the scheme isomorphism to every K/k. The product is the principal
open D(t_(r+1)...t_(r+s)) of affine (r+s)-space over K; when s=0 the product is 1.
Apply step 3 over K, then transport the invertible module across this isomorphism.
6. Over an algebraically closed, hence perfect, field the derived subgroups are
smooth connected normal groups by `lem-sfb-smooth-connected-derived-subgroup`.
Their commutators factor through the next subgroup, so represented quotients are
commutative. Apply `lem-sfb-perfect-solvable-unipotent-torus` to obtain U with
split torus quotient. Pull back the coordinate torus series by
`lem-sfb-affine-normal-quotient-geometry` and append the additive series of U from
`lem-sfb-perfect-unipotent-additive-series`. This includes torus rank zero and U=1.
-/
theorem split_solvable_torsors_and_variety {k : Type u} [Field k]
    (H : Grp (Over (Spec (.of k))))
    [IsAffine H.X.left] [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] :
    (IsSplitSolvable H →
      (∀ (S : Over (Spec (.of k))) (P : RepresentedRightTorsor H S),
        P.IsZariskiLocallyTrivial) ∧
      (∃ r s : ℕ, Nonempty (H.X ≅
        StandardGroupSchemes.affine k (MvPolynomial (Fin r) k) ⊗
          (MultiplicativeType.splitTorus k s).X)) ∧
      (∀ (K : Type u) [Field K] [Algebra k K]
        (L : ((MultiplicativeType.baseChange (k := k) (K := K)).obj H).X.left.Modules),
        L.IsInvertible → Nonempty (L ≅ SheafOfModules.unit _))) ∧
    (IsAlgClosed k → IsSolvableGroupScheme H.X → IsSplitSolvable H) := by
  sorry

end AlgebraicGeometry
