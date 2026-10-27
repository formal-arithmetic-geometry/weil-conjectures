## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSelfExchangeForgetSupports` states
`AlgebraicGeometry.Etale.proper_self_exchange_forget_supports` with one postponed proof.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The node is otherwise unchanged. The source read is the current blueprint's
`sec-six-functors-basics/sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md`,
especially the first triangle's common-pullback-counit paragraph and final paragraph
specifying the canonical exchanges. All six DAG proof steps are reproduced in the
Lean docstring, including open-unit transposition and chosen-refinement normalization.

Hypotheses and clauses:

- A finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  This is the coefficient universe of the recorded ordinary module derived categories.
- Arbitrary schemes and proper f: `{X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]`.
  There is no Noetherian, finite-type-base, nonempty-base, trace, or invertible-exponent
  assumption. No extra compactification hypothesis is introduced; properness supplies it.
- Every unbounded K: `(K : DerivedCategoryModule A X)`, the ordinary derived category
  of `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`, with no boundedness predicate.
- U is the library pullback of f with itself; p and v are respectively
  `pullback.fst f f` and `pullback.snd f f`. All occurrences have this order.
- F is `ordinaryFinitePullback A`, the recorded left-derived inverse image. The
  compact-support beta is `(SfDiagonalKernel.exchangeFirst A f).hom.app K`, whose
  definition is the actual `rightDerivedLowerShriekBaseChangeMap` at the flipped
  `IsPullback.of_hasPullback f f`, promoted by `asIso`.
- c_f and c_p are the actual
  `rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat A) ...` hom components.
  The latter is evaluated at `(ordinaryFinitePullback A (pullback.snd f f)).obj K`.
- E_f is `(CoordinateTrace.exchange1 A f K).hom`. Its definition is `asIso` of the
  component of `derivedBaseChangeMap (ModuleCat A)` at the same flipped square;
  its invertibility uses the recorded torsion-ring proper-base-change theorem and
  `isAddTorsion_of_finite`. This is the left-derived presentation of the ordinary
  exact-inverse-image mate, explicitly allowed by `def-kun-unbounded-exchange`'s
  lean.note and by the `EtaleCoordinateTraceData` module documentation. The
  comparison is `leftDerivedUpperStarIsoMapDerivedCategory`; no arbitrary arrow
  or isomorphism is substituted.
- The first conjunct is precisely beta;c_p = F(c_f);E_f, with `≫` in application order.
- The second conjunct is precisely beta inverse;F(c_f) = c_p;E_f inverse, using
  `exchangeFirst.inv.app K` and `CoordinateTrace.exchange1.inv`. Both equations
  are included, rather than retaining just the invertibility of their endpoints.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`:
  `AlgebraicGeometry.Etale.ordinaryFinitePullback`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`;
  its body is the chosen open forget-supports comparison, direct-image compositor,
  then the compactification's equality with f.
- `Sheaf.AlgebraicGeometry.SfSupportedDiagonalData`:
  `AlgebraicGeometry.Etale.SfDiagonalKernel.exchangeFirst`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso` and
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`, read to check that the
  ordinary mate is the one prescribed by the node. The statement uses its canonical
  left-derived presentation through the existing `CoordinateTrace.exchange1`.
- `Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData` (publicly imported by the
  supported diagonal module): `AlgebraicGeometry.Etale.CoordinateTrace.exchange1`,
  whose actual definition uses the proper-base-change theorem recorded at
  `lem-kun-proper-base-change-torsion-ring`. The recorded `ProperUnboundedBaseChange`
  module is explicitly imported; the public theorem is also available upstream in
  `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`.
- All already recorded proof-dependency modules are plain imports, including
  `CompositionAdjunctionNormalization`, `FiniteDirectImageComposition`,
  `DerivedPullbackCompositionMonoidal`, the module inverse-image declarations,
  open-unit base change, and Mathlib's `Adjunction.Mates` and proper base change.
  `lem-sf-proper-refinement-forget-supports` has no Lean record at the time of reading;
  it is a proof dependency only, so there is no module to import yet.

Edge cases checked before writing: zero ring (no Nontrivial assumption), zero complex,
empty X, empty S, identity f, and arbitrary unbounded complexes. Properness of the first
projection follows from base change; the empty cases do not require selecting points.
For identity f the equations are the canonical mate/unit comparisons; none of the
formulas relies on a dimension, trace, nonzero coefficient, or boundedness choice.
The common `u` is the library's scheme universe, with coefficient carrier and module
universe `u+1`, preserving the small-etale categories used by the dependencies.

Searches actually run:

- `msearch.py ... leanfinder "Proper self-product compact support exchange commutes
  with canonical forget supports isomorphisms in unbounded derived etale module
  sheaves"`: eight unrelated hits, including sheaf free-presentation and topological
  section comparisons; no match.
- `msearch.py ... loogle '"baseChange", "counit"'`: zero hits.
- `msearch.py ... grep 'forget.*[Ss]upport|[Bb]ase[Cc]hange.*counit'`: one Mathlib
  hit, `LinearAlgebra/Finsupp/Pi.lean:79`, unrelated forgetting finite support.
- `rg` in `lean/WeilConjectures` for the exact node id: no occurrence.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for exchangeFirst,
  exactDerivedBaseChangeMap, forget supports, and base-change/toLowerStar found
  the recorded definitions, `exchangeCompatible` in `LowerShriekLowerStarWeil`,
  and the compactification-level compatibility in `CompactificationLowerStarBaseChange`.
  The former is for endomorphism squares with the same proper vertical map on both
  sides, so cannot specialize to f versus p in the self-product square. The latter
  is at specified input/output compactifications, before the actual chosen-output
  comparison, and does not state the item. Existing projective-line trace transport
  statements impose a projective-line chart and concern specified traces, rather
  than this assertion for every proper f and every K.
- `rg` in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`
  for the proposed declaration name: no existing declaration.

No statement dispute or source defect was found.

## Second reading by NB

A separate pass compared the finished signature to the node, with both texts open:
finite commutative A, arbitrary X and S, proper f, and every unbounded K are bound.
The first coordinate is fst and the top horizontal edge is snd in both conjuncts.
The first conjunct has source F_f R_f! K, the second has source R_p! F_v K;
both targets are R_p F_v K and F_f R_f K respectively. The actual chosen proper
comparisons occur at exactly those components. The inverse ordinary exchange is
that of the existing canonical `asIso`, not a free isomorphism parameter. No
mismatch or silent additional hypothesis was found. This is the worker's own
rereading; the dispatch brief prohibits starting another agent, and the maintainer's
independent review remains the independent reading of the delivery.
