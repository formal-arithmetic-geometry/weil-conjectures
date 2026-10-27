## Worker report

The item is stated by `AlgebraicGeometry.exists_rigRegularFormalResolutionRule` in
`Sheaf.AlgebraicGeometry.RigRegularFormalResolution`. Its only proof is `sorry`.
The statement of the item, its proof plan, and its proof dependencies are unchanged.
Two definition nodes supply the missing arbitrary-formal-pair and ordered-tower
interfaces. No global algebraization of the input is required. All writes are in
this sandbox; all compiles use the prescribed scompile.py wrapper.

Clause-by-clause rendering:

* A Noetherian adic formal scheme is `NoetherianAdicFormalScheme.space` with
  `noetherian : IsNoetherianAdicFormalScheme space`. This is the landed Q47 finite
  cover by complete Noetherian formal affine opens. `ideal`, `coherent`, and
  `idealDefinition` add a distinguished coherent ideal and formal charts identifying
  its actual stalk extension with the chart ideal. The ringed-space completion and
  formal spectrum are the landed Q13 constructions, never sorry data.
* The domain is all `RigRegularFormalInput.{u}`. `rational` expresses being over Q;
  the lift of Q fixes size and no separation/dimension assumption is made.
  `reduced` and `quasiExcellent` are the Q47 predicates on every formal affine
  ring. `invertible` is local generation of the distinguished ideal by a
  non-zero-divisor. These are properties, not chosen coefficient fields.
* `varieties` gives a finite disjoint open cover by components. Their reduced
  closed fibres have actual quotient stalks (surjective with radical kernel),
  homeomorphic underlying spaces, and finite-type structure maps to spectra of
  characteristic-zero fields. Those fields may differ. No chosen field is bound
  in `compatible`.
* `rigRegular` is `exists n > 0, c.ideal ^ n <= absoluteSingularIdeal c.ring`
  on each complete chart. The singular ideal reuses the landed Q13 absolute
  nonregular ideal. `singularLocus` uses the nonregular ordinary local rings at
  the corresponding open primes, so it is the support of this radical ideal.
* `IsRegularFormalMap h` is equality of actual extended distinguished stalk
  ideals, locality of all stalk homomorphisms, and Q47's
  `IsRegularOnAdicFormalAffines h`. The latter uses the actual section map on
  every pair of formal affine opens, with `RingHom.IsRegular`, the recorded
  flat/geometrically-regular-fibre predicate. Finite purely inseparable tests in
  that predicate are equivalent to all finite field-extension tests.
* `RigRegularFormalResolutionRule.tower` is one simultaneous assignment to every
  input, and `FormalBlowupTower.length` is finite. `center` records the actual
  ideal at every stage. `blowup` requires completed ordinary blowup charts with
  a cartesian restriction square, the correct map to Spec(B), and the extended
  distinguished ideal; it uses the recorded `IdealSheafData.blowup`.
* `resolves` says each center is coherent, open, regular and nonempty, and its
  image under the actual composite `toBase` lies in the ORIGINAL input singular
  locus. The terminal complete formal affine rings are regular. A regular
  center is checked by the ordinary regular quotient scheme on formal affine
  charts; the ideal contains a power of the chart ideal, so no points away
  from the formal locus are silently tested.
* `compatible` requires a `FormalResolutionComparison` for EVERY regular map of
  input pairs. `cartesian` tests the genuine formal pullback universal property
  against Noetherian formal pairs with local ideal-preserving maps. An ordinary
  ringed-space pullback is used only to restrict a blowup to an OPEN target
  chart, where it is the correct restriction. No arbitrary map is substituted
  for a canonical construction.
* `retainedStage` is an order embedding; `count_before`, `count_after`,
  `deleted_level`, `count_zero` and `count_last` synchronize all original
  and contracted levels. `retained_ideal` equates the actual extended ideals,
  including equality transport between identified levels.
  `deleted_iff_unit` deletes EXACTLY stages whose extended ideals are unit at
  every point. It therefore retains all nonempty isomorphic blowups.
* `empty` asserts length zero for every empty input. There is no comparison
  between different distinguished ideals.

Dependencies read and used:

* `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, `IsExcellent`;
  `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular` and its geometric
  regularity predicate (the original dependency records are used).
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, with Mathlib's
  `IsRegularRing` and `IsRegularLocalRing` for the ring clauses.
* `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`;
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the coherence interface;
  `WeilConjectures.Compactification.FiniteTypeExtension`: `ofFiniteType` for
  ordinary center ideals. Local finite generation of stalk ideals is coherence
  on a Noetherian formal scheme and does not create another module category.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`, precisely the recorded finite-type conjunction.
* Parallel landings, read in full before finalizing: `AdicFormalCompletion.space`,
  `.toScheme`, `.formalSpectrum`, `.ringedSpaceFunctor` from
  `Sheaf.AlgebraicGeometry.AdicFormalCompletion`; `absoluteSingularIdeal` from
  `Sheaf.AlgebraicGeometry.FormalCompletionGeometry`; and
  `IsNoetherianAdicFormalScheme`, `IsReducedAdicFormalScheme`,
  `IsQuasiExcellentAdicFormalScheme`, `IsRegularOnAdicFormalAffines` from
  `Sheaf.AlgebraicGeometry.AdicFormalGeometry`. Their nodes are added to the
  item's statement dependencies. Initial private completion definitions were
  removed when these landings became visible.

All six already stated ring-theoretic proof dependencies are plain imports of
the theorem module: FieldsExcellent, IsExcellentFiniteTypeLocalization,
AdicCompletionNoetherian, FlatUnderRegular, GRingCompletionRegular and
RegularMapAscent. The four formal proof dependencies
lem-per-rig-variety-strong-resolution, lem-per-rig-principal-formal-algebraization,
lem-per-rig-formal-resolution-intrinsic and lem-per-rig-formal-resolution-gluing
have no recorded Lean declarations yet, so there are no proof imports for them.
Their complete six-step assembly plan is in the theorem docstring.

Edge cases checked before finalization: empty formal space and empty component
cover; regular formal disc (no centers); a unit ideal and its empty center;
a nonempty Cartier center inducing an isomorphism (retained); pullback missing
some or all centers; different coefficient fields; a formal map without an
algebraized lift; locally principal but not globally principal distinguished
ideal; non-reduced closed fibre for a reduced formal scheme (only its REDUCED
closed fibre is required finite type); arbitrary fixed universe u. The complete
chart condition excludes no local formal objects and no scheme separation
hypothesis was added. No statement correction or dispute is needed.

Searches: msearch.py LeanFinder queried functorial desingularization of
rig-regular locally principal Noetherian formal schemes, returning normalization
and ordinary smoothness, no match. Loogle queried FormalScheme, Spf and
AdicCompletion, returning unknown FormalScheme; the later FormalBlowupTower query
also had no hit. Mathlib grep for FormalScheme/formal scheme/formal blowup had no
hit. LeanSearch for the formal spectrum/completed-sheaf phrase returned ordinary
Spec and IsAdicComplete results. A separate LeanFinder ordered-tower/contraction
query returned ordinary affine-limit/valuative criteria. Exact outputs are in
the new nodes' mathlib_searches. Project rg and DAG scans located the concurrent
Q13 and Q47 landings and the ordinary tower of def-trf-ordinary-resolution-rule;
the first two are reused and the third has different (ordinary) objects.
`blueprint_refs.py ancestor` gave lem-per-artin-gabber-affine-curve;
`blueprint_refs.py search` was also used. The upstream node-id search had no hit.

Source checked directly: Temkin arXiv:0904.1592v2, §§2.2–2.4, 3.1.1–3.1.5,
3.4.1; the PDF at the node's recorded URL and its current arXiv HTML. The latest
blueprint ancestor proof was also read; this item is an auxiliary source theorem,
not the blueprint unit statement.

## New nodes

`def-per-rig-regular-formal-pair-geometry` owns
`Sheaf.AlgebraicGeometry.RigRegularFormalGeometry`. It adds formal stalk ideals,
the distinguished-ideal pair, rig-regular input predicate, regular pair maps,
formal blowups, and regular-center predicate. It reuses all three landed formal
geometry nodes listed above. Their completion-specific predicates cannot state
this theorem on arbitrary formal schemes without assuming a global
algebraization. Its source is Temkin §§2.4 and 3.1. All definitions have actual
data and there is no theorem or sorry in this module.

`def-per-formal-resolution-rule` owns
`Sheaf.AlgebraicGeometry.FormalResolutionRule`. It defines finite formal towers,
strongness over the original singular locus, genuine formal cartesian comparison,
exact empty-center contraction, and the one resolution rule. Temkin §§2.2.2–2.2.5,
2.3.3–2.3.4 and 2.4.8–2.4.12 specify these notions. The existing ordinary tower
and comparison cannot be substituted for formal levels. The new node searches
record no formal counterpart. This module also contains no theorem or sorry.

## Second reading by Q87

A separate pass reread the item and every definition/signature after the first
clean compile. It caught the new Q13 and Q47 landings: removed the private
completion/Spf/singular-ideal constructions, imported their modules, and used
their Noetherian/reduced/QE and actual regular section-map predicates. It also
checked that cartesianness for arbitrary completed base changes is tested in
formal schemes (not all ringed spaces), while restriction to an open chart can
use the ringed-space square. Locality of stalk maps is explicit. Nonemptiness
is a nonunit stalk ideal, unit-ideal deletion is an iff, every other center is
retained in order, and support refers to the initial singular locus. The old
statement is unchanged and every input clause has the matching field listed
above. Both helper nodes and all docstrings were reread. This is a second pass
by this worker; the dispatcher explicitly forbids starting other agents, and
the maintainer performs the independent review.
