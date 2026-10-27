## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceHenselianProperClopenLift` states Stacks
Tag 0CWI, read in `literature/stacks-project/spaces-more-morphisms.tex`,
lemma-split-off-proper-part-henselian, lines 8482–8521. The node statement is unchanged.
The sole theorem has proof `sorry`; the two helper definitions contain actual data.
Its docstring records all seven proof steps and their DAG inputs.

Hypothesis and conclusion correspondence:

- The commutative ring A is `{A : Type u} [CommRing A]`; its ideal is `(I : Ideal A)`.
  The henselian-pair hypothesis is `[HenselianRing A I]`, exactly the interface
  specified in def-weil-pbc-henselian-terminology (including the Jacobson condition).
- X is an arbitrary `AlgebraicSpace (Spec (CommRingCat.of A))`, and `f` is its map
  to the representable base `schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A))))`.
  Using Spec A as the common base is just the category of algebraic spaces over A;
  it imposes no representability condition on X or f.
- Separatedness and finite type are respectively `hsep : MapIsSeparated f` and
  `hft : MapIsFiniteType f`. The latter already includes quasi-compactness.
- `henselianPairClosedFibreBaseMap I` is the actual Yoneda map of
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`, not an arbitrary map.
  `enlargedFibreProduct (henselianPairClosedFibreBaseMap I) f` is X_0, with the
  factors reversed from the displayed mathematical notation. It is the actual
  sheaf fibre product, with algebraicity from the recorded fibre-product theorem.
- The given subspace is presented by Z and i. `hopen` requires every scheme test
  of i to be an open immersion, and `hclosed` requires every scheme test to be a
  closed immersion. Together these say precisely open and closed subspace.
  Open immersion includes the isomorphism with the ambient restricted structure
  sheaf; these are not arbitrary ringed-space structures on a point subset.
  A representable open immersion is a monomorphism, so presentation by such an
  arrow is equivalent to the recorded `OpenSubspace` subfunctor formulation.
  No second predicate or definition of open subspace is introduced.
- The properness of Z over Spec(A/I) is `hproper : MapIsProper
  (i ≫ enlargedFibreProductFst (henselianPairClosedFibreBaseMap I) f)`.
  In particular this is properness over the quotient spectrum, not over Spec A.
- The existential W and w present the lifted subspace of X. The first two
  conjunctions require representable open and closed immersions on all scheme
  tests. `MapIsProper (w ≫ f)` says exactly that W is proper over Spec A.
- `∃ l : Z ⟶ W, IsPullback l i w (henselianPairClosedFibreInclusion I f)`
  identifies Z, with its specified inclusion into X_0, with W ×_X X_0.
  Since X_0 is X ×_A Spec(A/I), this is W ×_A Spec(A/I) = Z as subspaces of X_0.
  The cartesian square forces the quotient-base map on Z as well; it does not
  assert only an unrelated abstract isomorphism. The helper for its bottom arrow
  is literally the second sheaf-pullback projection.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`: Mathlib `HenselianRing`, and the
  recorded terminology including `HenselianLocalRing` and
  `IsStrictlyHenselianLocalRing` (the latter two are not needed in this theorem).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`, with its full test-scheme
  pullback-square definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsProper` and their chart/point definitions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`; its actual sheaf pullback is bundled by
  `enlargedFibreProduct` in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.
  That existing module also supplies `schemeSpace` and `enlargedFibreProductFst`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- Proof-only imports for recorded proof dependencies: `SpaceFiniteTypeComposition`
  (`mapIsFiniteType_comp`), `SpaceLocalPropertiesChartTest`
  (`local_properties_chart_test`, `local_properties_chart_test_iff_scheme`),
  `AlgebraicSpaceOpenSubspace` (`OpenSubspace`), `AlgebraicSpacePointOpenCalculus`
  (`point_open_calculus`), `WeilConjectures.RingTheory.HenselianPairPrimeConnected`
  (`PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian`), and
  `EtaleOpenChartMorphismDescent` (`etale_open_chart_morphism_descent`).
  Unstated proof-only nodes (weak Chow, separated composition, proper base change,
  proper composition, the scheme lifting theorem and closed-subspace properness)
  currently have no Lean module to import; their ids remain in the proof docstring.

Only already-landed definition nodes were added to stmt_deps:
`def-trf-scheme-algebraic-space` owns the existing `schemeSpace` construction;
`def-sfb-space-sheaf-fibre-product` owns the existing `enlargedFibreProduct` and
`enlargedFibreProductFst` constructions. Both records point to the definitions in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`; the enlarged-site theorem is
not a statement dependency. `def-weil-open-immersion` and
`def-weil-closed-immersion` own the actual scheme-test predicates. No new nodes,
statement corrections or dependency-module repairs are needed.

Edge cases checked before writing: empty X, empty Z, the empty lift W, and Z equal
to the entire closed fibre are all admitted. A zero ring and I = 0 are admitted;
for I = 0 the closed fibre is canonically X and the assertion reduces to choosing
the given proper clopen part. I = top is not independently excluded, and the
henselian Jacobson condition itself forces the zero-ring case if it occurs.
The statement assumes neither that X is proper nor that A is Noetherian, local,
nonzero, reduced, or complete. No finite-presentation or representability condition
is imposed on f. The ring and schemes use the same explicitly bound universe u,
matching the library's scheme-space size convention.

Searches made on 2026-10-24:

- msearch.py leanfinder: "A proper clopen subspace of a closed fibre lifts to a proper
  clopen algebraic subspace over a henselian pair". Eight hits: HenselianRing,
  HenselianLocalRing, IsAdicComplete.henselianRing, Algebra.QuasiFiniteAt.isClopen_singleton,
  instHenselianRingMaximalIdeal, HenselianLocalRing.TFAE, Field.henselian,
  HenselianRing.is_henselian. None states the algebraic-space lift.
- msearch.py leansearch: "A proper clopen part of a closed fibre of a separated finite
  type algebraic space lifts over a henselian pair". Eight hits, headed by
  AlgebraicGeometry.isProper_eq and Algebra.QuasiFiniteAt.isClopen_singleton,
  followed by scheme immersion lift facts, formal etaleness and separatedness.
  None states the result.
- msearch.py loogle: "HenselianRing, IsProper". Zero hits; IsProper unqualified is
  unknown to the endpoint. The actual project properness predicate was located
  and read directly in the recorded source module.
- msearch.py grep: "henselian.*proper|proper.*henselian|clopen.*proper|proper.*clopen".
  Four file hits: Topology/ClopenBox, Topology/Separation/Profinite,
  Topology/MetricSpace/Polish and RingTheory/Henselian. None is this statement.
- rg of the same expression in live WeilConjectures and Sheaf sources located
  HenselianClopenRestriction, HenselianConnectedness and other scheme or unrelated
  constructions. HenselianClopenRestriction assumes the ambient scheme proper and
  is the clopen restriction bijection, not this algebraic-space finite-type lift.
  ConnectedProperFibresProper cites this node but does not state it. The explicit
  id search in WeilConjectures had no hits. Searches for the three proposed full
  declaration names in both project roots, Mathlib and dag/lean_names_upstream.json
  had no hits. Search for schemeSpace/enlargedFibreProduct found their existing
  definitions, which are used rather than copied. The existing adic quotient map
  handles I^n with an auxiliary base morphism, so the two helpers here expose only
  the current node's quotient map and projection, using the canonical existing
  constructors rather than defining another closed-fibre notion.

Validation: scompile.py compiled both the sandbox import context and the final
module in approximately 2–3 seconds each, with no errors or warnings. A second
compile also checks the explicit direct public statement-dependency imports.
No STATEMENT-DISPUTED finding or source discrepancy.

## Second reading by Q24

The dispatcher forbids additional agents and assigns the maintainer an independent
review. This is therefore a second in-thread reading, not a claim of an independent
worker review. Reopened the node, Tag 0CWI and the final Lean file. Checked every
binder against the source: arbitrary henselian pair; arbitrary separated finite-type
space; clopen Z in the actual quotient fibre; properness over the quotient spectrum;
existence of clopen W proper over the original spectrum; and identification of the
subspaces with their inclusions by the cartesian square. Checked the orientation
of IsPullback: top l:Z→W, left i:Z→X_0, right w:W→X, bottom X_0→X. This is exactly
W ×_X X_0, and hence the required closed fibre. The representable open/closed
conditions include the restricted sheaf and do not assert only a point equality.
No mathematical mismatch found. Added direct public imports for all original
statement dependencies before the final compilation; no statement change was made.

## Returned delivery repair

Repaired the H2/H4 finding in the independent review of immutable head
4c24188e78da. Replaced `lem-trf-space-enlarged-etale-ringed-site-model` in
stmt_deps with the two landed definition owners `def-trf-scheme-algebraic-space`
and `def-sfb-space-sheaf-fibre-product`, after reading their statements and Lean
records against the existing definitions. Updated the paragraph identifying added
statement dependencies. Compared the retained sandbox node against current main:
all original fields outside lean and stmt_deps agree. The Lean module and entire
lean record are unchanged from the returned delivery. The reviewer accepted the
mathematics and asked for no compilation because no Lean changed; the prescribed
dry-run and delivery wrappers still perform their normal validation.
