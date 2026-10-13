## What changed

Closed `AlgebraicGeometry.Etale.etale_limit_open_comparison_certificate_degree`
with its original signature. The proof applies `StageCohomologyComparison.system`
to the explicit tail-open system, using the proved geometry and coefficient
restriction theorems saved in this sandbox. The supplied cohomology arrows are
reassociated, and the coefficient-leg equality identifies the supplied cocone.

Repaired the prior compilation timeout without splitting the proof or changing
any existing definition. Local aliases for the restricted system caused expensive
kernel conversions. The constructor now receives the explicit restricted-system
terms. The leg calculation unfolds only `tailOpenCohomologyLegDegree`,
`tailOpenCone` and `tailOpenSheaf` before rewriting the coefficient equality.
All three delivered modules compile cleanly with the prescribed lcompile.py;
the main file took 35.0 seconds, coefficients 9.7 seconds, and geometry 2.6 seconds.

The geometry helper proves the limit by transporting Mathlib's `isLimitOpensCone`
along the equivalence with the over category. It proves affine transitions by
base change, compactness by affine preimages, quasi-separatedness by restriction,
and the least-stage isomorphism by restricting the given e. The coefficient
helper uses the existing `tailOpenRestrictedSystem_coherence`, proves finality
of the upper-tail inclusion and preservation of the sheaf colimit, and proves
the coefficient-leg equality by expanding the specified `tailOpenLimitIso`.
Both helpers retain real explicit constructions; they choose no data from a
holed existence theorem. No existing interface or target statement changes.

## Proved and sorry left

Closed the item's single hole:
`AlgebraicGeometry.Etale.etale_limit_open_comparison_certificate_degree`
(node `lem-weil-pbc-etale-limit-open-comparison-certificate-degree`).

Also delivered complete proofs of
`AlgebraicGeometry.Etale.etale_limit_tail_open_geometry`
(node `lem-weil-pbc-etale-limit-tail-open-geometry`) and
`AlgebraicGeometry.Etale.etale_limit_tail_open_coefficients`
(node `lem-weil-pbc-etale-limit-tail-open-coefficients`).

Holes closed in the existing item: 1. Holes added: 0. Holes split off: 0.
No `sorry` remains in any delivered module. The imported existing theorem
`AlgebraicGeometry.Etale.tailOpenRestrictedSystem_coherence` remains a hole
in the read-only library; this delivery does not add or duplicate it.
This is a proof from existing stated dependencies, not a sorry-free proof
of their full transitive closure.

## No longer needed

Removed the item's direct proof imports:
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit` (used by the geometry helper);
- `Mathlib.CategoryTheory.Filtered.Final` (used by the coefficient helper);
- `Mathlib.CategoryTheory.Adjunction.Limits` (used by the coefficient helper);
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` (unused);
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already available through
  the public statement imports).

The canonical cocone existence theorem
`etale_limit_open_cohomology_cocone_degree` is not needed: K and its cocone
are already supplied. Its node
`lem-weil-pbc-etale-limit-open-cohomology-cocone-degree` is removed from the
proof dependencies, but its module remains publicly imported because the
unchanged statement needs its degree-map definitions.

The former direct dependencies
`lem-weil-pbc-limit-cone-affine-projections-opens`,
`lem-weil-pbc-colimit-initial-full-subcategory`, and
`lem-weil-pbc-left-adjoint-preserves-colimits` are handled in the geometry
and coefficient helpers. The standalone node `lem-weil-pbc-inverse-image-composition` is
not applied: the proof uses the explicit restricted-system coherence theorem.
Its composition constructions remain needed through that system.
The old direct dependency `def-weil-pbc-scheme-conventions` is used in the
geometry helper rather than directly by the item. These entries account for
every old proof dependency except the retained certificate definition.
No existing module is claimed globally unreachable, and no realized unit
statement or proof step is bypassed.

The earlier attempt's duplicate tail-open definitions are not reintroduced;
the existing `EtaleLimitOpenRestrictedSystem` supplies all canonical data.

## Where the brief, the DAG or earlier work was wrong

The prior blocker was reproducible: the main proof exceeded the 60-second
limit. Profiling located the cost in kernel conversion of AddCommGrpCat
structures, rather than tactic elaboration. Explicit constructor arguments
and normalization of the leg before rewriting repair this; no tool or limit
was changed, and no theorem was split solely to evade the limit.

The saved helpers correctly reuse the library's restricted-system constructions,
which the original attempt had duplicated. Their statements were checked on
empty opens, zero coefficients and singleton diagrams; neither asserts
cohomology continuity. The main theorem certifies the supplied map without
asserting that it is an isomorphism.

Read Stacks Tags [09YQ](https://stacks.math.columbia.edu/tag/09YQ) and
[01F7](https://stacks.math.columbia.edu/tag/01F7), and the Mathlib definitions
and lemmas used by the helpers. LeanFinder returned `isLimitOpensCone` and
related open-limit tools; Loogle confirmed categorical associativity; local
rg searches found the restricted-system theorem and the degree-zero sibling.
The saved LeanSearch attempt records HTTP 500. Searches are in searches.jsonl.

## New nodes

`lem-weil-pbc-etale-limit-tail-open-geometry` records the proved geometric
restriction theorem in `EtaleLimitTailOpenGeometry`. It is strictly the
geometric part of the certificate construction.

`lem-weil-pbc-etale-limit-tail-open-coefficients` records the proved coherent
coefficient restriction, colimit and leg theorem in `EtaleLimitTailOpenCoefficients`.
It uses the specified canonical coefficient isomorphism and is independent
of the allowed predicate, compactness, the scheme-limit hypothesis and degree.
Neither new node contains a hole. No change records or forced adaptations.

## Second reading by E2

1. Compared the sole existing module against the repository with diff and a
   byte comparison of the theorem signature. Verdict: unchanged signature,
   public imports, visibility and docstring; the only changes are proof-local
   options, private proof imports and the proof. The other two modules are new.
   There are no changes to existing definitions or target statements and no
   forced adaptations or change records.

2. Read all three Lean modules and compiled the complete set in import order
   with lcompile.py: coefficients 9.6 s, geometry 2.5 s, main 36.1 s, no warnings
   or errors. Searched the delivered Lean for sorry and forbidden declarations:
   none. A scratch import with #print axioms for all three public theorems
   compiled: geometry uses only propext, Classical.choice and Quot.sound;
   coefficients and main additionally use sorryAx through the imported
   tailOpenRestrictedSystem_coherence. The two private geometric constructions
   have explicit fields. The choices of limit proofs, colimit proofs and the
   least-stage isomorphism come from the proved geometric theorem or a universal
   property, not from an unproved theorem selecting arbitrary data. Verdict: a
   valid reduction with one old hole closed and zero holes added.

3. There are no split-off holes. Read both new helper statements, their word
   proofs and nodes against the actual formulas. Geometry requires the limit,
   affine transitions, quasi-separated stages, W compact, W ≤ O and the given e;
   it does not assume unjustified compactness of arbitrary stage opens.
   Coefficients requires only directedness, the original coefficient coherence
   and the supplied sheaf colimit. It uses the specified tailOpenLimitIso, not
   an arbitrary isomorphism. Empty W gives empty stages, singleton diagrams
   reduce to restriction along the identity, and zero coefficients preserve
   all formulas; a preorder need not be antisymmetric. Both helpers are strict
   parts of the certificate argument, with no certificate in their conclusions.
   Searched lean/Sheaf and upstream WeilConjectures for tailStageOpen,
   tailOpenCohomology and StageCohomologyComparison; the degree-zero sibling
   supplies the same route only in degree zero. New LeanFinder query on compact
   open restrictions returned affine-transition limit tools, not a shorter
   certificate proof; Loogle confirmed isColimitWhiskerEquiv. Verdict: no
   duplicate exact theorem or restatement replacing the item.

4. Read StageCohomologyComparison.system, the restricted-system module and
   Mathlib AffineTransitionLimit.lean:203–245. The main proof uses the original
   K, eK, hK, cocone and hι. Reassociation matches hK to the system arrow formula;
   expanding the leg and applying the proved coefficient-leg equality matches
   its cocone formula in every degree n. Geometry transports isLimitOpensCone
   along the explicit tail/Over equivalence; the affine square is cartesian.
   Coefficients uses finality (a common upper bound and uniqueness of preorder
   arrows), then preservation by the inverse-image left adjoint. Read
   [09YQ](https://stacks.math.columbia.edu/tag/09YQ),
   [01YX](https://stacks.math.columbia.edu/tag/01YX) and
   [01F7](https://stacks.math.columbia.edu/tag/01F7): the supplied map is certified
   without making a continuity assertion. The private imports each supply
   proof declarations; public imports supply the unchanged signatures.
   Compared all seven old proof dependencies with the new route and completed
   the pruning report. Read sk-thm-p1.json realized: this item is below its
   statement and four realized steps; none is bypassed or edited. Verdict:
   the unit route remains intact and no module is globally pruned.

5. Checked each node's recorded Lean signature against its module, and each
   proof step against the declarations it actually uses. The main node lists
   the two helpers and certificate definition. The coefficient node records
   the existing coherence theorem, final reindexing, colimit preservation and
   explicit coefficient-leg calculation. The geometry node previously cited
   only conventions for affine base change and compact inverse images; added
   the existing Mathlib leaves lem-weil-pbc-affine-morphism-permanence and
   lem-weil-pbc-quasi-compact-morphism-preimage-qc-open. Separated out the
   elementary open-subspace quasi-separatedness argument. Its statement now
   explicitly introduces c and cites the scheme and cone definitions; its
   source records Tag 01YX and the permanence tags. New nodes retain their
   creation, blueprint, search and Lean records. Verdict: DAG matches Lean.

Second reading changed only the report and new geometry node: completed the
removed-import/dependency list, made the geometry statement self-contained and
corrected its proof citations and source. No Lean proof needed repair.
