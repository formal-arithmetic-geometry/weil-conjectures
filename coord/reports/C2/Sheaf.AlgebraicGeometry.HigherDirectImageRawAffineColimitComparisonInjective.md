## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.exists_raw_affine_colimit_comparison_injective`
with a complete Lean reduction. Its signature, public imports, data structure and
existing docstrings are unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherence` and
`Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation`.

The proof constructs the group diagram by evaluating the raw natural transformations
at U, and constructs its cocone by evaluating the limit maps. Identity isomorphisms
supply eStage and eLimit, and the transition and leg equations are reflexivity.
The geometric presentation supplies precisely the inputs of the existing complex
continuity theorem. The existing `EtaleComplexCohomologyPresentation.isColimit`
applies that theorem; `IsColimit.ofWhiskerEquivalence` removes double-opposite
reindexing. The unique colimit comparison is an isomorphism and is therefore injective.
No definition selects arbitrary data from a merely existential theorem.

The new coherence lemma assumes no affineness, qcqs, directedness, nonemptiness,
or limiting cone. It supplies additive natural transformations and algebraic
laws, without any continuity claim. The new geometric lemma accepts an already
specified group diagram and cocone, and asserts the input complex presentation,
without IsColimit B or injectivity. These are separate parts of the original argument.
Their docstrings and nodes contain their source and proof in words.

Compiled the two new modules and the main module through lcompile.py. The final
main-file compilation succeeded without errors or warnings. The delivery dry run
performs the final compilation and axiom checks. Mathlib searches used LeanSearch
(unavailable, HTTP 500), LeanFinder, Loogle and grep. No exact theorem was found.
The source pages read were Stacks Tags 09Z1, 03Q8 and 0EZM.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.exists_raw_affine_colimit_comparison_injective`
(node `lem-sbc-raw-affine-colimit-comparison-injective`). Its proof is complete,
but depends on the two new statements below and on existing library obligations.
This is a decomposition: one original hole closed, two new holes added, not a
sorry-free proof of the geometric continuity argument.

Every sorry left in the delivery is the entire proof of one public theorem:

- `AlgebraicGeometry.Etale.abelianRawPullback_coherent`
  (node `lem-sbc-abelian-raw-pullback-coherence`, module
  `Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherence`).
- `AlgebraicGeometry.Etale.abelianRawCocone_complex_presentation`
  (node `lem-sbc-abelian-raw-cocone-complex-presentation`, module
  `Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation`).

There is no sorry in the main module and no added definition or axiom.

## No longer needed

The main module no longer imports `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek.EtaleMap`, or
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; all are proof dependencies
of the two new modules or are transitively provided by them. The corresponding old
proof-dependency nodes no longer occur as direct dependencies of this node:
`def-weil-pbc-inverse-image`, `lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-affine-morphism-permanence`, `def-weil-pbc-etale-cohomology`,
`prop-weil-pbc-derived-inverse-image-adjunction`, `def-weil-pbc-sheafification`,
`lem-weil-pbc-dplus-injective-representative`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-etale-restriction-injectives`. The continuity node
`lem-weil-pbc-etale-cohomology-limit-complex-systems` remains recorded because it is
the existing theorem used by the presentation step (through its wrapper).
Both new proof imports are used directly.

The existing modules `HigherDirectImageRawAffineComplexPresentation`,
`RestrictedAffineComplexSystem` and `RawRestrictedCohomologyNaturalIso` were read.
The first two were not imported as a proof shortcut: their exposed stage isomorphisms
have no equation intertwining each stage transition with the raw transition. This
is an interface limitation, not a claim that these nodes can be globally pruned.
The geometric obligation cites the existing natural raw/restricted comparison.

## Where the brief, the DAG or earlier work was wrong

The assigned module had only statement imports, despite the standing brief saying
that planned proof dependencies are already imported. The original plan described
the construction correctly but did not expose a usable varying-coefficient natural
raw diagram or a transition-compatible complex presentation in Lean.

`RawCohomologyComplexPresentation` records compatibility of stage isomorphisms
with limit legs but not with stage transitions. Leg compatibility alone cannot
identify the diagrams: the individual limit legs need not be injective. Consequently
its existing existence theorem cannot supply the htrans field of the present item.
The new presentation theorem explicitly requires hmap as well as hleg, and the
main proof supplies both from the canonical raw maps.

The constant-coefficient ModuleCat raw diagram is a different encoding and does
not accept the present varying abelian coefficient system. It was not specialized
silently. The existing `EtaleComplexCohomologyPresentation` predicate and its
proved continuity wrapper were reused, rather than defining a duplicate predicate.

Edge cases: the coherence lemma allows an empty indexing preorder; its universally
quantified laws then hold vacuously. Its arbitrary cone need not be limiting.
Zero coefficients, zero classes and empty etale objects preserve all identities.
The geometric lemma retains the original nonempty directed hypotheses, needed
for continuity. Degree zero is ordinary restricted sections, and empty affine U
has zero groups; neither case requires an added hypothesis. Arbitrary isomorphisms
e and eB in that lemma are constrained by both transition and leg equations, so
changing their coordinates does not change the prescribed cocone.

No unit statement or realized unit step was bypassed or changed. The unit record
`sk-lem-failure-field` has no realized nodes here; the existing higher-direct-image
limit route through restricted cohomology and complex continuity is retained.
The blueprint ancestor command returned None for this freshly created item;
the new nodes therefore inherit the explicit ancestor
`sbc-lem-higher-direct-image-limit` recorded on the parent node itself.

## New nodes

`lem-sbc-abelian-raw-pullback-coherence`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-abelian-raw-pullback-coherence.json`,
records the algebraic naturality and coefficient coherence portion of parent
proof step 2. Its statement omits all geometric continuity hypotheses and conclusions.
Its Lean module is `lean/Sheaf/AlgebraicGeometry/AbelianRawPullbackCoherence.lean`.

`lem-sbc-abelian-raw-cocone-complex-presentation`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-abelian-raw-cocone-complex-presentation.json`,
records parent proof steps 1 and 3, with the stage-transition equation made explicit.
It supplies only the input to the existing continuity theorem, which the main module
then applies. Its Lean module is
`lean/Sheaf/AlgebraicGeometry/AbelianRawCoconeComplexPresentation.lean`.

No change record is needed: no existing interface, definition or statement changed,
and no other module was adapted. Blueprint searches for raw cohomology and restricted
cohomology returned no matching blueprint nodes; searches of the existing Lean modules
found the related, but insufficient, presentation interfaces described above.

## Second reading by C2

1. **Visibility and signatures.** I diffed the delivered main module against the repository version. The target theorem and the existing `RawAffineColimitComparisonData` structure have byte-for-byte identical signatures; only proof imports and the proof body changed. The two added modules introduce exactly the two declarations recorded by their nodes.

2. **Compilation and axioms.** All three sandbox modules compile with `lcompile.py --all`. The only remaining `sorry`s are the complete proofs of `abelianRawPullback_coherent` and `abelianRawCocone_complex_presentation`, each named and documented with a matching node. There are no axioms, unsafe declarations, hollow definitions, or sorries in definitions. The main theorem's proof uses only the stated imported obligations and standard colimit isomorphism facts.

3. **Statements and split obligations.** I checked both new statements against their docstrings and edge cases. The coherence statement is algebraic and makes no geometric assumptions; the presentation statement supplies only the continuity input and retains the required transition and leg equations. Neither restates the parent theorem, and both are strictly smaller obligations with explicit sources.

4. **Pruning and route.** The proof constructs the diagram and cocone from the canonical natural transformations, applies the existing complex-presentation continuity route, transports across the double-opposite equivalence, and obtains injectivity from the colimit comparison isomorphism. Removed imports and obsolete direct proof dependencies are listed above; the unit route and its existing continuity step are retained.

5. **DAG agreement.** The parent node's `proof`, `proof_deps`, and `proof_origin` match the proof and its two split obligations. The two new node records contain their Lean statements, sources, proof plans, searches, and `lean` records. No target statement, definition, or unit realization was changed.

I changed only this report: corrected the pruning inventory and added this second-reading record. No Lean proof or statement required repair.
