## What changed

Replaced the hole in `AlgebraicGeometry.schemeIso_secondMate_normalized_square`
by a complete categorical reduction through the existing theorem
`dualityEquationBaseChangeMap_eq_inverseSquareMate`. The private proved helper
`source_iso_mate_comparison` transposes under the upper exceptional adjunction,
cancels the ordinary direct-image comparison, and uses naturality and the supplied
counit normalizations. The original public declarations, signatures, source
comparison construction, and target meaning are unchanged.

Added `Sheaf.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport` for the
ordinary inverse-square transport step. It contains one theorem and no definitions.
Its statement has no exceptional right adjoints, normalized endpoint comparisons,
or second mates. It specifies every component of its three comparisons; the
component equations determine them uniquely, including the inverse of the
isomorphism. The proof obtains these comparisons and rewrites their components;
it does not select arbitrary data from a mere existence statement.

Added and proved
`AlgebraicGeometry.schemeIso_liftedComparison_counit` in
`Sheaf.AlgebraicGeometry.SchemeIsoLiftedComparisonCounit`. This lemma applies a
supplied postcomposed component identity at a(K) and then the supplied ambient
normalization. It addresses one vertical morphism and has no square or second mate.
Its proof is a direct equality-transitivity argument. Keeping its comparison
parameters generic avoids unfolding the pullback-specific derived model data.

The main module uses proof-only imports of both new modules. The two existing
public imports remain public. Scoped elaboration transparency options on the two proofs keep the chosen derived
comparison families folded. All three node records follow the new route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeIso_secondMate_normalized_square`
(`lem-sc-scheme-iso-second-mate-normalized-square`). Its proof is complete from
named declarations. Also proved the private categorical helper
`source_iso_mate_comparison`. Also proved the new declaration
`AlgebraicGeometry.schemeIso_liftedComparison_counit`
(`lem-sc-scheme-iso-lifted-comparison-counit`), with no remaining hole in that module.

Added exactly one hole:
`AlgebraicGeometry.schemeIso_inverseBaseChange_transport`
(`lem-sc-scheme-iso-inverse-base-change-transport`), in its own new module.
Its whole proof is `:= by sorry`, with its source and complete proof in words.
There are no holes in definitions and no holes left in the item's module.
This is a decomposition: one upper hole closed and one strictly smaller ordinary
transport hole added, net zero holes. The existing inverse-square presentation
lemma is already proved; this delivery adds no hole for the mate calculation.

## No longer needed

Removed the main module's direct proof import
`Sheaf.AlgebraicGeometry.DerivedBaseChangePasting`. Its geometric calculation is
needed by the new ordinary transport item and that module retains the import.
Thus no whole module is claimed pruned from the import closure.

The old proof dependencies no longer used directly by the main node are
`lem-cat-right-adjoint-composition`, `lem-pc-derived-base-change-pasting`,
`def-pc-derived-base-change-map`, `def-sc-duality-equation-base-change-map`, and
`lem-pc-ringed-spaces-derived-pullback-composition`. The latter two still supply
statement data (including the unchanged source comparison); their use in the
proof is now mediated by the inverse-square presentation and ordinary transport.
These are removals from the direct proof plan, not from the statement dependencies. The inverse-square presentation and the proved counit calculation replace
the original expanded second-mate calculation. These declarations remain available
through statement dependencies and the ordinary transport step; none is claimed
globally unnecessary. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped without reducing the target hole. The absence of a
packaged second-mate transport theorem is not an obstruction: the existing
inverse-square presentation permits a direct categorical proof. The remaining
ordinary comparison can be stated independently of the four exceptional right
adjoints, so it is a strict subargument rather than the original equality renamed.

The unit route is preserved. The original node lies below the unit's realized
statements/steps; the reduction implements its ordinary-comparison step and proves
the exceptional mate step. The comparisons are specified by component formulas,
which also handle identity isomorphisms, zero complexes, and empty schemes.
No statement is disputed and no existing interface was changed.

## New nodes

`lem-sc-scheme-iso-inverse-base-change-transport` records the inverse ordinary-square
transport step. It produces the explicitly specified projection and direct-image
unit comparisons and the inverse-square equality for every quasi-coherent object.
Its Lean module is `Sheaf.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport`.
The node records its Stacks sources, searches, edge-case argument and proof plan.

`lem-sc-scheme-iso-lifted-comparison-counit` records the proved normalization bridge
for one vertical morphism. Its module is
`Sheaf.AlgebraicGeometry.SchemeIsoLiftedComparisonCounit`; it adds no hole. The
component property is written after arbitrary postcompositions to keep the pinned
comparison family folded while applying the normalization. Identity postcompositions
recover the underlying component identity.

There are no change records or forced adaptations, since existing public
signatures and definitions are unchanged.

## Second reading by H1

1. PASS: Compared the main module with the repository by `diff` and separately
   compared the raw declaration headers. Both existing signatures are byte for
   byte identical; `schemeIsoMateSourceIso` is also unchanged in its entire body.
   Only proof imports, scoped proof elaboration options, the private proved helper,
   and the target proof changed. No existing statement or definition was adapted.
2. PASS: All three modules compiled individually in dependency order through
   `lcompile.py --all`, without errors or warnings. The only textual hole is the
   whole proof of `AlgebraicGeometry.schemeIso_inverseBaseChange_transport`.
   No forbidden declaration or attribute and no hole in a definition occurs.
   The categorical helper uses only Hom-equivalence injectivity, counit mate
   identities, naturality and cancellation of the supplied isomorphism q.
   A scratch copy with explicit `#print axioms` checks is included in the local
   verification: the unchanged source definition and private helper use only
   propext, Classical.choice and Quot.sound. The three public theorems also
   depend on sorryAx through the split theorem or existing open imported
   declarations; no other axiom appears. The delivery tool checks every
   declaration again.
3. PASS: The remaining ordinary-square theorem is strictly a subargument: it
   contains neither exceptional right adjoints nor their comparisons nor second
   mates. The three component formulas fix k, q and sigma uniquely; identity
   postcompositions recover q's component, and faithfulness fixes the lifted
   maps. The main proof merely eliminates this existence statement in a theorem;
   it constructs no data definition from it. Reviewed the complete docstring and
   matching node. Identity source changes reduce by the pinned unit/composition
   laws; zero coefficients and empty schemes cause no cancellation of an object
   or assumption of nonemptiness. The counit bridge is already proved by equality
   transitivity and adds no hole. Fresh leanfinder, loogle and grep searches, plus
   local Lean searches, found generic mates tools but no fixed-component ordinary
   transport result. `exists_derivedBaseChange_source_iso` was inspected: its
   unspecified existential comparisons do not provide these component equations.
4. PASS: The main proof reduces the fixed second mate using the already proved
   inverse-square presentation, then proves its exceptional-adjunction transport
   directly. Both new proof imports are used, and both original public imports
   supply existing signature data. The pasting import remains in the ordinary
   transport module for its recorded proof plan, so no whole module is pruned.
   Checked `dag/units/sk-thm-picard-duality.json`: this auxiliary item is not a
   realized unit statement or step; its route and realized fields are unchanged.
   This remains a decomposition (one original hole closed, one lower hole added),
   with net zero holes rather than a completed import-closure proof.
5. PASS: Read all three node records against the Lean statements and proof bodies.
   Each proof_deps is exactly the union of its proof steps' uses. The existing
   node changes only proof, proof_deps and proof_origin. Both new nodes have the
   required source, statement dependencies, searches, provenance, blueprint,
   chapter/unit and verbatim Lean statement records.

Second-reading changes: completed `## No longer needed` by explicitly listing
all five removed old direct proof dependencies and distinguishing their retained
statement or indirect uses. No Lean proof, statement, definition or node repair
was needed. No additional hole was closed or added during this reading.
