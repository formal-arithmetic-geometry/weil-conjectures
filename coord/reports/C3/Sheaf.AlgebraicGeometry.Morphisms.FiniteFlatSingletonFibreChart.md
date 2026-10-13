## What changed

Proved `AlgebraicGeometry.Scheme.exists_finite_flat_singleton_fibre_chart` in
`Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatSingletonFibreChart`, preserving its signature
and public imports. Added proof imports of `Sheaf.AlgebraicGeometry.EtaleLocalFiniteAtPoint`,
`Sheaf.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

The existing 02LK theorem supplies an actual open subscheme of the pullback and its
singleton fibre. Flatness, etaleness of the source projection, commutativity, and local
Noetherianness follow from Mathlib. The forward neighbourhood implication descends
smoothness along the etale surjection onto the source neighbourhood's open image, then
uses the discrete fibre of the finite map to obtain an etale neighbourhood. The reverse
implication pulls back an open and cancels the etale base map.

Updated the item's DAG proof and proof dependencies to these three existing declarations.
The chapter and unit route is unchanged. The two proper-base-change nodes are used as
generic tools: isolated fibre localization and smooth zero-dimensional fibre etaleness,
not as replacements for a step of the spreading unit. The same tool use already occurs
in `QuasiFiniteFlatCodimensionOneEtaleNeighbourhood`.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.exists_finite_flat_singleton_fibre_chart`
(`lem-sbc-finite-flat-singleton-fibre-chart`). No `sorry` remains in the delivered module;
no new holes, modules, definitions, or statements are added. This is a proof from existing
library declarations, not a decomposition. Local single-file compilation passes. The second reader's scratch `#print axioms`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`;
thus this declaration is proved without any remaining imported proof hole.

## No longer needed

None. No existing import was removed, and the old node had no proof dependencies to prune.
The proof does not require a new scheme-level etale-locus invariance theorem, any separate
finite-piece persistence assertion, or ramification/discriminant results. These were not
DAG dependencies of this item, so no existing nodes are declared pruned.

## Where the brief, the DAG or earlier work was wrong

The old node's single non-elementary proof step had an empty dependency list. It described
02LK and etale-locus invariance in prose without connecting them to library statements.
The updated proof explicitly records the existing localization, smooth descent, and
zero-dimensional fibre criterion that the Lean implementation uses. No mathematical
statement correction or forced adaptation was necessary. Empty schemes have no input x;
all supplied source neighbourhoods contain their designated point, and the argument also
covers dimension-zero and purely inseparable finite-flat fibres without added assumptions.


## Second reading by C3

1. **Interface preservation — pass.** Compared the sole delivered Lean module with
   the repository using `diff`. The only changes are three plain proof imports,
   a declaration-local elaboration option, and the replacement proof. Restored the
   extra space before `:=`; a direct byte comparison of the theorem signature now
   agrees exactly. Public imports, visibility, definitions, hypotheses, and conclusions
   are unchanged. There are no change records or forced adaptations.
2. **Proof and axioms — pass.** Compiled the delivered module locally through
   `lcompile.py`, without errors or warnings. Independently compiled a scratch copy
   with `#print axioms AlgebraicGeometry.Scheme.exists_finite_flat_singleton_fibre_chart`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and no `sorryAx`. There are no
   forbidden declarations, new definitions, or remaining `sorry`s. Read the witness
   construction and each branch: localization supplies a genuine finite open chart;
   base change and restriction give flatness and etaleness; the supplied fibre
   uniqueness is transported using `g(z)=t`. The forward branch factors an etale
   map through its actual open image and proves the factor surjective before
   descending smoothness. The finite fibre's open singleton and nonempty
   neighbourhoods give both dimension bounds. The reverse branch restricts along
   `a` and cancels the etale `b`.
3. **Split statements — pass, none added.** There are no new modules, nodes, or
   split-off statements. The three dependencies have the exact existing Lean
   declarations named by the proof. All three are read in source, and the axiom
   check confirms this proof introduces no unresolved assumption through them.
   Empty schemes cannot supply the input point; zero-dimensional fibres need no
   reducedness assumption, so a nonreduced singleton fibre is not incorrectly
   treated as etale merely because its dimension is zero: smoothness is established
   separately before applying the dimension criterion.
4. **Shortest route, imports, and unit — pass.** Searched Mathlib and the library
   for scheme-level source descent of etaleness, including a fresh Loogle search
   for `AlgebraicGeometry.Etale`. Mathlib's `LocalFlatDescent` is descent under base
   change, not a direct replacement for the source-composition descent here.
   The existing proved smooth source-descent theorem and zero-dimensional-fibre
   criterion give a valid route without new intermediate statements. Each added
   plain import supplies a theorem explicitly used. Each original public import
   supports the unchanged signature. The old `proof_deps` is empty, so the report's
   `No longer needed: None` is complete. Read `sk-prop-input-spreading.json`:
   its `realized` statement and step lists are currently empty; this pre-existing
   bookkeeping state is unchanged. This auxiliary chart is below the unit level,
   and the delivery neither changes nor bypasses any of the unit's proof steps.
5. **DAG agreement — pass.** Compared the delivered node with the repository:
   only `proof`, `proof_deps`, and `proof_origin` differ. Its three dependency IDs
   match localization, smooth source descent, and the smooth zero-dimensional fibre
   criterion. The union of the steps' `uses` is exactly `proof_deps`; the reverse
   branch uses only Mathlib. Statement, statement dependencies, Lean declaration
   record, chapter, and unit are unchanged. No new-node requirements apply.

Second-reading changes: restored signature whitespace, recorded the independent
axiom check and the five review verdicts in this report. No proof term or DAG
repair was needed. Holes closed: one, by the named declaration above; holes added:
zero. No modules or old dependency nodes were pruned.
