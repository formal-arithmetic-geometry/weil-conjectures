# Stage-1 delivery: lem-sfb-smooth-curve-function-field-p-basis

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-curve-function-field-p-basis.json`: item, statement unchanged, six-step split; Mathlib searches found no exact match.
- `citations.json`: nine entries, one for every step/node pair, with verbatim statements.
- `searches.jsonl`: actual search-command output records; earlier searches in the item are preserved.
- `report.md`: this report.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and the p-basis notion, and specifically the Curve and FieldTheory directories. The closed existing p-basis extension and differential-basis declarations cover tools, not all clauses of this item. `AlgebraicGeometry.finrank_kaehlerDifferential_functionField` in `WeilConjectures/AlgebraicGeometry/Curve/FiniteMapToLine.lean:161` covers only the differential dimension under a smooth-relative-dimension hypothesis; it does not assert the monomial basis and is not an attachment of this item.

## Wanted literature

None. All sources used are in the read-only repository.

## Corrections and source context

The statement is correct and was retained, including dimension exactly one and no properness hypothesis. The imported item was statement-only. Its source Stacks 0CCY is about proper curves, but the paragraph used here is the generic differential calculation: its proof needs only smoothness and dimension one. Algebraic closedness is used explicitly to replace the compositum kK^p by K^p.

Read the chapter and unit records, SETUP's three blueprint levels, and `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` (unit section and direct-images proof). The unit record points to an older six-functors unit; the current source places this direct-image argument in six-functors-basics. Its current proof (3) contains the surrounding direct-image compactification route, not this auxiliary field calculation. The inherited `blueprint.from.node = null` and its detailed ancestry/place are preserved; `tools/blueprint_refs.py ancestor` returned None. No unit or chapter route was changed.

The source lemma 07P2 has an unrelated typographical error in its maximality proof (`L[z]/(z^p-x)` rather than `L[z]/(z^p-x^p)`). We use the existing p-basis theorem's statement, not that formula. No disputed statement is needed in this item.

## Searches and reuse

Searched the entire DAG for p-basis, smooth differential rank, function-field differentials, the source tags and localization. Ran `tools/blueprint_refs.py search` for `p-basis`, `differential`, and `function field`; read the returned relevant nodes. The blueprint has no exact singleton p-basis statement. Existing nodes already cover dimension on opens, smooth local differential rank, affine fraction fields, localization of differentials, extension of a p-independent family, and differentials of a p-basis. Accordingly no new nodes were created.

The logged Mathlib searches used LeanFinder with both geometric and separably-generated-field phrasings, LeanSearch, Loogle, and grep in RingTheory, FieldTheory and RingTheory/Smooth. Read the returned smooth-cotangent declarations, general power-basis construction and purely inseparable degree result in the pinned source. None states the curve-field conclusion or is a one-line specialization giving all its clauses: the smooth results require a presentation, the power-basis results require a generator and its degree, and purely inseparable finite degrees are only asserted to be some power of p. Services all answered; no unavailable result was disguised as a negative.

## Not duplicates

No new nodes. In particular we did not create a curve-field differential-rank clause or a singleton p-basis clause: both are proved within the item by assembling existing statements.

## Review by Q102

I read Stacks `curves.tex`, Tag 0CCY, label `lemma-inseparable-deg-p-smooth`, second proof paragraph, together with `more-algebra.tex`, Tags 07P1 (`definition-p-basis`) and 07P2 (`lemma-p-basis`). The latter really states both extension of an arbitrary p-independent family and the implication from a monomial p-basis to a differential basis. I also read `morphisms.tex`, Tag 02G1 (`lemma-smooth-omega-finite-locally-free`), `algebra.tex`, Tag 00RT (`lemma-differentials-localize`), and `varieties.tex`, Tag 0A21 (`lemma-dimension-locally-algebraic`), part (3). There are no new nodes needing a separate source audit.

Step 1 uses the definition of algebraically closed in `def-weil-algebraic-closure`, whose statement explicitly gives roots of nonconstant polynomials. The argument applies it to X^p-a, including a=0, with p prime and positive. It writes the field operations on pth powers and the inclusion of the given coefficient field explicitly. No perfection or Frobenius-surjectivity theorem is smuggled in.

Step 2 uses `lem-sc-integral-locally-algebraic-opens-dimension`, whose statement gives equality for every nonempty open of an integral locally finite-type scheme; `def-kun-topological-dimension-at-point`, whose minimum over open neighbourhoods gives the local dimension; and `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`, whose statement supplies precisely an affine neighbourhood with free differential module of that rank. The curve is integral, finite type, dimension one and smooth; the base is Spec k and the fibre is C. Thus its rank parameter is one, including at the generic point. The general tool nodes are declared in split_report.tool_uses; they implement the local rank input and do not replace a unit proof step.

Step 3 uses `lem-sc-integral-function-field-affine-fraction`, which explicitly gives the domain A and the fraction-field structure via the germ map for every nonempty affine open; and `lem-weil-pbc-kahler-differentials-localization`, which explicitly identifies localized differentials with the differentials of the localization over the same base ring. The chosen W is nonempty because it contains eta. The multiplicative set is A minus zero. Rather than cite a definition as a theorem about tensor products, the step displays the two localized mutually inverse maps on fractions, so localization preserves the chosen rank-one isomorphism directly. It establishes actual dimension one, not just a finrank value without finite-dimensionality.

Step 4 cites `lem-weil-pbc-p-independent-extends-to-p-basis` and `lem-weil-pbc-p-basis-differentials-basis`. I opened both statements, checked their characteristic-p hypotheses for K/k, and checked that their coefficient field is the compositum kK^p. Step 1 has proved this equals K^p. The empty family is admissible because its sole monomial is 1, which is nonzero. Extension yields the entire monomial basis; the second node yields a basis indexed by exactly the same set I. No converse of the second node is used, and a mere existence node is not cited for a more specific construction.

Step 5 uses no new theorem: in the already established one-dimensional space it writes every differential as a scalar times v and displays the nontrivial two-term relation that forbids two indices. The empty-index case contradicts spanning of the nonzero space. Therefore I has exactly one element and dt is itself a basis. This elementary argument avoids creating a new node that would restate one clause of the item.

Step 6 explicitly bijects the finitely supported exponent families on a singleton with the integers 0 through p-1. It thus reindexes the existing basis, without requiring an additional finite-generation or separability theorem. `def-pc-field-tower` states that field degree is vector-space dimension and supplies precisely the final notation [K:K^p]=p.

For B--E I checked that all uses are statement-level, not facts hidden inside the cited proofs, and `citations.json` quotes each used statement literally. Every non-elementary input has an existing node. There are no new unsplit objects, hidden inline sublemmas, new source-tag duplicates or statement weakenings. All six proof steps are below 2000 characters. The elementary steps prove the pth-root coefficient inclusion, the singleton-index argument, and the exponent reindexing rather than merely labelling a substantive geometric assertion elementary.

Small cases checked: for C=A^1_k, K=k(u), the basis is 1,u,...,u^(p-1), and properness is absent as required; p=2 gives the two-element basis 1,u and the displayed linear relation still works with minus equal to plus. A zero-dimensional integral scheme would have zero differentials, but is excluded explicitly by dimension one. With an imperfect coefficient field, k need not lie in K^p, so the proof correctly retains algebraic closedness when making that identification. The coefficient root a=0, nonzero denominators, empty p-independent starting family and potentially infinite p-basis index set were all handled in the argument.

## Unfinished work

None in this one-level split. Existing dependencies retain their own independently tracked statuses. No Lean was written and no compilation or build tool was run.
