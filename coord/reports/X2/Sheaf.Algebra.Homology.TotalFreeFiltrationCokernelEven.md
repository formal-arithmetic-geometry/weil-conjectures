## What changed

Replaced the proof of `CochainComplex.TotalFreeFiltration.cokernel_even` without
changing its signature, context, visibility, or docstring. The proof constructs
an explicit map from the shifted first endpoint to the even cokernel, uses its
commutation equation and degreewise bijectivity to obtain a complex isomorphism,
and transports the given endpoint decomposition through shifts and coproducts.

Added `TotalFreeFiltrationEvenQuotientMap`: its lower-column restriction and
quotient components are real constructions. Its chain-map equation is fully
proved by separating horizontal and signed vertical differentials.
Added `TotalFreeFiltrationEvenQuotientBijective`: its one named open theorem
isolates the degreewise quotient calculation. These are proof-only imports of
the item; `SingleFunctors` is also a proof-only import. Public imports in the
new modules are needed by their signatures or definition bodies.

## Proved and sorry left

Closed the existing hole in
`CochainComplex.TotalFreeFiltration.cokernel_even` (1 of 1 item holes).
Its proof still depends on the following new hole, so this is a decomposition,
not a completed proof of the target import closure: one existing hole closed,
one new hole added, net zero before any pruning measured by the ledger.

Added and proved
`CochainComplex.TotalFreeFiltration.evenQuotientComponent_comm`, node
`lem-pc-derived-total-filtration-even-quotient-map`, together with
`lower_mem_odd` and its private differential calculations. There is no sorry
in this module or its explicit map definitions.

The only delivered sorry is
`CochainComplex.TotalFreeFiltration.evenQuotientComponent_bijective`, node
`lem-pc-derived-total-filtration-even-quotient-bijective`. It is the entire
proof of a public named theorem, with its source and full mathematical proof
in its docstring. It proves neither the chain-map equation nor the endpoint
coproduct reindexing, and is strictly smaller than the item.

Local compilation succeeds for all three modules. Scratch `#print axioms`
checks show only `propext`, `Classical.choice`, and `Quot.sound` for the explicit
map definitions and chain-map theorem. The bijectivity theorem and
`cokernel_even` additionally show `sorryAx`, exactly as the open hole requires.

## No longer needed

No repository imports, old proof-dependency nodes, or library modules were
pruned. The sole old dependency `lem-pc-derived-total-filtration-stable` remains
used for the concrete terms and step map. During second reading, removed the
redundant direct proof import of `TotalFreeFiltrationEvenQuotientMap` from the
item (it is publicly imported by `TotalFreeFiltrationEvenQuotientBijective`),
and the unnecessary `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`
import. Compilation still succeeds with both removed.

## Where the brief, the DAG or earlier work was wrong

The first report incorrectly listed the chain-map theorem as a remaining
sorry even though its Lean proof was already complete. It also called the
upper theorem a complete proof without identifying the one-for-one hole
replacement as a decomposition. Both descriptions are corrected here.

The delivery initially omitted the updated item node. Both new nodes used
the same generic chain-map proof text, which was incorrect for bijectivity,
and the bijectivity node omitted its dependency on the component-map node.
The second reading repairs these records and gives self-contained informal
statements while preserving the verbatim Lean statements in their Lean records.

The local unit `sk-thm-picard-f-representable` has empty `realized` entries for
its statement and step and concerns Picard representability; that inherited
unit assignment is not changed here. The filtration argument remains within
the item and its original stable-terms route, and bypasses no realized unit
node. The source's alternating filtration and differential sign were checked
against Stacks Project [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP).

## New nodes

`lem-pc-derived-total-filtration-even-quotient-map` records the explicit
quotient components' chain-map equation, now proved. Its new module is
`Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientMap`.

`lem-pc-derived-total-filtration-even-quotient-bijective` records degreewise
bijectivity of that specified map. Its new module is
`Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective`.

No existing statement or definition changes, no forced adaptations, and no
change records are needed.

## Second reading by X2

1. Compared the item with the repository by `diff`. The only changes to the
   existing module are proof imports and the body of `cokernel_even`; its
   signature, variables, visibility, and docstring are byte-for-byte unchanged.
   No other existing Lean module is delivered. Verdict: pass.
2. Compiled every delivered file through `lcompile.py`, checked the source for
   forbidden declarations and holes, and compiled scratch axiom probes. There
   is exactly one named theorem with sorry, as listed above. The explicit
   constructions choose no data from an unproved existence statement. The
   constructed quotient map and proved commutation equation use only standard
   axioms. Verdict: pass as a decomposition with one open theorem.
3. Read both new statements and their proofs. For j=0, the even term is zero
   and the odd term is the image of the injective first endpoint map. For j>0,
   earlier lower ranges lie inside their full columns; projecting to column
   -j kills the earlier-column sum and retracts the new full column, giving
   injectivity. The odd term is exactly the even term plus the new lower range,
   giving surjectivity. Zero rings and zero endpoints cause no exception;
   an empty endpoint basis also gives a zero quotient. Chain commutation needs
   no exactness and is already proved. Neither lemma restates the whole item.
   Repeated searches with Loogle, Lean Finder, and grep using different queries;
   inspected local upstream and Sheaf homology modules. Found general cokernel
   and direct-sum tools, no existing theorem for these specific filtration
   terms. `Submodule.quotientEquivDirectSum` requires finite rank and a PID and
   does not apply over an arbitrary commutative ring. Verdict: pass.
4. Read the upper proof downward: component isomorphisms, complex isomorphism,
   shift of the endpoint decomposition, coproduct preservation, and single
   degree translation. These use existing Mathlib tools. Removed the two
   redundant imports noted above and recompiled. The old stable-terms node
   remains used, and the unit's realized route is unchanged. Verdict: pass.
5. Read the item and new nodes with the Lean files open. Repaired the item
   proof and proof dependencies, the bijectivity proof description and its
   map dependency, the new nodes' self-contained informal statements, search
   records, and the stale report. Lean-record statements still match the
   corresponding declaration signatures. Verdict: pass after repairs.

Second reading changed the report, DAG proof/dependency records and informal
new-node statements, and removed two redundant proof imports. No mathematical
statement, existing docstring, definition, or already correct proof was changed.
