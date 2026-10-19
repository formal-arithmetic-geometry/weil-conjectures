# Q59 repair: lem-sf-unbounded-compact-support-proper-composition

## Files written

- `dag/nodes/sec-six-functors/lem-sf-unbounded-compact-support-proper-composition.json`: repaired split; statement, statement dependencies, Lean record, and the first five proof steps are unchanged from the retained work.
- `dag/nodes/sec-six-functors/lem-sf-unbounded-proper-open-grid-comparison-transport.json`: retained statement-only unsplit lemma for the distinct six-square structural-compositor equation.
- `citations.json`: rebuilt with one verbatim statement quotation for each current citation.
- `report.md`: this repair report.

The three duplicate helper files for horizontal pasting, vertical pasting, and generic naturality were removed from this delivery. Their arguments are now cited from the existing ordinary-etale interchange node and the existing Mathlib whisker-exchange leaf. The retained search records in `searches.jsonl` are unchanged and remain available for the retained transport node and the earlier audit.

## Attachments

None. The read-only project search found no sorry-free declaration proving the complete item with its specified K-injective map, all-refinement coherence, compactification independence, and ordinary unbounded small-etale scope.

## WANTED:

None. The Stacks sources used by the split are present locally.

## Fault repaired

The return identified C5 duplication of the two extracted pasting clauses and the generic whisker-exchange leaf, B2 because the extracted pasting statements did not define `H'`, and C4/F2 stale step references. I deleted those three nodes rather than repairing duplicate statements. Steps 6 and 8 now use the existing `lem-amb-unbounded-proper-open-interchange`, whose statement already gives both horizontal and vertical pasting laws for ordinary unbounded small-etale categories. Step 7 and step 8 use the existing Mathlib leaf `lem-amb-natural-transformation-whisker-exchange`. The only newly retained node is the genuinely distinct compositor-transport statement; it assumes the grid equation and spells out the kappa and open-compositor factors. The item now has eleven consistently numbered steps: step 9 is transport, step 10 is common-refinement cancellation, and step 11 is final naturality.

## Review by Q59

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B--E. I compared the retained item against the current shared item: the statement, statement dependencies, Lean record, chapter, unit, blueprint ancestry, and first five steps are identical; the repair changes only the proof tail, proof dependencies, split report, citations, and retained child set. No Lean file, compiler, live repository, or launcher file was written.

I reread Stacks `literature/stacks-project/more-etale.tex` at Tags 0F7B, 0F7C, 0F7D, 0F7H, 0F7I, and 0F7J. Steps 1--5 retain the geometric and coefficient checks, the K-injective refinement map, refinement cocycle, identity compactification normalization, and compatible-tower construction from the retained repair. For each of those steps I reopened every cited node statement and verified that its hypotheses and conclusion supply exactly the fact used; citations.json preserves the corresponding verbatim quotations.

Step 6 uses the compatible-tower statement for the proper maps and seven commuting equations, then uses the existing interchange statement's horizontal and vertical pasting clauses. That interchange statement has the same finite-ring ordinary small-etale unbounded category, proper vertical maps, open horizontal maps, canonical direct-image/open-extension compositors, and no Cartesian hypothesis. It therefore supplies both displayed identities without a new helper or an undefined `H'`.

Step 7 uses the existing Mathlib leaf `lem-amb-natural-transformation-whisker-exchange`, whose statement is the categorical identity `(K η) ∘ (θ F) = (θ G) ∘ (H η)`. Instantiating it with the two normalized transformations gives the displayed `gamma_B`/`gamma_A` equality. Step 8 is the direct substitution and associativity calculation from the two existing pasting formulas and that whisker identity; the current citations quote both source statements.

Step 9 uses the retained transport node. I checked its complete statement: it introduces all schemes, finite coefficient ring, open/proper maps, tower refinement equations, normalized transformations, direct-image compositors, open compositors, and the exact equation `C_gf D_2 = D_1 (C_g F_f,1) (F_g,2 C_f)`. The node is strictly smaller than the item because it concerns two fixed compatible towers and assumes the grid equation; it does not assert compactification independence or the final composition comparison. Steps 10 and 11 then use the common-refinement clause and the already established cocycle/naturality calculations. All uses have matching verbatim citations, and the union of uses equals `proof_deps`.

I checked C1--C4 by opening every current cited statement and checking all 26 citation entries (including the two existing paste-law quotes and the Mathlib whisker quote) as exact substrings. I checked C5 by searching the whole DAG and blueprint before retaining the transport node. The removed horizontal/vertical nodes duplicate the existing interchange clauses, and the removed naturality node duplicates the existing generic whisker leaf. The surviving transport node is not a restatement of the item or of those clauses. There is no dependency cycle, no off-unit route substitution beyond the declared generic tools, and no SGA citation.

I checked B2 and E1--E7 on identity refinements, identity opens, empty schemes, zero complexes, and non-Cartesian refinement squares. The displayed transformations reduce to identities or zero maps in those cases, and all source/target composites remain defined. Every non-elementary current proof step is under 2000 characters. No statement dispute or source error was found.

## Not duplicates

- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-amb-unbounded-proper-open-interchange`: the existing node gives one-square normalized maps and their horizontal/vertical pasting laws; the retained node assumes a six-square grid and identifies its transport through explicit kappa and open-compositor factors between two compatible compactification towers.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-sfb-proper-open-tower-derived-unit`: the existing node compares resolution-unit paths for one fixed tower; the retained node compares two tower refinements and concludes the displayed `C_gf D_2` equation.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-sf-ambient-proper-open-pasting`: the existing node is a pro-etale/semilinear clopen-mate construction over l-adic coefficient systems; the retained node is ordinary small-etale unbounded finite-ring transport and has no clopen mate or semilinear system.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-sf-unbounded-compact-support-proper-composition`: the item ranges over arbitrary compactification choices and proves the global composition comparison; the retained node concerns one fixed pair of compatible towers and only the local refinement equation.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-weil-pbc-etale-shriek-qcqs-composition`: the existing node gives a bounded-below qcqs composition existence/isomorphism; the retained node gives a fixed-tower unbounded refinement equation with named kappa and mu factors.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-sfb-quasifinite-compact-support-exact`: the existing node concerns quasi-finite compact-support exactness and existence of a functor package; the retained node concerns arbitrary proper refinement maps and a six-square transport identity.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `sk-lem-geo-affine-local`: the existing node concerns affine pro-etale exceptional adjunction and local purity; the retained node concerns ordinary small-etale derived direct-image and extension-by-zero compositors.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-sf-compact-coefficient-composition`: the existing node compares coefficient changes on bounded constructible inputs; the retained node has one finite coefficient ring, arbitrary unbounded inputs, and no coefficient-change morphism.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-sf-composition-projection-mate`: the existing node is a tensor/projection-mate identity; the retained node has no tensor or projection map and transports a refinement grid.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-amb-shriek-open-exchange-adjoint`: the existing node is the adjoint exchange for one proper/open square; the retained node is the two-tower equation obtained after a six-square grid and explicit structural compositors.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-amb-shriek-tensor-composition`: the existing node concerns tensor compact-support composition; the retained node concerns fixed-coefficient ordinary-etale refinement transport and contains no tensor.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-amb-unbounded-compact-support-comparisons`: the existing node packages global compactification comparisons; the retained node is the local fixed-tower equation used to prove composition compatibility.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-cbc-compactifiable-compatible-tower`: the existing node supplies geometric compatible towers and common refinements; the retained node adds the derived six-square compositor equation.
- `lem-sf-unbounded-proper-open-grid-comparison-transport` vs `lem-weil-pbc-compatible-compactification-triangle`: the existing node constructs one compatible geometric triangle; the retained node assumes two complete towers and states the derived structural-compositor transport equation between their normalized maps.
