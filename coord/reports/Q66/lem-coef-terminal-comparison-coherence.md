# Q66 stage-1 report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-terminal-comparison-coherence.json`: split statement, eight proof steps; exact original statement retained.
- `dag/nodes/sec-six-functors/lem-coef-triangular-top-deletion-anodyne.json`: one new unsplit statement node, no Mathlib match.
- `citations.json`: verbatim statement quotations for every cited node at every step.

## Attachments

No attachment. Searches for the blueprint tag and terminal-comparison, terminal-triangle and interval-poset notions in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration proving the item. Ordinary categorical terminalComparison results do not state it. Upstream master is reference material, not proof evidence.

## Literature

WANTED: none required for this agent-written split. I read `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, together with the item, its ancestry, the chapter record and `sk-prop-sf-biduality-general` unit. The blueprint motivates coherent terminal comparisons only through that ancestry; its displayed proof is a derived coefficient-adjunction calculation, not a proof of this simplicial assertion. The particular finite-poset anodyne assertion is an agent-written combinatorial auxiliary, not an assertion attributed to HTT or Cisinski. Existing nodes supply the marked-anodyne class and its pushout-product theorem. There is no Stacks tag for this finite combinatorial assertion, and no SGA source is used.

## Corrections

The prior sandbox's dry run passed, but its general pullback claims were not in the statement of `lem-coef-infinity-cartesian-fibration-pullback`: that node treats a pullback of two cartesian fibrations over a common intermediary under an isofibration hypothesis. The text also mentioned `lem-coef-relative-marked-anodyne-calculus` without citing it. That latter node would give the desired interfaces but creates a dependency cycle through coherent-nerve comparison and this item's ancestors. I removed both uses. The repaired proof checks each marked-anodyne generating family using existing statements and definitions, then handles arbitrary base change by directly pairing horn fillers. Proper faces are handled over the same ambient fibration and a restricted base simplex; this avoids needing reflection of cartesian edges under base change.

## Not duplicates

`lem-coef-triangular-top-deletion-anodyne` vs `lem-coef-marked-anodyne-lifting-calculus`: the new statement is the specific interval-nerve inclusion after deleting `(n,n)`; the existing statement defines the general class and supplies its product calculus, without asserting this inclusion is in it.

`lem-coef-triangular-top-deletion-anodyne` vs `lem-coef-marked-triangle-cancellation`: the latter concerns adding one marking on a two-simplex with two specified marked edges, not the interval-poset inclusion.

`lem-coef-triangular-top-deletion-anodyne` vs `lem-coef-relative-marked-anodyne-calculus`: the latter characterizes fibrations and proves generic relative mapping and pullback assertions; it does not assert the finite interval-poset inclusion is anodyne.

DAG-wide searches for interval-poset, top-diagonal deletion and marked-anodyne notions, and whole-blueprint searches for interval and terminal comparison, supplied no existing statement of this finite inclusion. The blueprint search returns coefficient Tor-interval results, which have different objects and conclusions. The new lemma is purely combinatorial: it does not restate boundary-extension or contractibility clauses of the item. Its proof is deliberately not supplied in its statement-only node.

## Review by Q66

I read delivery-errors B through E with the node files and source paragraph open. The item's statement remains verbatim, including the fixed parameter-diagonal condition, empty B_0, arbitrary cartesian transport, and the final pullback clause. The auxiliary introduces all finite posets, index subsets, nerves and markings itself, with definition dependencies that actually define those notions. Its provenance and Mathlib searches from the earlier attempt are preserved. I read the recorded hits: ordinary nerves and strict Segal nerves, horn combinatorics and pairings, and unmarked Quillen anodyne extensions do not supply this selectively marked interval inclusion. The logs include LeanFinder with two phrasings, LeanSearch, Loogle and grep; none is claimed unavailable or to match contrary to its result.

Step 1 uses the nerve definition in `def-cbc-enhanced-diagrams-cones`: its decomposition follows by checking the two coordinates of a chain ending at (n,n). The strengthened ambient-simplex formulation is an internal proof device and makes the face argument uniform. Step 2 uses all four generating families stated in `lem-coef-marked-anodyne-lifting-calculus`. I checked innerness, final-horn lifting and target-prescribed lifts against `def-coef-infinity-fibrations`. The cocartesian-composition statement gives exactly the cartesian consecutive-edge composition rule after reversing simplex order. The core-Kan statement says every edge of a Kan complex is an equivalence; simplicial maps preserve its inverse-triangle witnesses. The relative outer-horn theorem then makes their images cartesian. Its total and base quasicategory hypotheses hold throughout. Closure of the lifting property under pushouts, ordinal composites and retracts is written out. Each generator therefore has an actual cited justification, without invoking the cyclic relative-calculus node.

Step 3 uses the auxiliary's exact inclusion D_n into Y_n, and the pushout-product clause of the marked-anodyne calculus. Minimal parameter markings impose precisely row conditions at parameter vertices, as required by the statement. Step 4 uses the horn definition to see the strict fibre is a quasicategory, and the exact statement of `lem-cbc-terminal-boundary-extension` to fill boundaries with last vertex t_n. Every newly attached nondegenerate product simplex has last column coordinate n; all vertices were already defined. Newly added edges in that column cannot be new required row edges. The finite dimension induction retains all intersections and parameter boundaries.

Step 5 uses the exact boundary-lifting definition of a trivial Kan fibration, including m=0. For n=0 the fixed full parameter strip forces the unique constant diagram. Step 6 only applies the already proved generalized lifting statement to proper faces, using the same E and S and the restricted base simplex: no theorem about detecting cartesian edges under pullback is assumed. Increasing subset cardinality gives exactly the proper-face intersection, so the glued maps agree. Step 7 uses, separately, the stated lifting-against-monomorphisms theorem for horns, the section-and-simplicial-homotopy theorem, and the simplicial-homotopy-equivalence-to-weak-equivalence theorem. These imply nonempty contractible Kan complexes in the convention of the item. Step 8 uses only the horn definitions: pair a filler with its prescribed base simplex, first for innerness and then for cartesian edges and prescribed-target lifts. The ordinal nerve is a quasicategory, hence the pulled-back total space is too; the strict fibres are literally the original fibres. Applying the proved result to that fibration establishes the final clause without asserting pullback reflection.

Small cases checked: n=0 gives two points, n=1 gives a chosen cartesian lift followed by a map to the terminal object in the last fibre, and empty parameter boundary gives existence. The retained finite-filtration script succeeds for n=1 through n=5 (all chains added and all required row markings obtained); this is a finite sanity check, not a proof for every n. Nonterminal transports are permitted, since no transported object is ever declared terminal. An empty fibre cannot have the chosen terminal object, so is excluded by an actual hypothesis. Repeated base vertices and degenerate base edges cause no change in the horn arguments. All eight steps are shorter than 2000 characters; their cited statements were read and their exact quotations regenerated. No new node moves an item clause into a renamed theorem. No Lean files, compiler, Lake, live repository, or launcher files were modified.

## Unfinished

No split work remains beyond the independent maintainer review. The auxiliary is unsplit, as a newly created stage-1 node must be.
