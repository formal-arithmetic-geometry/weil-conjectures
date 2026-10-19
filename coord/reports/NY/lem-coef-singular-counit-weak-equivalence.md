# Stage-1 report: lem-coef-singular-counit-weak-equivalence

Files written:

- `lem-coef-singular-counit-weak-equivalence.json`: statement node, zero new nodes; Mathlib searches found no matching counit theorem.
- `citations.json`: citations for every proof-step use.

Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item, and the existing `lem-cbc-realization-singular-unit-weak` is the converse unit statement rather than an attachment.

WANTED: Hovey, *Model Categories*, Theorem 3.6.7 (printed p. 99), or Goerss--Jardine, *Simplicial Homotopy Theory*, Ch. I.11, as an archived reference for the singular-realization counit theorem and its explicit homotopy-group calculation.

The imported statement is retained verbatim. The proof is written as an agent proof because the blueprint explicitly identifies the Milnor input as agent-formulated and no archived source is present. I used the existing DAG topology statements rather than creating clause-sized duplicate nodes. The Mathlib searches were rerun with `msearch.py`; they found only `sSetTopAdj` and characteristic-simplex declarations, not this weak-equivalence assertion.

## Review by NY

I read the item node, its parent blueprint proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, the `sk-prop-sf-biduality-general` unit record, and the chapter record. I also read the full statements of every cited node: `def-cbc-enhanced-diagrams-cones`, `lem-coef-realization-finite-limits`, `lem-coef-simplicial-realization-cylinder`, `lem-coef-kan-realization-serre`, `lem-coef-compact-open-currying`, and `lem-coef-homotopy-equivalence-weak`.

Step 1 uses only the realization quotient and affine-coordinate relation in `def-cbc-enhanced-diagrams-cones`; this proves the simplicial identities, well-defined evaluation, continuity, naturality, and the universe bound. Step 2 uses the realized horn-pair homeomorphism stated by `lem-coef-realization-finite-limits`; I explicitly glue a simplicial horn to a continuous map through the quotient, so no k-space hypothesis is silently imposed on the arbitrary space `T`. The retraction supplies fillers for all dimensions and both outer horns. Step 3 uses the cubical homotopy convention from `def-cbc-enhanced-diagrams-cones` and the exact cylinder homeomorphism of `lem-coef-simplicial-realization-cylinder` to identify pointed singular representatives and boundary-fixed continuous maps, including their homotopies and concatenation.

Step 4 applies the Kan-complex realization comparison in `lem-coef-kan-realization-serre` after Step 2. Its statement gives both the component comparison and the isomorphism from simplicial homotopy groups to realized homotopy groups; evaluating a representative is exactly the map `a(z)`, so the comparison is the desired evaluation map at constant singular vertices. Step 5 checks every hypothesis of `lem-coef-compact-open-currying` with the compact interval and uses its transpose/evaluation continuity to make the attached-interval homotopies joint and continuous. Step 6 applies `lem-coef-homotopy-equivalence-weak` to the four explicitly homotopy-equivalent attached spaces; the two strict commutative squares then cancel the basepoint-change maps and transfer the isomorphism from a singular vertex to every point of the realization. Step 7 handles the empty space and matches the component and all-based-group clauses with the weak-equivalence convention in `def-cbc-enhanced-diagrams-cones`.

I checked the empty case, a point, a path-connected interval, a disconnected two-point space, and an arbitrary source point lying in the interior of a singular simplex. There are no new nodes, no duplicate split, no cycles, and no SGA citations. The five off-unit topology nodes are declared in `split_report.tool_uses` because they are generic black-box topology inputs and the biduality unit has no replacement statements for them.

What could not be finished: no Lean code or compilation was authorized in this stage; the Mathlib theorem itself is absent, so the result remains a natural-language stage-1 split.
