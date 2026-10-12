## What changed

Proved `AlgebraicGeometry.exists_descended_qc_neighborhood_core` by expressing the base change over `A` as the inverse limit of base changes over finitely generated `k`-subalgebras. The proof uses the filtered-colimit construction for subalgebras, `isLimitOfIsPullbackOfIsConnected`, affine transition maps, and `exists_preimage_eq` for compact opens. Added proof-only imports of the inverse-limit and filtered-colimit modules.

## Proved and sorry left

The declaration `AlgebraicGeometry.exists_descended_qc_neighborhood_core` is proved with no `sorry` left (node `lem-weil-pbc-descended-qc-neighborhood-core`): one hole closed, zero holes added. No new declarations were added. The dry-run axiom probe checks the proof against the standard permitted axioms.

## No longer needed

No imports were removed. The node originally had no proof dependencies. The direct principal-open/tensor-coefficient construction in its plan is replaced by the inverse-limit argument; no existing node or module is pruned. The proof-only imports are both used. No new nodes were created.

## Where the brief, the DAG or earlier work was wrong

The DAG described a direct principal-open coefficient argument. The available inverse-limit API gives a shorter formal route for the same statement, with the same finitely generated subalgebras and compact-open conclusion.

## Second reading by N3

1. **Unchanged interface: PASS.** Compared the delivered module and node with the repository versions. The full `canonicalProjection` definition and the existing theorem signature are byte-for-byte unchanged (also checked by assertions). Only two proof-only imports, the theorem proof and its explanatory docstring differ. The node differs semantically only in `proof`, `proof_deps` and `proof_origin`. No change record or forced adaptation is needed.

2. **Proof and axioms: PASS.** Compiled the module locally through `lcompile.py`, with no errors or warnings. Compiled a scratch copy with `#print axioms` for both `AlgebraicGeometry.canonicalProjection` and `AlgebraicGeometry.exists_descended_qc_neighborhood_core`: both use exactly `propext`, `Classical.choice`, `Quot.sound`. The delivered module contains no `sorry`, prohibited declaration or hollow definition. The ring cocone, scheme diagrams, cone and natural transformations are explicit constructions; their limiting properties come from proved universal-property declarations, not arbitrary witnesses of unproved existence claims.

3. **Split statements and edge cases: PASS.** No statements or nodes are split off or added. Inspected the filtered-colimit construction and Mathlib's actual `exists_preimage_eq` signature: the latter needs a cofiltered index and affine transitions, without qcqs assumptions on the stages. Bottom supplies a stage even when no coefficients are needed. If `X_A` is empty (in particular for the zero ring `A`), the point hypothesis is impossible. For `A = k`, the diagram still contains the bottom subalgebra and the same argument works. Arbitrary non-quasi-compact or non-quasi-separated `X` is allowed: only the selected affine neighborhood is compact.

4. **Shortest route, imports and unit: PASS.** Independently searched with Lean Finder using compact-open neighborhood/base-change/inverse-limit wording, and searched `lean/Sheaf` and `lean/WeilConjectures` for descent and neighborhood formulations. The applicable result is the already used `exists_preimage_eq`; the neighboring wrapper depends on this item and cannot prove it. Other upstream spreading and descent declarations impose additional hypotheses. The two new imports are plain proof-only imports and both are used. The original public imports remain unchanged. There were no old proof dependencies to prune. Read `dag/units/sk-thm-p1.json`, including `realized`: this auxiliary node is not a realized unit step. Its replacement argument stays below the unit level; the Mathlib compact-open descent leaf is a generic tool, not a replacement for a unit step.

5. **DAG and Lean agreement: PASS.** The two recorded proof steps describe exactly the constructed filtered diagram, its limit after base change, affine transitions, the affine neighborhood and its descent. `proof_deps` names the existing Mathlib compact-open descent node `pqf-lem-limit-qc-open-descends`; its recorded Mathlib declaration is the one applied here. `proof_origin` identifies the categorical, filtered-colimit and compact-open results actually used. No old dependency is omitted from `## No longer needed` because the old list was empty.

**Changes made in the second reading:** replaced the obsolete principal-open/coefficient proof description in the theorem docstring with the actual inverse-limit argument. Normalized the sandbox node's Unicode JSON formatting without changing its data. No proof, statement, definition, import or proof-dependency repair was needed. One hole closed, zero holes added: this is a proof, not a decomposition.
