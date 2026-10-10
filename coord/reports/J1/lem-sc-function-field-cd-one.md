Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-function-field-cd-one.json`: repaired item, with item-level LeanSearch, LeanFinder, Loogle, and source-grep searches recorded.
- `dag/nodes/sec-curve-estimates/lem-sc-field-kummer-h2-brauer-injection.json`: statement-only helper; Mathlib searches found no match.
- `dag/nodes/sec-curve-estimates/lem-sc-brauer-algebraic-function-field-zero.json`: statement-only helper; Mathlib searches found no match.
- `dag/nodes/sec-curve-estimates/lem-sc-field-artin-schreier-sequence.json`: statement-only helper; Mathlib searches found no match.

Attachments:

- None. No sorry-free slopmaster2 declaration states the item exactly.

WANTED:

- None. The three helper nodes remain statement-only queue nodes for later proof work.

What was repaired:

- The three helper statements previously cited `def-sc-field-extension`, which defines a curve base-change map rather than a field extension. I removed that citation from all three. The Brauer helper now cites `def-pc-field-extension` for fields and `def-weil-pbc-separable-algebraic-extension` for separability, with finiteness stated inline as finite-dimensional over L; its `stmt_deps` are exactly the cited nodes.
- The Kummer helper now defines `mu_ell` inline as the kernel of the ell-th power map on the small etale site of `Spec E`, and cites `def-sc-gm-torsor` for `G_m`. I dropped the redundant assumption that E contains all ell-th roots of unity. Its `stmt_deps` now include every definition used in the statement and no removed field-extension node.
- The Artin–Schreier helper now defines `F_p` inline as the constant sheaf with value `Z/pZ` on `(Spec E)_Et`, cites `def-weil-pbc-constant-sheaf`, defines `G_a` as `(O_{Spec E})_et` using `def-sc-etale-qcoherent-module`, and names the maps `iota` and `wp` explicitly. Its statement dependencies were changed accordingly.
- I deleted the vacuous former step 3 of the item. Step 2 already cites the Brauer helper, and the split-report blueprint now says that step 2 realizes both the second and third blueprint proof paragraphs.
- I added the item-level LeanSearch, LeanFinder, Loogle, and source-grep search records for the function-field cohomological-dimension/vanishing claim. The report no longer lists `dag/units/sk-prop-h2.json`, which is not part of this delivery.

## Review by J1

I reread the item source `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/lem-sc-function-field-cd-one.md`, the three helper source paragraphs, and the cited definition nodes. The item statement remains the blueprint claim. Step 1 uses exactly the torsion filtered-union, filtered-colimit, field/discrete-module dictionary, and group-cd-one statements; their hypotheses apply to torsion etale sheaves on `Spec L` and finite separable extensions of L. Step 2 uses the Kummer helper and the Brauer helper. The Kummer statement now supplies its own field, prime-to-characteristic, `mu_ell`, and `G_m` hypotheses; the Brauer statement supplies an algebraic extension L of the curve function field and a finite-dimensional separable extension E/L. Step 3 is the characteristic-p branch and uses the field Artin–Schreier helper, affine quasi-coherent vanishing, and the group-cd-one criterion. All three steps are non-elementary and cite their dependencies; no step relies on a helper's proof text.

For the returned point B3/C4, I checked every citation in each helper statement against the cited node's statement: the Brauer field and separability citations now say exactly what the statement uses; the Kummer field and `G_m` citations define those objects; and the Artin–Schreier constant-sheaf and quasi-coherent-module citations define the sheaves on the stated site. For B3's `mu_ell` issue I verified the inline kernel definition and removed the redundant roots-of-unity hypothesis. For the Artin–Schreier issue I verified the inline definitions of `F_p`, `G_a`, `iota`, and `wp`. For C3/D1 I deleted the unsupported step and assigned both relevant blueprint paragraphs to step 2. For B9/F I recorded all four searches for the item and removed the unit file from the files-written list. I also rechecked the small edge cases: ell is distinct from `char(E)` in the Kummer branch, p is the positive characteristic in the Artin–Schreier branch, and E is finite-dimensional separable over L in the Brauer branch. Before retaining each helper I searched the DAG and whole blueprint for an existing matching statement; none existed.

What could not be finished:

- The three helper nodes are intentionally unsplit statement-only nodes, as required for a one-level stage-1 split.
