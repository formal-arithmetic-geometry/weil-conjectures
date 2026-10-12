## What changed

Added two intermediate modules splitting the affine comparison into construction of a compatible linear map and proof that such a map is bijective. The target module imports them and combines their results with `LinearEquiv.ofBijective`.

## Proved and sorry left

The target theorem `AlgebraicGeometry.relativeDifferentials_affine_sections` is proved. The intermediate declarations `AlgebraicGeometry.relativeDifferentials_affine_sections_map` and `AlgebraicGeometry.relativeDifferentials_affine_sections_map_bijective` remain as named sorries, with DAG nodes of the same names.

## No longer needed

No imports or existing proof-dependency nodes were removed; the two new nodes replace the original direct proof route and are the only additional dependencies.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the substantial construction and bijectivity arguments, so they were split into two strictly simpler intermediate statements.

## New nodes

`lem-sc-relative-differentials-affine-sections-map` and `lem-sc-relative-differentials-affine-sections-map-bijective` are new intermediate nodes; their modules and node records are included in this delivery.

## Second reading by B3

1. **Statement identity:** Compared the delivered target module with the repository version. The target theorem signature and all existing declaration signatures are byte-for-byte unchanged; only its proof and proof-only imports were added. Verdict: pass.
2. **Compilation and proof audit:** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The two intentionally split intermediate theorems are the only remaining named sorries and each has a matching DAG node. Verdict: pass.
3. **Split statements:** Checked both split statements against the affine comparison argument. The map theorem constructs exactly the linear map needed by the target, and the bijectivity theorem adds only the missing bijectivity conclusion for such a compatible map; neither restates the parent equivalence theorem. Their docstrings identify the source and their nodes record proof plans and dependencies. Verdict: pass.
4. **Pruning and route:** The target uses both split declarations through `LinearEquiv.ofBijective`; no existing import or proof dependency was unused, and no shorter available declaration was found in the imported library. The unit route remains represented by the parent node and its two proof steps. Verdict: pass.
5. **DAG and delivery consistency:** Verified that declarations, statements, modules, node records, and report entries agree, including `proof`, `proof_deps`, `proof_origin`, and split status. Verdict: pass.

Changed in this second reading: added the required second-reading audit to this report and its delivery copy; no Lean statements or proofs required repair.

