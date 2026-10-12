## What changed

Replaced the target proof with a compiled construction using two intermediate theorems:
`galoisSet_embedding_decomposition` decomposes a continuous discrete Galois action into
finite separable embedding sets, and `etaleCoproduct_embedding_points` identifies the
geometric points of the corresponding étale coproduct. The target combines their
equivariant equivalences into an isomorphism. Added the two supporting modules and
updated the target node proof dependencies. Added a change record for the proof-only
imports; the existing local instance attributes were retained unchanged.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.etaleFieldPointFunctor_essSurj` with a compiled reduction. Added one hole: `AlgebraicGeometry.etaleCoproduct_embedding_points` (node `lem-exc-etale-coproduct-embedding-points`). The new `AlgebraicGeometry.galoisSet_embedding_decomposition` has a complete Lean proof using the existing, still open `FieldTheory.finite_separable_extension_galois_classification`.

This is a decomposition: one original hole closed and one smaller hole added, net zero holes. The target and decomposition still depend on `sorryAx`; they are not axiom-free proofs of the target. No data definitions were added.

## No longer needed

The direct imports of `Sheaf.FieldTheory.EtaleFieldGaloisClassification` and
`WeilConjectures.Mathlib.RingTheory.Etale.Field` were removed from the target module;
no module was pruned. The old direct proof dependencies
`lem-exc-etale-field-galois-classification` and
`lem-weil-pbc-finite-separable-extension-etale` were replaced by the intermediate
steps, but remain transitively needed by the decomposition and étale-coproduct
theorems respectively; `lem-exc-etale-coproduct-etale` remains a direct dependency.

## Where the brief, the DAG or earlier work was wrong

The earlier blocked report was obsolete: the proof and intermediate modules compile.
The original DAG proof plan omitted explicit intermediate statements for orbit
 decomposition and coproduct point identification; these are now recorded as new nodes.

## New nodes

`lem-exc-galois-set-embedding-decomposition` and `lem-exc-etale-coproduct-embedding-points` are the strictly smaller intermediate statements used by the target proof; each has its own module and DAG node.

Change record: `coord/changes/etaleFieldPointFunctorEssSurj-imports.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof imports and the target proof body changed. Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`. There are no forbidden declarations or hollow definitions. The only remaining `sorry` is the named theorem `AlgebraicGeometry.etaleCoproduct_embedding_points`; The target depends on `sorryAx` through both `AlgebraicGeometry.etaleCoproduct_embedding_points` and the existing unproved `FieldTheory.finite_separable_extension_galois_classification`; the decomposition theorem also depends on the latter. All other reported axioms are permitted. Verdict: pass.

3. Checked the two split statements against their Lean declarations and searched the library and Mathlib records. Both are strictly smaller than the target and are needed by its proof; the coproduct point statement is the sole open hole and has its node, source, and docstring proof. Verdict: pass.

4. The proof follows the unit route through orbit decomposition, finite separable coproduct construction, and geometric-point identification. The decomposition theorem uses the existing finite Galois classification, and no unnecessary proof dependency was found. Verdict: pass.

5. The target node's proof and `proof_deps` match the imports and declarations used in the proof; the two new nodes carry matching Lean records and source metadata; the decomposition node records its use of `lem-exc-etale-field-galois-classification` in both `proof[0].uses` and `proof_deps`. Verdict: pass.

Changed during second reading: no Lean code or statements; appended this review and corrected the report's description of local instances to note that they were retained from the original module.

## Second reading by E2

1. Compared every delivered module with the repository. The sole existing module has exactly the same declaration signature, variables, public import, and local instance attributes; only its proof, proof imports, and opened namespace changed. The other two modules are new. Verdict: pass.

2. Compiled all three modules locally with lcompile.py --all, and compiled a scratch copy with #print axioms for all three delivered theorems. Only propext, Classical.choice, Quot.sound and sorryAx occur. There is exactly one delivered sorry, the named coproduct-point theorem; no forbidden declarations, definitions, or arbitrary data constructions from unproved existence statements were added. Existential witnesses from classification are used within a theorem proof to establish another existential claim, not to define library data. Verdict: pass as a decomposition, not an axiom-free target proof.

3. Read both new statements and their docstring proofs. Empty actions give an empty orbit index; each chosen orbit is nonempty, finite and transitive. Empty coproducts have no field-valued points; for one summand the point statement is the affine anti-equivalence, with the stated postcomposition action. For general indices the point factors uniquely through the open component containing its unique topological point. Searched with different queries using leanfinder (field-spectrum maps into coproducts), loogle (orbit decomposition), grep, and rg on both source roots and Mathlib. Found selfEquivSigmaOrbits', sigmaSpec and SpecToEquivOfField as tools, but no duplicate of either new statement or short direct proof of the remaining hole. The point identification is strictly smaller than essential surjectivity. Verdict: pass.

4. Followed the target reduction downward: orbit decomposition uses the existing finite classification; the prescribed coproduct uses the existing étaleness theorem; the point equivalence then produces the action isomorphism explicitly. Proof-only imports have plain import; Limits is public in the new point module because its statement uses Sigma.desc. The unit sk-prop-h2 realized record has no assignment to this item, and its route is unchanged. The report now accounts for all old direct proof edges and distinguishes replaced edges from pruned modules. Verdict: pass.

5. Checked the target node steps and dependencies against the actual proof; checked the new node signatures, sources, origin, creation records, and dependency union. Removed stale reviewed/reviewed_proof fields copied from unrelated K1 landings in the new nodes and added the missing statement dependency citations. Verdict: pass after repair.

Changed during this reading: repaired new-node metadata and statement dependency citations, corrected the proof-only import change record, and made decomposition/axiom/dependency accounting explicit in the report. No Lean code or theorem signature changed.
