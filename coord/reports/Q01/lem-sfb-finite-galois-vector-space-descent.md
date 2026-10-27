# Stage-1 report: lem-sfb-finite-galois-vector-space-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-galois-vector-space-descent.json: existing statement, now split. Full statement retained. No new nodes and no new Mathlib leaves.
- citations.json: verbatim statement evidence for all nine step/node pairs.
- searches.jsonl: actual searches made with the required msearch.py command. Original inherited mathlib_searches retained, followed by this session's searches.
- report.md: this report. write_split.py is sandbox-only preparation, not a delivered project file.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, semilinear descent, and Galois descent found no declaration stating this equivalence. The matrix and sheaf-section declarations concern other objects or restricted cases. AlgebraicGeometry.finiteGaloisTensorDecomposition supplies an existing dependency, not an attachment for this item.

## WANTED

None. Read Milne, Algebraic Groups (2017), Appendix A.63–A.64, printed pp.580–581 (PDF pp.592–593), and 3.36, printed p.77 (PDF p.89). Also read the local Stacks sources: descent.tex, lemma-galois-descent (Tag 0CDR); fields.tex, theorem-galois-theory (Tag 09DW); and pione.tex, section-finite-etale-under-galois (Tag 03SF).

## Corrections and scope

The item originally had no proof. Milne A.64 proves the equivalence using a skew group ring and Morita equivalence; 3.36 identifies the invariant quasi-inverse. I gave a different explicit tensor calculation and marked proof_origin.by = agent, rather than attributing that calculation to Milne. It stays below the unit route: the auxiliary vector-space descent needed by the parent Hopf descent. There is no change of target or statement, and no SGA source.

The blueprint ancestor command prints None: the creation chain eventually reaches the module-name string Sheaf.SixFunctors.CtfStabilityDirectImages instead of a node id. The inherited place and via list already identify det-thm-sf-ctf-stability-direct-images, proof (3). I retain that metadata and document the broken chain in split_report instead of editing other nodes or inventing a different creation history. Read the latest blueprint's sk-thm-sf-ctf-stability/_section.md, sk-thm-sf-ctf-stability-direct-images.md and its proof.md (whose front matter identifies det-thm-sf-ctf-stability-direct-images), as well as the chapter and unit records.

## Reuse and search results

Whole-DAG searches and tools/blueprint_refs.py searches for Galois, semilinear, and vector space found no equivalent imported statement. The existing lem-exc-finite-galois-tensor-decomposition, clause (1), gives the tensor isomorphism needed here. The similarly named algebra-tensor-decomposition node instead assumes that isomorphism and proves its spectrum consequence; it cannot supply clause (1). The existing Mathlib leaf lem-weil-pbc-finite-galois-fixed-field supplies finiteness and the fixed-field assertion. Reuse avoids both a new tensor-decomposition node and a new fixed-field node. lem-sfb-galois-stable-subspace-descent concerns invariant subspaces of an already scalar-extended space; it does not state arbitrary semilinear descent. The matrix-descent node only concerns matrix spaces with a specified action.

The six new searches are two LeanFinder phrasings, Loogle for IsGalois with TensorProduct, LeanSearch for bijectivity of the canonical map, and two grep patterns (one restricted to FieldTheory). All ran successfully. Read their hits: integral-closure invariance and fixed fields do not yield arbitrary semilinear descent; representation invariants use linear, rather than semilinear, actions. TensorProduct.map_bijective assumes bijectivity of the two factors and so cannot establish the map at issue. The field-theory fixed-field source and the existing tensor theorem's source were read. No search was recorded as run without an actual invocation; pre-existing records are retained as inherited records.

## Not duplicates

No nodes created. Both substantial field-algebra tools already exist. No clauses of the item have been moved into new nodes.

## Review by Q01

I checked B–E against the actual node statements, not their titles. For the item I read Milne A.64 and 3.36 and checked that neither assumes finite dimension of the descended vector space. The finite extension is the only finiteness assumption used in the sums. Stacks 0CDR supplies compatible context, but I do not cite it as a DAG dependency or assert that its quasi-coherent formulation immediately gives the explicit vector-space maps.

Step 1 takes finiteness and fixed field exactly from lem-weil-pbc-finite-galois-fixed-field. Clause (1) of lem-exc-finite-galois-tensor-decomposition explicitly gives an isomorphism a tensor b maps to (a q(b))_q, so its inverse on the identity delta function gives the required finite coefficients. I verified the factor order by renaming its base L to k and E to L. The tensor-product definition explicitly supplies finite generation by pure tensors and the universal property. Reindexing tau sigma proves that T_b(v) is invariant. No sheaf clause of the tensor node is used.

Step 2 cites the same tensor definition and fixed-field assertion. The two inverse calculations are written out: theta S = id by the delta coefficients, and S theta = id by the weighted traces. The trace is fixed by reindexing, which is the exact reason balancing over k is valid. Equivariance and naturality are checked by their pure-tensor formulas. S is initially only additive; its L-linearity follows from its being inverse to the L-linear theta. There is no unproved assertion that the individual T_b are L-linear.

Step 3 again uses fixed field only to put trace values in k and the tensor definition to construct P. Summing the delta identities produces a trace-one t without assuming that the group order is invertible. On a pure tensor the formula 1 tensor P(z) = sum sigma(t) sigma(z) follows by expanding trace; only after this check is z assumed invariant. This proves both inverse identities for eta without invoking basis existence, tensor exactness, or preservation of invariants by arbitrary tensor products.

Step 4 uses only the tensor functoriality explicitly in its definition node and the established formulas. Both triangle identities are displayed. Step 5 constructs the inverse on Hom explicitly from eta, and L-linearity plus tensor generation proves the required equality with 1 tensor f. Thus the equivalence, named theta and eta, naturality, equivariance, and Hom clauses are all proved.

I tested the proof at L=k (one group element), U=0, V=0, infinite-dimensional U and V, and a finite Galois extension of characteristic p with p dividing the group order. The weighted-trace construction still works in the last case, whereas unweighted averaging by division by the order would not. The coefficient family cannot be empty because it maps to a delta function with value 1. All objects are introduced and all hypotheses of the existing nodes hold. All steps are under 1100 characters; none hides a >2000-character lemma. Non-elementary input consists precisely of the two existing field-algebra results, with the off-unit tensor theorem declared as a generic tool in split_report.tool_uses. No new self-contained statement needs searching or sourcing.

## Unfinished

No mathematical clause remains unfinished in this stage-1 split. Lean writing and compilation are outside this assignment. The maintainer's independent review follows delivery.
