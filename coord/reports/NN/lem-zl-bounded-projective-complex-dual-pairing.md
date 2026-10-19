1. Files written:

- `dag/nodes/sec-zeta-weil/lem-zl-bounded-projective-complex-dual-pairing.json`: statement node, split; one new unsplit dependency, no Mathlib leaf.
- `dag/nodes/sec-zeta-weil/lem-zl-finite-projective-module-dual-pairing.json`: statement node, unsplit; no exact Mathlib match.
- `citations.json`: verbatim citations for every proof-step dependency.

2. Attachments: none.

3. WANTED: none.

4. I found no statement error. The imported item has no Lean declaration in the source checkout. The exact source is Stacks Tag 0FNK (More on Algebra, `lemma-left-dual-complex`), whose converse is the construction in this item; the finite-projective module input is Stacks Tag 0FNV (Modules, `example-dual`) together with the finite-projective characterization in Tag 0FNJ. Mathlib has only the separate general facts `Module.dual_projective`, `Module.dual_finite`, and field-only `FGModuleCat` rigid pairings, so the commutative-ring tensor--End isomorphism and triangle identities remain an unsplit DAG node.

## Review by NN

I read the item node, its unit `sk-prop-smooth-proper-purity`, the chapter record, and the Stacks source around Tags 0FNK, 0FNJ, and 0FNV. I also searched the whole DAG and blueprint for finite-projective duality and found no duplicate; the closest existing node, `lem-pod-projective-hom-evaluation-model`, concerns derived Hom from bounded-above projective complexes and does not state coevaluation or triangle identities, so it is not a substitute. The new module-level node states exactly the finite-projective evaluation, coevaluation, finite-projective dual, and both triangles from the source.

Step 1 uses that node for finite projectivity of each `Hom_A(P^{-n},A)` and uses only the given interval bound for support. Step 2 uses the definition of a cochain complex and writes the sign product and the composite of consecutive differentials explicitly; it is elementary once the displayed differential is unfolded. Step 3 uses the tensor-complex definition for the signed direct-sum differential and the module node for the identity tensor defining coevaluation. It checks the evaluation cancellation on a homogeneous element and records the adjacent-degree cancellation relation for coevaluation. Step 4 uses the two module triangle identities componentwise; the tensor definition supplies the direct-sum grading and canonical reassociation. Step 5 checks the zero and one-term boundary cases against the same module statement. Every cited sentence is copied verbatim in `citations.json`, and all cited nodes occur in `proof_deps`.

I ran LeanFinder, Loogle, LeanSearch, and Mathlib grep searches through `msearch.py` for the new node (including a second phrasing); the searches are recorded in its `mathlib_searches` and in the sandbox search log. No compiler or Lean build was run, per the stage-1 restriction.

5. Nothing remains unfinished in this split.

## Not duplicates

lem-zl-finite-projective-module-dual-pairing vs lem-zl-bounded-projective-complex-dual-pairing: the new node is the single-module evaluation/coevaluation lemma, while the existing item is the bounded cochain-complex construction with signed Hom differential and total-complex chain maps.
lem-zl-finite-projective-module-dual-pairing vs lem-sc-picard-tensor-dual-comparison-iso: the existing node concerns pullback of a finite locally free sheaf and invertibility of a specified base-change morphism; the new node concerns a module over one ring and its tensor-End dual pairing.
lem-zl-finite-projective-module-dual-pairing vs lem-ag-dual-tensor-hom-comparison: the existing node identifies two sheaf-level tensor-Hom morphisms for arbitrary sheaves; it does not assert finite projectivity, the tensor-End isomorphism, or triangle identities for a ring module.
lem-zl-finite-projective-module-dual-pairing vs lem-ag-finite-locally-free-dual-pairing: the existing node is a scheme-level finite locally free sheaf ExactPairing with sheaf tensor order and sheaf dual; the new node is the explicit affine ring-module tensor-End isomorphism and its elementwise evaluation/coevaluation.
lem-zl-finite-projective-module-dual-pairing vs lem-ag-pullback-dual-finite-locally-free: the existing node is a pullback comparison for sheaf duals; it contains no evaluation, coevaluation, finite-projective conclusion, or triangle identity.
lem-zl-finite-projective-module-dual-pairing vs lem-ag-tangent-along-section-pullback: the existing node identifies tangent sheaves after pullback along a smooth section; it is unrelated to the ring-module dual pairing asserted here.
