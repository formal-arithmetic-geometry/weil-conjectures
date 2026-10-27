# Q62: lem-trf-finite-free-total-tensor-model

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-free-total-tensor-model.json: statement item, split into five steps; not a Mathlib leaf. Preserved the complete statement, source and blueprint ancestry.
- citations.json: eight verbatim statement quotations, covering every use in every proof step.
- searches.jsonl: actual msearch log. Added the five searches from this session to the item without deleting its prior seven searches.
- report.md: this report and direct-delivery self-review.

No new nodes and no new Mathlib leaves. The existing tensor-basis and finite-free-flat leaves are reused.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the finite-free/tensor/total notions. PerfectDerivedTensor has a bounded strictly-perfect sheaf result, FiniteRetractTensorComplexTerms gives coherence of tensor terms, and the generic KFlat source gives bounded-above flat K-flatness. None states every clause of this ordinary-module item, particularly the explicit finite tensor basis and the bounded-above case with no lower bound. The existing module K-flat node already records the applicable upstream declaration; no new attachment is claimed.

## WANTED

None: the source files needed for this calculation are present.

## Problems found and changes

The statement is correct. Stacks Tag 0DJE, more-algebra-lemma-tensor-pseudo-coherent, displays the total tensor of finite-free models but leaves the present coordinate and support calculation implicit. The item had no proof. I wrote that argument explicitly and used the module version of bounded-flat K-flatness instead of introducing another sheaf or abstract-category variant. For the derived comparison I specialized the existing derived-second-factor functor to the identity ring map and the identity resolution. No coefficient category or target statement was changed.

The latest blueprint's lem-trf-local-term-locality and its proof, and the latest sk-i-curve-zero statement, were read. This item is the algebraic auxiliary at the end of the existing long ancestor chain, not the key unit theorem; its local finite-free model calculation does not replace any geometric unit step. Its existing blueprint.from.place is specific and retained. Blueprint searches for finite free total tensor and tensor product free basis found no identical imported node. The bounded-above flat search found the geometric replacement lemma, whose conclusion is not this item.

## Unfinished work

None for this one-level split. No Lean was written and no compiler, Lake or build was run. The server review_split check passed before the delivery dry run.

## Not duplicates

No new nodes were created. Reused lem-sc-tensor-product-free-basis, lem-sc-affine-standard-cover-finite-free-local-fp-flat, lem-pc-module-bounded-flat-kflat and lem-pc-derived-tensor-second-factor-functor rather than recreating their assertions. The item is strictly more than any of these: it assembles the coordinate basis, both support bounds and the natural derived comparison for the given complexes.

## Review by Q62

I read more-algebra.tex at Tag 0DJE (lemma-tensor-pseudo-coherent), Tag 06XZ (definition-K-flat), Tag 064K (lemma-derived-tor-quasi-isomorphism), and the K-flat derived-tensor construction preceding and underlying Tag 06Y6. I also read algebra.tex at Tag 00NX (lemma-finite-projective) for finite-free flatness and Mathlib/LinearAlgebra/TensorProduct/Basis.lean:38–58 for the actual tensor basis. These sources use a commutative ring; the item's ring is commutative. The finite total-degree interval is obtained from upper term bounds, not from a cohomological bound. No Noetherian assumption is needed. There are no new-node sources to check.

For step 1 I opened def-pc-tensor-complex-sheaves: its statement supplies the direct-sum terms, signed differential and functoriality. Its module specialization is on the one-point site, as explicitly allowed in the existing module K-flat definition and derived-functor node. The inference that zero factors yield zero tensors is written from pure-tensor generators; the finite interval and the upper-bound inequality are elementary. This is not an appeal to a hidden totalization finiteness lemma.

For step 2 I opened lem-sc-tensor-product-free-basis and def-weil-pbc-free-module. The former really states that the products of the two given finite bases are a tensor basis; it does not claim the direct-sum assertion. The proof therefore proves that assertion itself by expanding coordinates and then projecting any relation to each summand. The definition node supplies precisely the unique finite-linear-combination criterion being verified. Finiteness follows from a finite interval and finite products/unions, so a new direct-sum basis node would be elementary duplication. This step is marked non-elementary because it invokes the existing tensor-basis theorem.

For step 3 I opened lem-sc-affine-standard-cover-finite-free-local-fp-flat, lem-pc-module-bounded-flat-kflat and def-pc-module-kflat-complex. The first states flatness for any finite-free module, regardless of locality suggested by its id. The second states the acyclic total-tensor criterion for bounded-above flat ordinary-module complexes, not just a definition of flatness. The third identifies exactly that criterion with module K-flatness. The upper bounds required for applying the theorem are c, d and c+d, with the last already proved. All three applications are to complexes over the same ring. This avoids using the sheaf-only bounded-flat node or the abstract categorical theorem with extra colimit hypotheses.

For step 4 I opened the entire statement of lem-pc-derived-tensor-second-factor-functor. Clause (2) says the derived functor is computed by every K-flat resolution and gives the canonical comparison; the identity F to F is such a resolution after step 3. Clause (3) represents maps in the other variable by Tot(1 tensor u) and supplies its naturality. Inverting the comparison gives exactly the item's displayed direction in D(R), and no degreewise substitute is used for that derived isomorphism. The two off-unit statement nodes are declared as generic tool uses in split_report; both are algebra tools and do not change the trace-formula route. Step 5 again uses the actual direct-sum definition: if p+q is less than e+f at least one factor is zero. This proves the lower bound without asserting it from a source which only states an upper bound.

I tested empty intervals (k>c+d), the endpoint k=c+d (only p=c, q=d), zero complexes, empty term bases, and the zero ring. The basis proof uses uniqueness of coefficients and never divides or assumes 1 is nonzero, so it remains valid over the zero ring, even for a nonempty chosen basis of a zero module. If both inputs are bounded, the support is contained in [e+f,c+d]; incompatible input bounds simply give a zero complex. Unboundedness below causes no infinite basis in a fixed degree, because the two upper bounds still leave only finitely many contributing p. All five proof steps are below 2000 characters and none hides a standard lemma or a new independent comparison. The item statement was not corrected or weakened. I checked B–E against the actual files and source statements, not only against the server diagnostics.
