## Files written

- `dag/nodes/sec-trace-formula/lem-trf-double-evaluation-finite-components.json`: statement item, now split into nine steps. The full comparison is not a Mathlib leaf; no new nodes or Mathlib leaves are introduced.
- `citations.json`: one verbatim quotation from the live statement for every cited node in every step.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id and double-evaluation/double-Hom terminology found no declaration stating this item. Existing internal Hom and tensor-Hom adjunction infrastructure does not assert this degreewise double-evaluation isomorphism. No Lean was written or compiled.

## WANTED

None. The source needed is present locally.

## Corrections and scope

The mathematical statement is unchanged. Definition references were added for a finite basis and the ordinary module tensor product. The original empty proof has been replaced by the finite-support proof from Stacks Tag 0A68, `lemma-internal-hom-evaluate-isomorphism`, case (2), with explicit finite-free inverse calculations. This special case needs neither injectivity nor a derived comparison; the separate signed-derived-model item is not used. The whole derived evaluation theorem would therefore be an inappropriate citation for the work done here.

The chapter and unit were read: `sec-trace-formula` and `sk-i-curve-zero`. This item is an algebraic auxiliary several levels below the local-term-locality branch, not the unit's key statement. Its existing blueprint ancestor and full via chain are preserved. No chapter or unit file is changed.

## Not duplicates

There are no new nodes. Whole-blueprint searches for `double evaluation`, `finite-support`, and `Hom(Hom`, and DAG searches by evaluation terminology and Tag 0A68 found no blueprint node stating this item. The other four 0A68 nodes describe the canonical derived map, its signed derived model, or the derived isomorphism under perfect/pseudo-coherent hypotheses; none replaces this calculation. The finite-product tensor distribution is already `lem-weil-pbc-tensor-finite-product`, and is cited rather than recreated.

## Mathlib search results

The six searches run for Q90 are preserved exactly in `searches.jsonl` and appended to the inherited item search records. LeanSearch, Loogle, two differently phrased LeanFinder searches, and two source searches all returned results. I read the returned hits. `HomologicalComplex.double` and its corepresentability declarations concern a two-term complex, not iterated Hom evaluation. Tensor totalization declarations only construct the tensor total complex. I read `Mathlib/LinearAlgebra/Contraction.lean` lines 163--189: `dualTensorHomEquivOfBasis` identifies the dual of a finite free module tensored with another module with ordinary Hom; it does not directly identify the double Hom here or prove the support bounds. It would take several additional comparisons, so it is not a one-line specialization for this item. The existing `TensorProduct.piLeft` leaf states exactly the distribution used in step 3.

## Review by Q90

I read the entire proof of Stacks Tag 0A68 in `literature/stacks-project/more-algebra.tex`, especially its displays for the components c_{p,r,s} and its last paragraph bounding p, r, s in case (2). The source uses finite projectives; this item's finite-free specialization permits the explicitly requested basis inverse. I read each cited DAG statement itself, not its proof, and copied it verbatim into citations.json. No new node requires a source audit.

Step 1 is integer arithmetic: substituting p+r+s=n gives both stated lower bounds; the finite integer box also bounds p. No vanishing theorem or finiteness lemma is hidden here. Step 2 uses exactly the product formula in `def-sc-module-total-hom-complex`; the zero terms follow from the hypotheses on P and J. Projection and zero extension are inverse on every coordinate, and the finite product/direct-sum conversion is written out. Step 3 uses that same Hom formula for H and the direct-sum term formula in `def-pc-tensor-complex-sheaves`, specialized to modules as the item explicitly requires. The statement of `lem-weil-pbc-tensor-finite-product` gives the componentwise tensor isomorphism for arbitrary R-modules over a commutative ring, even for t=0. The relevant p-family is finite since p lies in [a,b] and r=h-p; neither J nor its terms need finite generation. The outer s-family is finite because h<=b-ell and s<=u. These checks justify the only cited non-elementary step, including its exact map.

Step 4 again uses only the total-Hom formula. Its maps beta -> (beta composed with j_s) and (beta_s) -> sum beta_s composed with pi_s are inverse by the displayed projection identities. Thus it does not assume that Hom commutes with an infinite product. The substitutions k=p-n and r=n-p-s identify its factors with exactly S_n. I verified the order of the two Hom arguments and the index J^{-r}.

Step 5 uses the universal bilinear property in `def-weil-pbc-module-tensor-product`; commutativity of R ensures scalar balance, so the specified formula defines a module map. Step 6 uses the basis notion in `def-weil-pbc-free-module` and that same tensor definition to define the finite sum D. The finite-basis hypothesis is imposed on P^s alone; W=J^{-r} and U=I^p are arbitrary modules. Step 7 uses the basis expansion from that definition to prove the identity f=sum_i iota_i(f(e_i)), then evaluates CD on arbitrary beta and f. Step 8 uses the same basis expansion, tensor balancing, and generation by pure tensors, all given by the two cited definitions, to prove DC. Both computations retain the sign epsilon and use epsilon squared = 1, valid for positive and negative integer exponents and in characteristic 2. Step 9 assembles the already proved inverse maps by taking finite sums. It does not invoke a chain-map identity or the derived category.

I checked delivery-errors B--E against the node and source. There are no new unsplit nodes, unnamed objects, false duplicate claims, proof-sketch-only statements, or new definitions. The non-elementary tensor-distribution input has an exact statement citation (C1/C4); all remaining steps provide coordinate maps, finite sums, or integer calculations directly from definitions. No clause is moved into a new node (D1/D2), and no downstream derived evaluation node is cited, avoiding a cycle. All steps have fewer than 2000 characters. The supplied component inverse is proved in both directions rather than described merely as an isomorphism.

For edge cases I checked the zero ring, a rank-zero P^s (empty basis), I=0, J=0, an empty S_n caused by n>b-ell+u, and singleton ranges a=b and s=u with r=-ell. The maps become the unique zero-module map in the empty cases; in rank one with all nonzero terms in degree zero they reduce to g tensor x -> (f -> g(f(x))). In odd signed cases both inverse compositions acquire exactly two copies of epsilon, so no characteristic assumption enters. No missing hypothesis or statement dispute was found.

## Unfinished work

None for this one-level split. The existing nodes cited by it retain their own statuses. Server dry-run and direct delivery are the remaining mechanical steps.
