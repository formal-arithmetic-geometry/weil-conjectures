# Stage-1 report: cor-fin-projective-curve-finite-group

Files written:

- `dag/nodes/sec-smooth-purity/cor-fin-projective-curve-finite-group.json` — statement, split proof, no new nodes; Mathlib search found no matching theorem.
- `citations.json` — verbatim statement quotations for every node used by every proof step.
- `searches.jsonl` — the four required searches run with `msearch.py` (LeanFinder, Loogle, grep, and LeanSearch).

Attachments: none. I found no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator` carrying this statement or its blueprint tag.

WANTED: none.

The repository copy already contained a complete seven-step split, but was still `unsplit` and cited the older `literature/blueprint/master` snapshot. I retained its mathematical route, changed the provenance to `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/`, marked it `split`, and updated the split summary to identify how the seven steps realize the current five-paragraph proof. No new node was justified: the non-elementary ingredients are already stated by the cited DAG nodes, while the finite-group filtration, annihilation calculation, and exact-segment calculation are written as elementary parts of the item's proof.

## Review by Q59

I read the current blueprint statement and proof (`cor-fin-projective-curve-finite-group.md` and its `.proof.md`), the imported item node, and each cited node in the DAG. Step 1 uses the existing enough-injectives statement for abelian sheaves, the direct-image additivity/left-exactness statement, the horseshoe delta-functor statement, and the definitions of constant and constructible abelian sheaves; these provide exactly the derived-functor setup and the zero base case. Step 2 is the finite-group filtration argument and was checked on the zero group and on a cyclic group of prime order; its strict cardinality decrease makes the induction terminate, and invertibility of every prime divisor follows from the assumed inverse of the group order.

Step 3 uses the constant-sheaf definition and the exact-sheafification node to obtain a short exact sequence of constant abelian sheaves. Step 4 applies `thm-fin-projective-curve-constant` only after checking that the same projectivity, finite-type, fibre-dimension, and prime-invertibility hypotheses hold, and uses the existing constant-sheaf definition to transport the chosen additive isomorphism with `F_ell`. Step 5 checks that every group in the filtration is killed by `n=|M|`, then uses the killed-by-`n` module node, abelian inverse-image exactness, the geometric-stalk identification, the module inverse-image node, and the two constructibility definitions to convert the abelian higher direct images to constructible `Z/n`-module sheaves. The quoted statements explicitly supply the unique scalar actions, linearity, and compatibility of underlying inverse images.

Step 6 uses the existing derived-functor long-exact-sequence statement and the sheaf-of-modules category definition. I checked the displayed segment `T -> A -> B -> C -> D`, including the separate `q=0` case with `T=0`; the elementary image/kernel calculation gives the short exact sequence with cokernel and kernel, and the cited module-category statement supplies the corresponding module kernels and cokernels. Step 7 applies the kernel, cokernel, and extension clauses of `thm-constructible-serre` to the finite ring `Z/n` (including `n=1`), then uses the two constructibility definitions to forget scalars and recover the requested abelian constructibility. The direct-image definition supplies the final vanishing of negative degrees from a nonnegative injective resolution.

For every citation in these steps I opened the corresponding node and copied a verbatim statement fragment into `citations.json`; a substring check against the DAG statements passes. I also checked all hypotheses against the item statement, including the scheme-over-a-field assumptions, geometric fibre dimension bound, finite abelian group, and invertibility on `S`. The required Mathlib searches produced no theorem matching this constructibility result (LeanSearch was available and returned only generic constant-sheaf declarations; Loogle and grep returned no direct match).

What remains unfinished: nothing in this stage; no Lean source was written and no compiler or build tool was run, as required.
