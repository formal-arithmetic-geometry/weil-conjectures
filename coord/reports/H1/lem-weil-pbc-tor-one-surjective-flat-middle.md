# Delivery report: `lem-weil-pbc-tor-one-surjective-flat-middle`

## Work

I read Stacks Algebra, Tag 00MM (`lemma-surjective-on-tor-one`, algebra.tex lines 23846--23880) in `/home/ubuntu/c1-stacks-review/algebra.tex`, and searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, Tor-one surjectivity, and flat intermediate base change. No exact declaration, with or without `sorry`, exists.

The returned proof is repaired by splitting the augmented resolution at $I=\operatorname{im}(F_1\otimes_R A\to F_0\otimes_R A)$. `lem-weil-pbc-flat-quotient-tensor-injective` gives injectivity after tensoring the second short exact sequence, and `lem-weil-pbc-tensor-right-exact` gives the exact tensor sequence for the first short exact sequence and for the Tor quotient presentation. The canonical identifications with $F_i\otimes_R B$ identify the image with $K_B$.

## Review by H1

I checked Tag 00MM's hypotheses one by one: ring maps $R\to A\to B$, an $R$-module $M$, flatness of $M\otimes_R A$ as an $A$-module, and surjectivity of the natural first-Tor map. Step 1 uses the definition of Tor via a free resolution and the exact-sequence definition, introducing $K_A$, $K_B$, and $I$. Step 2 uses `lem-weil-pbc-flat-quotient-tensor-injective` exactly on $0\to I\to F_0\otimes_R A\to M\otimes_R A\to0$, and `lem-weil-pbc-tensor-right-exact` exactly on $0\to K_A\to F_1\otimes_R A\to I\to0$; the identifications $(F_i\otimes_R A)\otimes_A B\cong F_i\otimes_R B$ are elementary reassociations. Step 3 uses `lem-weil-pbc-tensor-right-exact` on $F_2\otimes_R A\to K_A\to\operatorname{Tor}_1^R(M,A)\to0$, checks that the $F_2$ image base-changes to the $F_2\otimes_R B$ image, and identifies the descended map using the functorial $A$-module structure and $\bar k\otimes b\mapsto b\bar k$.

I opened each cited node and verified that its statement supplies the fact used. The two tensor lemmas are existing Mathlib-backed nodes, so no new node was needed. I checked the edge cases $B=A$ (identity map) and $M$ free (both first Tor groups vanish). The item retains the exact Tag 00MM statement, `status: split`, `blueprint.same_as: []`, and now lists both tensor lemmas in `proof_deps`. The previous fibre-product report was replaced completely. JSON parsing, DAG checks, and delivery preflight are run after this repair.
