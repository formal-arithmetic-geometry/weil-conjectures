# Worker report: det-thm-sf-pf-field-tensor

Files written: `dag/nodes/sec-six-functors-basics/det-thm-sf-pf-field-tensor.json` (item, split; no new nodes); `citations.json` (verbatim statement quotes for every cited node at every proof step). No Mathlib leaves were created.

Attachments: none. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the archived upstream source found no sorry-free declaration tagged `(blueprint: det-thm-sf-pf-field-tensor)` or stating this tensor-closure result.

WANTED: none.

The inherited item statement was retained. It explicitly fixes the standing separated finite-type-over-​the-field scheme setting, distinguishes a finite subextension $E$ from the condensed $\Qlb$ coefficient whose sections land in a single finite subextension, and forms the localizing closure in the ambient unbounded derived category. The inherited proof had no new dependency node to create; I searched the DAG and blueprint for each non-elementary input. The initial retained repair cited `lem-sc-source-kflat-tensor-left-triangulated` in step 1 for exactness of derived tensor by a K-flat model, and `lem-sfb-locally-closed-extension-coherence` in step 3 for normalized factorization independence and composition of locally closed extension by zero. The dedicated return repair described below additionally removes the inline comparison from step 3. The proof dependency union and the verbatim citation file were updated accordingly. The status is now `split`.

## Review by NM

I read the item and its proof against `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/sk-thm-sf-pf-field-tensor.md` and its proof file, and checked the chapter and unit records. The blueprint statement has exactly the two clauses in the item. The eight proof steps realize, in order, the blueprint's exactness and coproduct argument, reduction to locally closed lisse generators, extension-by-zero base change, two projection-formula applications, lisse tensor and K-flatness, explicit constructibility, and the two localizing-minimality arguments.

Step 1 uses `sk-def-sfb-derived-tensor-hom` for the relative K-flat derived tensor and its internal-Hom adjunction, `def-pc-tensor-complex-sheaves` for the total-complex and cone calculation, `def-pc-kflat-complex` for preservation of acyclic complexes, `def-weil-abstract-derived-category` for cone triangles, `det-def-localizing-closure-existence` for ambient coproducts, and `lem-sc-source-kflat-tensor-left-triangulated` for the precise statement that tensoring by a K-flat object preserves shifts and distinguished triangles. I checked each cited statement contains the fact used; the step is marked non-elementary because the exactness and coproduct argument is substantive.

Step 2 uses `det-cor-coefficient-heart-ii-generation` for finite cone witnesses by $a_!L[n]$, `det-cor-coefficient-heart-ii-triangulated` for triangulated closure of $\Dbc$, and `lem-weil-pbc-finite-type-over-noetherian` to obtain Noetherianity from finite type over the field. The field spectrum edge case is explicit: $\operatorname{Spec} k$ has one point and is Noetherian. The two finite-cone inductions and the zero/rank-zero case are written out.

Step 3 uses sk-lem-coefficient-heart for $b_!=i_*u_!$, det-sf-open-closed-sequence-ring-sheaf clause (4) twice for base change of $i_*$ and $u_!$, and sk-prop-sfb-cartesian-coefficients for the coefficient identifications and exact pullback. The finite-type Noetherian theorem and the Noetherian-open theorem verify that the base changes and the relevant opens satisfy the qcqs and quasi-compactness hypotheses. The statement of lem-sfb-locally-closed-extension-coherence explicitly identifies the extension with $i_*u_!$ for a given open-then-closed factorization, independent of that factorization. Applying it with $Y$ and $R=\Lambda_Y$ identifies the base-changed composite with $b_{Y!}$, even when $Z_Y$ is larger than the closure of $T_Y$. This is the precise lemma hidden in the returned long step; I now cite it directly rather than reproduce a comparison argument.

Step 4 uses `det-lem-int-tensor-projection` for both typed projection-formula isomorphisms and `sk-def-sfb-derived-tensor-hom` for symmetry and exchange of tensor factors. The displayed composite has the correct objects $a_!L$, $b_!M$, $c_!d^*M$ and does not assume an unsupported shriek-composition theorem.

Step 5 uses `sk-lem-coefficient-heart` for the lisse finite-free local models, `sk-prop-sfb-cartesian-coefficients` for the coefficient rings after pullback, `def-pc-kflat-complex` for the degree-zero K-flat criterion, and `sk-def-sfb-derived-tensor-hom` for computation of the derived tensor. The finite-free tensor is checked on a common pro-etale trivializing cover, including the rank-zero case; exactness is checked by restriction and vanishing of kernel/cokernel after the cover.

Step 6 uses `sk-lem-coefficient-heart`, `det-sf-open-closed-sequence-ring-sheaf`, and `sk-def-sfb-constructible`. I checked the five locally closed pieces $X\setminus Z$, $Z\setminus S$, $S\setminus V$, $V\setminus W$, and $W$, their restrictions $0,0,0,0,N$, the empty-piece convention, and the Noetherian constructibility hypothesis. This establishes the generator tensor belongs to $\Dbc$ before either finite-cone induction is invoked.

Step 7 uses the statement of `det-def-localizing-closure-existence` (ambient coproducts, localizing closure, and minimality) to form the full subcategory of objects whose tensor with a fixed $B\in\Dbc$ lies in the localizing closure. Step 1 supplies its triangulated and coproduct closure, and the minimality argument is written explicitly.

Step 8 repeats the same argument in the other variable, using the symmetry and step 7 to contain $\Dbc$, then applies the same minimality statement. It concludes the exact ambient tensor for arbitrary $A,B$ in the localizing closure.

I tested edge cases while reviewing: $X=\operatorname{Spec}k$, empty strata and rank-zero lisse sheaves, open and closed immersions (including identity immersions), and the finite stage $E=\mathbf Q_\ell$ versus the $​\Qlb$ coefficient. No hypothesis is added or dropped, no SGA source is used, no duplicate/new node is introduced, and the DAG remains acyclic. The server-side `srvcheck.py ... check_dag` was run before this report was written and completed after waiting for worktree capacity.


## Repair of dedicated handoff

The return in coord/returns/NM.md singled out the 2815-character non-elementary step 3. I retained the statement, Lean record, proof route and other steps. The replacement step applies the existing locally closed extension coherence theorem explicitly, so no new node duplicates that theorem. It keeps the two typed open-closed base-change isomorphisms and verifies their hypotheses, while deleting the inline scheme-theoretic-closure comparison and its three redundant citations. I also made step 1's existing citation of K-flat tensor exactness explicit in its text. All retained citation quotes were checked verbatim against the current node statements.

The existing Mathlib search history and searches.jsonl were retained. I read the logged results: the Tor hits concern general derived functors, the localization hits concern monoidal localization, and the grep hits concern topological constructibility. They do not state this pro-etale constructible tensor result. The logged LeanSearch retry was unavailable due to rate limiting; it is not evidence of absence. No new search question or new node requires repeating these searches.
