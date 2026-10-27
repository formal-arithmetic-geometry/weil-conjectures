# Stage-1 report: lem-sfb-flag-projective-linear-system

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flag-projective-linear-system.json`: item, statement unchanged; split into eight scheme-level proof steps. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-borel-quotient-affine-space-cell.json`: new statement-only geometric lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-cell-picard-product.json`: new statement-only product Picard lemma, unsplit; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every cited node in every item step.

The sandbox also retains `searches.jsonl`, the actual output of all fifteen searches in `search-results/`, and `prepare.py`, which wrote the JSON. No repository, launcher, Lean source, or unit record was edited. No compiler, Lake command or build was run.

## Attachments

None. Searches of the project source by the exact blueprint tag, Borel, flag variety, line-bundle linearization, big cell, Picard product and projective representation found no declaration giving this item or either new node. The projectivization actions found in Mathlib concern projective points of modules already equipped with an action. They do not construct the algebraic projective representation of this unlinearized line bundle. `AlgebraicGeometry.Proj.fromOfGlobalSections` (Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:443) starts from a graded ring map, rather than supplying the missing group action.

## WANTED

None needed for this delivery. The argument follows the available Milne and Stacks sources, with the extra construction explicitly marked agent-written. No SGA source is used.

## What was wrong or missing

The imported item had no proof. Milne Proposition 18.22 (printed p.393) asserts the canonical projective representation and complete-system map, but does not construct them in that paragraph. Nonzero sections alone do not imply global generation for arbitrary proper varieties. Here the missing reason is invariance under the transitive group action, which must itself be established before it can be used. We supply that invariance from an affine-cell product Picard theorem, and then construct local matrices and verify the multiplication law up to scalars. We do not assume a G-linearization, which need not exist: for example the degree-one line on PGL_2/B = P^1 has its projective action without a PGL_2-linearization.

The statement has not changed. Its convention is that P(V) classifies one-dimensional quotients, so the projective left action on a quotient q is q composed with u^{-1}. This convention is kept throughout. The natural tautological line has its GL(V)-linearization; we do not assert that this line descends with a PGL(V)-linearization.

A live supporting node, `lem-sfb-borel-quotient-proper-geometry`, became available while the session was paused. We use its full smooth/proper/geometrically integral conclusion instead of making a second node for those assertions. The new affine-space-cell node states only the remaining geometric assertion.

The item's imported `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor lem-sfb-flag-projective-linear-system` also prints None, because the inherited creation chain has no remaining blueprint ancestor. We preserve that result and its via chain, while giving both new nodes a precise supporting place. The current blueprint was read through `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`; its proof (3) remains the direct-image/compactification route. This delivery expands only the already imported supporting Milne construction, without changing the chapter or unit route.

## Arguments retained for the new statement-only nodes

For `lem-sfb-borel-quotient-affine-space-cell`, I read Milne Lemma 18.21 and its proof (printed p.392), which explicitly says G/B contains an open subvariety isomorphic to affine n-space, with references to Proposition 13.52 and the proof of Theorem 17.65 (printed p.374). I also read the latter proof and its attracting-cell construction. The group here is any split connected group variety, not necessarily reductive; over the algebraically closed field the split hypothesis is automatic. The statement asks only for this affine cell, so it does not duplicate the proper-quotient geometry or restate any conclusion of the item about sections and projective actions.

For `lem-sfb-affine-cell-picard-product`, here is the full product argument intended for its future split. Put U = A^d inside X and let D_1,...,D_r be the codimension-one irreducible components of X minus U. Since X and T are smooth and geometrically integral over F, X, T and X times T are regular integral Noetherian schemes, so line-bundle classes identify with Weil divisor classes (regular local rings are factorial, and Stacks divisors.tex 0BE9). In the Stacks Chow notation Cl is CH in codimension one, as explained in chow.tex section-divisor-invertible-sheaf. Tag 02TT, applied to A^d times T -> T, says that pullback is surjective on these Chow groups. Under the Picard/class-group identifications it is the ordinary line-bundle pullback. Thus any line H on X times T restricts on U times T to the pullback of some line N on T. Twist H by the inverse pullback of N. Its restriction to U times T is now trivial. Choose that trivialization as a rational section. Its divisor is supported on the complement; alternatively this support assertion is the localization sequence of Tag 02RX. The only prime divisors there are D_i times T, because dimensions add, and D_i and T are geometrically integral over the algebraically closed field. Hence the divisor is a finite integer sum of D_i times T. Each D_i is Cartier on the regular X. The twisted line is therefore the pullback of O_X(sum a_i D_i), proving surjectivity of the external-tensor map. For injectivity choose points x in X(F), t in T(F), available by finite type over an algebraically closed field. Restrict an external tensor product that is trivial first to X times {t} and then to {x} times T. Fibres of a line at an F-point are one-dimensional F-spaces, and hence give trivial constant lines. The first restriction makes its X-factor trivial and the second makes its T-factor trivial. This proves injectivity. The last clause follows by restricting the external decomposition to t_0. This proof requires smoothness of T (for the factorial/divisor comparison); the new statement retains it. It does not claim splitting for singular or nonreduced parameter schemes. Once an isomorphism over the smooth group has been obtained, its pullbacks may of course be taken over arbitrary algebras.

Sources read for this argument: chow.tex Tag 02TT, label lemma-pullback-affine-fibres-surjective, including its proof; Tag 02RX, label lemma-restrict-to-open; section-divisor-invertible-sheaf; divisors.tex Tags 0BE8 and 0BE9, labels lemma-normal-c1-injective and lemma-local-rings-UFD-c1-bijective, including the factorial comparison proof; more-algebra.tex Tag 0AG0, label lemma-regular-local-UFD. The product conclusion is our explicit consequence, not a claim that 02TT alone states it. The new node has statement dependencies only and no hidden proof inside its statement.

## Not duplicates

lem-sfb-borel-quotient-affine-space-cell vs lem-sfb-borel-quotient-proper-geometry: the existing node gives smoothness, integrality, regularity and properness of an already represented quotient, but gives no affine-space open; the new node states only that open.

lem-sfb-borel-quotient-affine-space-cell vs lem-sfb-flag-effective-picard-generators: the existing statement gives generators with nonzero sections, but does not assert the affine cell used in its source proof. Citing that proof in place of its statement would be C3.

lem-sfb-borel-quotient-affine-space-cell vs lem-sfb-longest-weyl-open-cell: the latter assumes reductivity and gives the open immersion U times B -> G for the longest Weyl element; it neither applies to the general connected affine group here nor states an affine-space cell in its quotient. No reductive quotient reduction is silently used.

lem-sfb-borel-quotient-affine-space-cell vs lem-sfb-reductive-borel-pair-structure: the latter assumes reductivity and gives properness and root data, with no affine-space cell in its statement.

lem-sfb-affine-cell-picard-product vs lem-pc-regular-curve-divisor-calculus: both cite Tag 0BE9, but the existing lemma is divisor and line-bundle calculus only for regular dimension-one schemes; it gives no product Picard decomposition in arbitrary dimension.

lem-sfb-affine-cell-picard-product vs lem-sc-divisor-module-local: both cite Tag 0BE9, but the existing lemma identifies local fractional-ideal sections of a divisor module on a smooth curve; it gives no product or affine-cell conclusion.

lem-sfb-affine-cell-picard-product vs lem-sc-smooth-connected-curve-local-rings: both cite Tag 0BE9, but the existing node gives the integral/DVR local-ring structure of a smooth connected curve, its function-field injections and its closed points; it does not compute the Picard group of a product in arbitrary dimension.

lem-sfb-affine-cell-picard-product vs lem-sfb-rigidified-product-seesaw: see-saw requires fibrewise isomorphisms already known; it cannot establish translation invariance for the family in step 2. The new lemma obtains that invariance from the affine-space open, with no fibrewise constancy assumed.

The whole DAG was searched by title, statement, tags 02TT/02RX/0BE9 and concepts, and the whole imported blueprint by Borel, big cell, affine cell, affine space, rational variety, linear system, Picard, Picard product and those tags. No blueprint statement gives either new lemma. The scheme-theoretic cohomology product nodes concern external products of sheaves already given; they do not decompose an arbitrary line bundle on X times T. Neither new node is elementary or a clause of the item: one is the geometric big-cell theorem, the other is the separate divisor-theoretic Picard decomposition. The item's proof carries the complete-system and projective-representation construction itself.

## Mathlib searches

All fifteen queries in `searches.jsonl` actually ran before the pause, and their saved outputs were read after resumption. For each of the item, affine-cell geometry, and product-Picard question there are two distinct LeanFinder phrasings, a Loogle query, a source grep and a LeanSearch query. The node records reproduce those exact queries and actual outputs. Every service answered successfully; no unavailable service was recorded as no-match. The hits were topological quotients, affine space and Proj themselves, module tensor-product formulas, abstract ring Picard groups, projective objects in representation categories and set-level projectivization actions. None is the asserted scheme theorem or its one-line specialization. I opened the relevant Proj construction and the Projectivization action source to check that distinction. The second phrasing for each question is retained, and no search from before the pause was repeated.

## Review by Q123

I read Milne 18.12--18.13 (printed p.390), 18.21 (p.392), and the full 18.22 proof (pp.392--393), together with the cited affine-cell and Stacks divisor/Chow sources described above. I checked delivery-errors B through E against the actual node files and their statements. The item and both new nodes introduce all objects and keep their hypotheses; all TeX is single-escaped in the decoded JSON. New nodes are unsplit and have no proof steps. There is no Lean attachment, no use of a sorried declaration as a finished proof, and no SGA route.

Step 1 reads the homogeneous quotient node for separated finite-type representability, the characteristic-sequence node for its stated Zariski B-torsor structure, the proper-geometry node for smoothness/geometric integrality/properness, and the new cell node for the affine-space open. The local product torsor charts justify finite presentation and the ratio/lifting hypotheses before applying the proper-geometry node. The finite-dimensionality node applies because the sheaf is invertible, hence quasi-coherent and finitely presented locally; H^0(O_Q)=F uses the stated geometrically integral clause of the proper-variety node. During review I added the homogeneous quotient citation explicitly at the start, so separated finite-type representability is not inferred from a node which only assumes it.

Step 2 takes precisely the final clause of the product-Picard node with X=Q, T=G and t_0=e. Both factors are smooth geometrically integral; G is affine separated finite type. The pullback family is defined by inverse translation, and restricts to L at e. The scalar transition functions come from the one parameter line N; they are not arbitrary fibrewise choices.

Step 3 uses the two closed-point statements exactly for Jacobson density and the residue field F. It uses the quotient node's actual assertion that Q(F)=G(F)/B(F), not merely transitivity on geometric points. A nonzero section on an integral scheme is nonzero on a nonempty principal open in a trivialization. Translation then supplies a nonvanishing section at each closed point. The finite basis makes the evaluation cokernel locally a quotient by finitely many functions, so its support is a closed set; Jacobson density rules it out. No unproved basepoint-freeness assertion is used.

Step 4 applies the projective-bundle node's statement to the now surjective evaluation quotient. It explicitly supplies both the classifying morphism and the compatible pullback isomorphism of O(1), in the correct quotient convention.

Step 5 applies the coherent flat-base-change node in degree zero to every F-algebra, all of which are flat over F. L is quasi-coherent, Q is proper. The local line-family isomorphism and the inverse-translation automorphism give invertible operators on the base-changed section module; their matrix entries and inverse entries are regular. Scalar transitions of N give PGL classes agreeing on overlaps, so gluing is legitimate. This establishes algebraicity rather than merely an action on F-points.

Step 6 uses the proper-variety node and coherent flat-base-change node, now for O_Q, to identify all functions on Q_A with A. Any automorphism of an invertible sheaf is multiplication by a global unit (locally End(L)=O); hence the two line identifications associated to multiplication differ by a base scalar. I checked the order: inverse pullbacks compose through h^{-1}g^{-1}=(gh)^{-1}. The verification is over the universal opens of G times G; it is therefore an equality of morphisms and survives nonreduced base changes. I do not apply the smooth-parameter Picard lemma to those nonreduced bases.

Step 7 uses the quotient-pair theorem to identify the two maps from equality of quotient pairs. I computed ev_{gx} R(g)=phi_{(gx,g)} ev_x, so the induced projective action is q -> q R(g)^{-1}, exactly the left action in the quotient convention. This proves equivariance on G times Q as schemes.

Step 8 unpacks the same universal quotient to construct the tautological line isomorphism, using identity maps on the displayed quotient modules. Its composition is q v^{-1} u^{-1}=q(uv)^{-1}; this checks the action law on the line itself. Scalar matrices fix the projective base but act with their scalar on the fibre after the canonical quotient-pair identification, as required. This is a few-line consequence of the quoted classification and is marked elementary with that citation, rather than made into a new node for a clause of the item.

Every node in each step's uses list was opened and its statement read. `citations.json` contains the actual sentences or full formulas used; its quotations were checked as literal substrings. The proof-dependency list is exactly the union of these uses. The largest step is under 1,000 characters, so no long step conceals a separately quantified lemma. The genuinely separate geometric and Picard inputs are the two unsplit nodes.

I tested small cases: G=B (including a torus, a unipotent connected group, and the trivial group) gives Q=Spec F, V one-dimensional and trivial PGL, and all steps still hold. For PGL_2/B=P^1, O(n) with nonzero sections means n>=0; n=0 gives a constant map and n>0 gives its usual complete-system projective action, without falsely requiring a PGL_2-linearization. For the product lemma d=0 forces X=Spec F and its conclusion is tautological; positive-dimensional T with a nontrivial line N is allowed and is exactly why the extra parameter factor is retained. The false stronger hypothesis-free claim for arbitrary proper varieties would fail on an elliptic curve with a degree-one effective line bundle: its section has a base point. Our proof uses the affine cell and transitive translations instead.

The off-unit tools requiring declarations are proper coherent finiteness, the quotient universal property, canonical coherent flat base change, and the two closed-point geometry facts; they are declared in split_report.tool_uses with their precise uses. The canonical coherent flat-base-change theorem and proper geometrically integral global-functions theorem are generic tools as well; the former is explicitly declared in split_report.tool_uses. None replaces the unit's direct-image route.

## Unfinished work

The two new nodes remain statement-only stage-1 queue items, as required for a one-level split. The assigned item is fully split; no mathematical clause is left unfinished. Dry-run and final push results are recorded below when the delivery command exits.

## Validation log

The first dry run exited at the duplicate-tag gate: it also required the comparison with `lem-sc-smooth-connected-curve-local-rings` (Tag 0BE9). Its statement had already been read; the missing explicit pair is now added above. No mathematical or JSON change was needed.

The second dry run reached server preflight, which did not recognize the cell node’s grouped bracket citations as individual node references. I changed the new nodes to individual `[def-id]` references, preserving all statements and hypotheses. In the same citation audit I selected `lem-pc-flat-base-change-cohom`, whose statement explicitly says the base-change map is an isomorphism, instead of using a statement that merely displays an abstract cohomology isomorphism. This makes the canonical scalar and section identifications in steps 5--6 explicit; its generic tool use and quotations are included.

The final dry run exited successfully: `OK (not pushed) deliver/Q123/lem-sfb-flag-projective-linear-system at c86c72f0ebb: preflight passed`. The local citation audit checked all 16 step/node quotations and exact item-statement preservation; the maximum proof-step length is 908 characters. Delivery contains two new statement-only nodes and zero Mathlib leaves. The direct-delivery brief authorizes Q123 to push this reviewed split itself after the passing dry run.
