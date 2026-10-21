# Stage-1 delivery: lem-pe-principal-reduction-cone-calculus

## Files written

- dag/nodes/sec-proetale-coefficients/lem-pe-principal-reduction-cone-calculus.json: statement, split into ten proof steps. Statement unchanged. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement certificate for every step/node citation.
- report.md: this report. The sandbox also retains the exact search log and the local generation script; neither is a project-source change.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, principal-reduction terminology, scalar cone terminology and the likely modules. The tag has no declaration. DerivedCategory.TensorStructure.reductionIso and its naturality, reduction-unit and change-of-scalar lemmas in CategoryTheory/DerivedCategory/Complete/ReductionCone.lean give part of the assertion, but do not give the asserted strict cone-of-cone permutation, its boundary square and all shift/coaugmentation comparisons. Thus this is not an attachment. The ordinary-ring principal-derived-tensor-cone node likewise covers only part and has different coefficient objects.

## WANTED

None. All source material needed here is available locally.

## Corrections and limitations

The imported statement is retained exactly, including its coefficient category, all integer shifts, transition and coaugmentation formulas, and negative-projection boundary convention. No STATEMENT-DISPUTED issue was found. The imported proof was empty. The new proof fills the strict chain calculation and the natural tensor identification rather than citing the parent Nakayama argument, which would be circular.

The proof is marked agent-written: the blueprint's Cones paragraph asserts commutation but omits the coordinate calculations. I expanded those assertions, following its two-term coefficient-resolution route and the Stacks cone/tensor conventions. I did not introduce a boundedness, flatness or torsion-freeness hypothesis on the input complex. The two-term coefficient resolution, not the arbitrary input, is the bounded flat object.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for principal reduction, mapping cone and finite coefficient were used before deciding to reuse existing nodes. det-pe-derived-nakayama-resolution supplies the exact coefficient sequence, but its statement alone does not specify the tower-compatible natural comparison required here. The proof therefore lifts the quotient and unit maps explicitly. lem-pod-principal-derived-tensor-cone is for ordinary rings and lacks the cone-of-cone and shift clauses. It is not substituted for a sheaf theorem.

## Search evidence

The item retains its existing O2 searches unchanged. This session additionally ran the five queries in searches.jsonl through the required msearch command: LeanFinder for a scalar quotient cone tower, Loogle for mappingCone/map, grep in Algebra/Homology for cone/quasi-isomorphism and shifts, LeanSearch for exact scalar-cone functors, and a second LeanFinder phrasing for signed iterated-cone interchange. All services answered. The hits concern ordinary cone constructions, additive functors applied termwise, shifts, or scalar short complexes. I read the relevant shiftIso and mapTriangleIso source in Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean and the short-exact-triangle source in DerivedCategory/ShortExact.lean. The former functor is induced by an additive functor on the abelian category; D_n is a functor on complexes, so that declaration does not specialize to the whole item. No result gives every requested compatibility in one line. No new-node search claim is made.

## Review by NR

I read the chapter sec-proetale-coefficients, the unit sk-lem-pe-derived-nakayama and the current main-20261015 first-reduction proof, especially its Cones paragraph. The proof remains on that route: resolve the finite coefficient by two rank-one terms, compute its tensor cone, then calculate the strict cone/shift interchange. The item is not the unit's key statement, so I changed no realization record. I read Stacks derived.tex at definition-cone (014E), and sites-cohomology.tex at lemma-bounded-flat-K-flat (06YQ), lemma-K-flat-resolution (06YS), lemma-derived-tor-quasi-isomorphism-other-side (06YT), definition-derived-tor (06YU) with its preceding construction, and lemma-factor-through-K-flat (0G7D). These support the existing tensor-model nodes; I cite their node statements rather than their proofs. There are no new nodes whose statements or sources need separate certification.

For step 1 I read def-weil-abstract-derived-category: it gives the actual cochain cone differential, localization and negative-projection triangle convention. Squaring the displayed differential and checking the diagonal maps, transition and unit uses only that formula. In step 2 the same node supplies cone triangles and factoring cohomology functors; lem-sf-triangle-morphism-iso states exactly that two isomorphism components force the third. The two repeated components are Qg, so its hypotheses really hold. Factoring cohomology then proves quasi-isomorphism invariance, not merely invariance after an unexplained localization. Additivity is checked by the explicit direct-sum rearrangement and the diagonal/codiagonal formula in the induced additive derived structure; I removed a contemplated citation to linear-localization-descent because its displayed statement did not itself assert preservation of sums.

For step 3 I read det-pe-derived-nakayama-resolution's statement: it gives exactly the coefficient sheaf sequence on X_proet with the pulled-back R and quotient B_n. It applies to every scheme, so no Noetherian or characteristic restriction is inserted. The augmentation is consequently a quasi-isomorphism. The bounded-flat-K-flat node states the result for essentially small sites and a coefficient universe, independently of object/morphism universe choices. I use a small site model in that universe, and the explicit rank-one tensor unit proves flatness. These checks apply to P_n and R[0], not to M.

For step 4 I read the full statements of lem-pc-kflat-resolution, lem-weil-pbc-site-derived-tensor-descent and def-pc-tensor-complex-sheaves. The resolution node gives flat terms and a quasi-isomorphism for arbitrary unbounded inputs. The tensor-descent statement gives the model when BOTH inputs are K-flat with flat terms, its resolving-category equivalence, and extension of natural transformations. C and P_n satisfy precisely these hypotheses. The two signs in the tensor swap were computed explicitly before identifying Tot(P_n tensor C) with D_n(C). Since D_n already preserves quasi-isomorphisms, passing from C to M is legitimate. The extension uses the stated localization equivalence, not a claim that arbitrary triangulated cone choices are functorial.

For step 5 the same descent statement supplies naturality also in the coefficient complex; sk-def-pe-derived-completion specifies the canonical quotient transitions and reduction map whose compatibility is needed. I verified the chain lift of the quotient has components (pi,id), the unit lift is identity in degree zero, the augmentation squares commute, and these become exactly T_n and j_n. This is the missing extra information beyond a bare cone isomorphism. All tensors are over the same sheaf ring R and the finite reductions are regarded by restriction as R-objects.

Steps 6 and 7 cite the actual cone/shift convention, and contain their entire arguments: the four-coordinate differentials on both sides agree under (b,a,b',a') -> (b,b',a,-a'); the shift map changes the second sign by (-1)^r. The inverse maps are displayed. These are elementary coordinate calculations and do not conceal new lemmas. Step 8 needs no new theorem: maps in a square act separately on the four coordinates, and the two orders of applying transitions give the identical displayed tuple. Step 9 again cites the actual boundary convention: D_n(-p) followed by S_1 is (-a,a'), exactly the negative projection on the permuted cone. The inclusion and both coaugmentation equations are written out.

In step 10, def-weil-abstract-derived-category explicitly says a distinguished triangle is isomorphic to the image of a chain-map cone triangle; def-weil-triangulated-category explicitly defines exactness as additivity, a shift comparison and preservation of distinguished triangles. Steps 2 and 6–9 provide these precise data. Thus this final step only assembles statements already proved, rather than using the desired exactness as a premise.

I checked B1–B10: no statement-only child is replaced by a proof sketch, no new self-containedness/notation/search/source issue arises, and no source or maintainer field is changed. I checked C1–C8 against each cited statement, including the two-K-flat-input and site-universe hypotheses. The three off-unit theorem uses are declared as generic tools in split_report; they supply resolution/descent, without replacing the unit's coefficient route. I checked D1–D5: no clause is moved to a new node and no parent is cited as a dependency. I checked E1–E7 with the actual objects, maps, signs and hypotheses; there is no appeal to an undefined transport or to exact ordinary tensor on M. The citation file uses actual verbatim portions of the statements, including whole statements when more than one clause is used.

Edge cases checked: M=0, zero maps, f=id, n=1, r=0, r=1 and r=-1, arbitrary negative r by parity, and a complex killed by pi. In the last case D_1(M) is M direct-sum M[1], as derived reduction should be; it is not identified with ordinary M/pi M. For f=0 the permutation still has its necessary last minus sign. For r odd it reverses only the second coordinate. No non-elementary step exceeds 2000 characters; each coordinate step is one explicit routine argument, not a hidden standalone comparison lemma.

## Unfinished work

None within this one-level split. Existing unsplit dependencies, if any, remain the project's later items. No Lean file was written and no compiler, Lake or build command was run.
