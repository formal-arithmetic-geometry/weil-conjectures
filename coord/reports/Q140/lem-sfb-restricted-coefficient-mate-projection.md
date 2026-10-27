# Q140: lem-sfb-restricted-coefficient-mate-projection

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-restricted-coefficient-mate-projection.json: statement, split into four steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- citations.json: eleven step/node entries, each copying the cited statement verbatim.
- searches.jsonl: actual searches made with the required command; the item preserves its inherited search records and adds these results.

## Attachments

None. Searched WeilConjectures both for the blueprint tag and for restricted-coefficient/mate notions and derivedPushHom/pushHomOfComapIso. Read CategoryTheory/ModuleObjects/ChangeOfScalarsSquare.lean and SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean. The project defines the scalar mate, conjugate and derived restriction comparison, but these definitions do not prove the requested tensor-projection equality. No exact completed declaration for the whole item was found.

## WANTED

None. The proof is marked agent-written: the blueprint paragraph does not contain this full normalization argument.

## Corrections and scope

The mathematical assertion is unchanged. Corrected the citation specifying e_Z: the imported residue-specific tensor presentation nodes state constructions for integral/residue coefficients, while this item allows arbitrary exact extension of commutative condensed coefficients. The already-existing lem-sfb-internal-scalar-pullback-normalization gives the required generic balanced map s tensor x maps to x tensor s. Replaced those two statement references and dependencies with that generic node. This is a citation correction, not a statement dispute or an added hypothesis.

Read the parent lem-sfb-coefficient-push-filtered-legs review note, which explains the distinction between this actual derivedPushHom and the adjunct-defined NB/NP siblings. The existing sibling lem-sfb-flat-coefficient-square-normalization already states the actual conjugate's normalized tensor equality and identifies the actual d with the ring-sheaf comparison. The proof uses that statement, without assuming the desired coefficient-push comparison. The Mathlib leaf lem-trf-iterated-square-mates closes the formal bridge between the actual scalar mate and the geometric mate of that actual conjugate. Thus no new bridge or tensor lemma is necessary.

## Not duplicates

No new nodes. Reused lem-sfb-flat-coefficient-square-normalization and the Mathlib leaf lem-trf-iterated-square-mates. Read lem-sfb-internal-scalar-mate-projection and lem-sfb-internal-scalar-projection-mate: they use an adjunct-defined push map, whereas the item uses the separately specified coefficient mate. Step 1 explicitly proves the required bridge rather than silently identifying these maps or creating another copy of their projection identities.

Whole-DAG searches covered scalar/counit, tensor/mate, conjugate/mate and the exact iterated_mateEquiv_conjugateEquiv declaration; whole-blueprint searches used projection mate, coefficient.*projection and conjugate. No imported blueprint node states this precise normalized coefficient mate equality; same_as remains empty. The ancestor command identifies det-thm-sfb-proper-base-change-rational. The existing precise paragraph (1) from.place and via are retained. No unit realization field is due: this item is not the unit's key theorem.

## Mathlib searches

Ran leanfinder with two different phrasings, loogle, grep, and leansearch; read all returned hits. The broad statement search found ordinary ModuleCat scalar counits, presheaf tensor maps and sheaf pushforward maps, not the claimed equality of the specific unbounded derived maps. The second semantic phrasing found CategoryTheory.iterated_mateEquiv_conjugateEquiv. Read Mathlib/CategoryTheory/Adjunction/Mates.lean, especially the mate formula and lines 442–477; its generic result is already represented by lem-trf-iterated-square-mates, status mathlib. This is used as a formal lemma, not misclassified as a match for the entire item. All new search entries exactly reproduce the command's tool/query strings and actual returned names. No service was unavailable.

## Review by Q140

I read the chapter and unit records, the current main-20261015 rational proper-base-change proof paragraph (1), the coefficient-comparison blueprint definitions, and the Stacks source sites-cohomology.tex at Tags 07A4 (lemma-pullback-tensor-product), 07A6 (lemma-adjoint), 0D6E (lemma-derived-pushforward-composition) and 0B56 (equation-projection-formula-map). The blueprint supplies the scalar-comparison purpose; the Stacks definition confirms that projection is the adjunct of counit tensor identity, without an isomorphism assertion. No SGA is used. There are no new nodes whose sources need checking.

For step 1 I opened every cited statement. The flat-square lemma fixes theta as the inverse of the derived pull conjugate of the actual d. The conjugate definition fixes the reversal between left and right adjoints, so the right-adjoint conjugate of theta has direction G_R U_X to U_Y G_S and is d inverse. The iterated-square-mates leaf states exactly that two successive square mates give that conjugate. I checked the eight functors in its substitution: L1=L_R, R1=G_R, L2=L_S, R2=G_S, F1=T_Y, U1=U_Y, F2=T_X, U2=U_X. Its first mate has type T_Y G_R to G_S T_X and its second has type G_R U_X to U_Y G_S. The definitions of derived-push-hom and mate-push-hom specify the inverse scalar mate of d inverse. Bijectivity therefore identifies the first mate with the actual gamma; the general adjunction-mate statement explicitly gives the transpose T_X(epsilon) theta. No flat representative calculation or implicit theta=lambda identification is hidden in this step.

For step 2 the ring-sheaf-change-adjunction statement explicitly gives the transpose relation for b and d, not merely the existence of isomorphisms. Its hypothesis a_X c_R = c_S f inverse a_Y holds for coefficients pulled back from the point by the coefficient compatibility in the item. The flat-square statement explicitly says that its d equals this comparison and that the scalar adjunctions agree under the module equivalence. Thus M=T_Y G_R K and N=T_X K are legitimate unbounded inputs. I checked the outer factors: postcomposition by G_R(e_X) becomes postcomposition by e_X, and precomposition by e_Y inverse becomes precomposition by L_R(e_Y inverse). This produces exactly the transpose of the specified h, not of an unspecified map with those endpoints.

For step 3 the generic scalar-pullback normalization states that e_X is natural and is normalized on the balanced generators. Its naturality at epsilon moves the counit through e_X. The flat-square lemma's final equation is precisely the remaining four factors, in the same direction and with the same right coefficient. Substituting M=G_R K yields the requested transpose. The generic e and the item's e coincide as specified balanced presentations; the citation correction makes that scope explicit. All hypotheses of the flat-square lemma occur in the item; it assumes neither boundedness nor invertibility of the push map.

For step 4 the ringed-projection-mate-exact statement gives the actual projection transpose, plus naturality in both variables. The two tensor composites differ only by the bifunctor interchange identity, written out in the step. Injectivity of the Hom bijection then proves equality, and the stated naturality of projection implies naturality of h. This is an elementary assembly, not an additional projection formula theorem. In particular we never use a proper projection isomorphism, qcqs continuity or a filtered diagram.

I checked B–E of delivery-errors.md against the resulting files. There are no unsplit new statements carrying proofs, no hidden new notions, no tag-only citations, no duplicate new lemmas, no unquoted dependencies and no clauses merely moved into new nodes. Every cited node's statement was read and its exact used clause is included in citations.json. The proofs depend on the flat-square sibling, which has no dependency back to this item; the generic Mathlib mate leaf and the ring-sheaf tool also do not depend on the item. Each step is below 1000 characters, so no long step hides an untracked argument. The ring-sheaf comparison is declared in split_report.tool_uses as a generic formal tool; it does not change the unit's route.

Small cases: for f the identity all geometric units/counits and normalized pullback comparisons become identities, and h is the identity tensor comparison. For a the identity, C and B are tensor units, so projection's stated unit normalization gives the identity on G_R K. For S the zero ring both sides have zero source and target. For K=0 both maps are zero. A complex unbounded in either direction causes no change: every invoked node explicitly uses ordinary unbounded categories, and the argument takes Hom transposes without truncations or cohomology. No flatness, finite rank or cohomological dimension was inferred beyond the given exact scalar extension hypothesis.

## Unfinished work

None at the stage-1 level of this item. The cited existing unsplit normalization lemmas remain their own DAG items. Required remote dry run and delivery follow this report.
