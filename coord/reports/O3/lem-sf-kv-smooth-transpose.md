## Files written

- dag/nodes/sec-six-functors/lem-sf-kv-smooth-transpose.json: item, split into six steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors/lem-sf-exterior-shriek-projection-compatibility.json: one new statement-only, unsplit lemma; no Mathlib match. It states that the ordinary compact-support exterior comparison respects tensoring by a target complex. It has neither smoothness nor exceptional inverse images.
- citations.json: a verbatim statement quotation for every proof-step citation. The full statements are retained so that the defining transpose formulas and their domain restrictions remain visible.
- searches.jsonl: retained the interrupted attempt's searches; appended actual search results through msearch.py. write_split.py is a sandbox-only preparation script.

## Attachments

None. Searched the project source for the exact blueprint tag and for smooth/transpose and Kunneth comparisons. Etale/Derived/Kunneth/Comparisons.lean defines a comparison interface and proves hasKunnethComparisons with sorry (line 166); it does not prove this equality of specified maps. Etale/Derived/ProjectionFormulaAssoc.lean supplies separate ordinary-direct-image and open-extension associativity lemmas, not the new exterior compact-support square for arbitrary f. No exact closed project declaration was found for either delivered node. The upstream master was not treated as evidence of a completed proof.

## WANTED

None. The needed lecture notes and blueprint are available locally. No SGA source is used.

## Corrections and route

The imported item had no proof. Its statement is well typed with the canonical signed reassociations indicated there, and no statement correction is needed. I retained its finite coefficient ring, actual pro-etale operations, constructible exceptional adjoints, separated finite-type scheme domain, all K,Q, and equality of the specified transformations. I did not assume an unrestricted ambient pro-etale exceptional adjoint or an admissibility datum.

The blueprint's alpha paragraph says that the smooth trace is the exceptional counit and its base-change square is the transpose of the same comparison. The split writes that argument as a calculation, using Scholze, Six-Functor Formalisms, Definition 5.1 for the two specified transposes. The lower module-coherence input is Remark 3.13 and the preceding discussion on p. 24 (compatibility of composites of correspondences). This is the lecture-notes route and uses no smooth trace/orientation theorem from a different source. No Tate orientation, fundamental class, or SGA trace normalization is introduced.

The only new lemma records an actual missing square: a comparison between extracting a pulled-back target factor before and after the compact-support exterior comparison. It is not the exceptional identity or a clause of it. In a later split it can be obtained by tensor associativity of the projection map and its base-change square, with the concrete compactification normalization of def-exchange-projection. The existing statements give base-change coherence or composition in f; they do not explicitly state this tensor-module square. I did not leave that square hidden behind the phrase 'by coherence'.

## Not duplicates

lem-sf-exterior-shriek-projection-compatibility vs prop-sf-pf-coherence: the existing statement supplies PF naturality, composition in morphisms and its base-change square in a six-functor datum; it does not state tensor associativity in two target complexes or the displayed exterior module identity for the actual operations.

lem-sf-exterior-shriek-projection-compatibility vs lem-sf-kunneth-coherence: symmetry, triple relative products, base change and the identity-factor PF normalization are stated there; the new lemma states the explicit square for tensoring an arbitrary source complex with a target pullback, with all exchange/PF factors fixed.

lem-sf-exterior-shriek-projection-compatibility vs lem-weil-pbc-ringed-exchange-tensor-coherence: the latter concerns ordinary Rf_* for ringed topoi, with its counit-defined projection map; the new lemma concerns compact support for arbitrary separated finite-type f and includes the tensor-module extraction square with a second exterior factor.

lem-sf-exterior-shriek-projection-compatibility vs lem-sf-kv-smooth-transpose: the new statement contains no exceptional functor, theta, dualizing object or smoothness assumption; the item proves the equality of two exceptional-adjoint comparisons by evaluating both counits.

lem-sf-exterior-shriek-projection-compatibility vs lem-sf-product-compactification-identity: the existing lemma compares relative product maps under a product compactification; it does not assert the target tensor-action identity.

Whole-DAG searches used projectionMap_assoc/ProjectionFormulaAssoc, exterior/external projection terms, and module/tensor associativity, followed by reading the nearby statements. Blueprint searches included 'projection formula', 'tensor associativity', 'projection formula associativity', 'projection tensor', 'exterior projection', 'compact support exterior' and 'smooth transpose'. None states the new square. The ancestry tool returned sk-thm-sf-kunneth-verdier; the new node carries via=[lem-sf-kv-smooth-transpose]. No Stacks tag is assigned to this categorical lecture-notes identity, so there are no same-tag pairs to disambiguate.

## Review by N3

I read the chapter/unit records, the main-20261015 alpha proof paragraph, the complete statements of every cited node, and Scholze's Definition 5.1 and Remark 3.13. The item agrees with Definition 5.1's actual maps: theta is transposed from inverse PF followed by the exceptional counit; b is transposed from inverse compact-support exchange followed by pullback of that same counit. Smoothness is used only to invert theta. The new statement is the target-module compatibility from the correspondence discussion and Remark 3.13, specialized to the concrete product square, and explicitly retains all three arbitrary finite-Tor complexes M,K,Q.

Step 1 uses thm-sf-ctf-stability only for its finite-coefficient clauses (i),(ii),(iv),(v); these state precisely the four closures needed. thm-pur-cohomological-smoothness supplies invertibility of theta, and lem-pur-derived-pullback-tensor-iso supplies coherent signed monoidal pullbacks. sk-def-sf-operations fixes the actual adjunctions, rather than an assumed ambient datum. On final review I strengthened the child's displayed square to include extracting the combined factor W directly, so that no additional tensor-associativity law for PF is hidden in step 3. This is still the same ordinary module-comparison obligation, not an exceptional lemma. The source and target of T are H boxtimes Q and f^!K boxtimes Q; cancelling T is therefore legitimate. The unit and identity adjunction identifications are ordinary adjunction uniqueness, not a geometric theorem.

Step 2 reads the explicit composite in sk-thm-sf-kunneth-relative, not its proof: over B=Y times Z one of its morphisms is the identity, so its PF and composition comparisons are identities. The other PF is the one for F; identifying its first target factor with s^*Rf_!M uses exactly E_M inverse. This gives the C defined in the child. sk-def-sf-kv-maps(ii) defines alpha as the counit transpose of this Ku_!, so its stated transpose is exactly the displayed one. Naturality allows precomposition by theta without changing any chosen comparison.

Step 3 uses def-pur-co-smoothness(2)'s full formula, including the initial symmetry, to rewrite epsilon P(theta). The new lemma gives precisely the square used when extracting K through C, with K and Q already combined into the single target factor W on its right-hand side. Its zeta, after swapping f^*K and omega, is exactly sigma rho; this yields the displayed formula a with domain P_F(H boxtimes Q) and codomain W. This is the mathematical content isolated from the source's implicit module coherence; it was not taken from a definition or from a proof of an unrelated lemma.

Step 4 again uses the theta formula in def-pur-co-smoothness(2), now for F,W. Naturality of the concrete PF is explicitly part of fix-prop-projection-formula; moving b through it has first argument r^*omega and target factor W. All these objects lie in the finite-Tor domain verified in step 1. No identification of omega with a twist/shift is needed, so signs are exactly the canonical tensor symmetries rather than an additional orientation convention.

Step 5 uses the complete displayed formula of def-pur-co-smoothness(3): epsilon_F P_F(b)=s^*(epsilon_f) E_omega inverse, with no smoothness assumption on s. This is the same product square and same specified Ex_! as the new lemma. Substitution makes the two transposes identical. thm-sf-ambient-adjoint-class(2),(3) gives an actual natural Hom bijection for bounded-below etale-origin source objects and compatibility with compactifications; it explicitly includes bounded constructible inputs. Here the source H boxtimes Q is in that class. The finite-dimensional compactification required there is the one underlying the operations in sk-def-sf-operations(vi), which states the resulting constructible adjunction. No ambient unbounded pro-etale adjunction is inferred. Injectivity of a bijection and cancellation of an isomorphism are elementary.

Step 6 is elementary componentwise equality of natural transformations; the input maps' naturalities were supplied in the earlier cited statements. It introduces no additional comparison.

For the new node I checked both paths have domain P_F((M tensor f^*K) boxtimes Q) and target (P_fM boxtimes Q) tensor s^*K. Its zeta and output associator preserve the order M,K,Q. In the item, the initial swap of f^*K and omega supplies exactly the signed symmetry appearing in theta; there is no extra crossing of K and Q. Tested f=id (all exchanges are identities, and the equation is tensor coherence), Z=Spec k and Q=A (the target module law for PF), K=A (unit compatibility), and zero M/K/Q or empty schemes (both maps are zero). These tests do not exclude any allowed input and produce no counterexample. The arbitrary target K need not be lisse or dualizable. No hypothesis of properness, smoothness of Z, or flatness of an individual complex was silently added.

The Mathlib search logs from the interrupted attempt were read and reused. Additional exact searches found monoidal adjunction counit identities and Cartesian Frobenius maps; I read Mathlib/CategoryTheory/Monoidal/Functor.lean 1024-1039 and Monoidal/Closed/Functor.lean 46-70. Those do not state the compact-support exterior square. The project-only ProjectionFormulaAssoc lemmas are restricted to ordinary direct image or open extension and do not justify attaching the new statement. One interrupted-attempt LeanFinder service failure remains recorded as unavailable. Every recorded query is an actual msearch.py log entry.

I checked B1-B9 (statement-only child, all objects/hypotheses introduced, definitions cited, literal TeX, exact source place, truthful searches, blueprint ancestry), C1-C8 (statement-level citations, no uncited module comparison, no conditional exceptional assumption), D1-D5 (the item carries its counit argument rather than applying a renamed exceptional identity), and E1-E7 (domains, square labels, signs, source intent and edge cases). There are no non-elementary steps over 2000 characters. The report and searches from the interrupted attempt were not discarded; there was no prior split/report or running delivery to repeat.

## Unfinished work

No obligation of this one-level split is left unstated. The new module-comparison lemma remains unsplit by the stage-1 contract. Its eventual proof should use the concrete ordinary/open compactification PF construction, not assume the item's smooth comparison.

## Validation

The first server review_split passed, and the first full dry run passed at cc1451c58f. After the final mathematical self-check above, I made the combined-target formula explicit and will rerun the dry run before pushing. No Lean, Lake or compiler was run, and the shared repository and source checkouts were read only.
