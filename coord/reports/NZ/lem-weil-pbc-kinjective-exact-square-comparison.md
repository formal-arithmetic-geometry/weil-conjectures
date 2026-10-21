# Stage-1 report: lem-weil-pbc-kinjective-exact-square-comparison

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-kinjective-exact-square-comparison.json: item, statement; split in six steps using existing nodes, no Mathlib match for the whole item.
- citations.json: six step/node entries with verbatim statement excerpts.
- report.md: report and independent self-review by NZ.

No new nodes and no new Mathlib leaves. The sandbox initially contained only launcher brief markers, so there was no earlier split or report to overwrite. The repository item was copied, its statement and existing search records retained, and the five current logged searches appended. write_split.py is a sandbox-only preparation script.

## Attachments

None. Searched the project library under lean/WeilConjectures for the exact item id/docstring tag and for K-injective, exact-square and normalized-comparison terminology. Read CategoryTheory/DerivedCategory/RightDerivedFunctor/KInjective.lean: its exists_iso_Q_obj_of_isKInjective and rightDerivedFunctorObjQIso cover representative existence and unit computation, not the normalized comparison or its uniqueness. They also use HasKInjectiveResolutions rather than just the arbitrary quasi-isomorphism hypothesis of this item. No project declaration found states all clauses under the item's assumptions.

## WANTED

None. All literature used is present.

## Problems found and changes

The original item had a statement and search records but no proof. Its statement is correct with its explicitly prescribed exact-functor localization identifications. I kept it unchanged. To prevent a hidden type mismatch, step 1 writes the actual maps with the factorization isomorphisms lambda: b_J includes RH(lambda_r,J inverse), while a_J includes lambda_s,H'J inverse. Their common source is Q(HrJ). The statement's suppressed identifications mean exactly these maps.

The current blueprint source is literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, first sentence. I read that source and the parent tower-derived-evaluation-normalization statement. This item proves the generic normalization/descent part used for tower evaluation; it makes no assertion that arbitrary varying-ring evaluation preserves K-injectives. No chapter or unit route was replaced, and no unit realization file is needed for this non-key node.

Read Stacks derived.tex Tags 070I (lemma-K-injective), 070Y (lemma-K-injective-defined), and 070K (lemma-enough-K-injectives-implies). The exact-square extraction and the choice-independence calculation are written here, so proof_origin is agent rather than claiming Stacks states this entire comparison theorem. No prohibited SGA source is used.

## Mathlib and duplicate searches

Ran the prescribed msearch.py command for LeanSearch, Loogle, grep and two LeanFinder phrasings; all returned successfully. The exact queries and actual hit summaries are appended to mathlib_searches and retained in searches.jsonl. Read the candidate declarations in Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean:46-125 and Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean:100-146. rightDerivedFunctorComparison assumes its source composite already has the derived universal property, and its isomorphism instance has right-derivability hypotheses not given here as instances. rightDerivedNatIso/rightDerivedUnique require two universal derived pairs. Establishing the needed composite universal properties is an argument, not a one-line specialization. Ordinary injective-resolution hits do not concern this unbounded statement. Therefore the whole item is not a Mathlib leaf.

Searched the whole DAG by the Stacks tags and K-injective/Hom/localization concepts and ran blueprint_refs.py ancestor and searches for K-injective, normalized right derived comparison, and exact square. Reused lem-weil-pbc-kinjective-hom-derived, an existing Mathlib leaf for precisely the Hom bijection. Read its full statement and Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean:41-56. Reused lem-weil-pbc-exact-functor-derived-factorization and read Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:36-76. Read def-sfb-right-derived-functor and def-weil-abstract-derived-category in full. The latter two supply the existing units/computation convention and the localization, respectively.

The other normalized common-resolution node, lem-sf-normalized-derived-comparison-common-resolution, assumes a supplied normalized comparison and computes it under resolutions, without assuming r preserves K-injectives; it does not construct or uniquely characterize this item's comparison. It is not used. The blueprint searches found no blueprint node stating this exact generic theorem in another form; same_as remains [].

## Not duplicates

No new nodes were created, hence there are no new/existing same-tag pairs. The descent calculation is kept in the item's proof rather than made into a node restating its clauses.

## Unfinished work

None in the mathematical split. The required dry run and direct push are the remaining delivery operations when this report is first written.

## Review by NZ

I checked the node against the source and delivery-errors B-E with the cited statements open. There is no statement dispute or hypothesis added. In particular H and H' need only be additive, neither left exact nor an adjoint; r and s are exact, r preserves K-injectives, and both source abelian categories have the assumed arbitrary quasi-isomorphic K-injective replacements. No functorial, monomorphic, termwise injective or bounded-below replacement is used.

For step 1, the exact-functor factorization node explicitly gives the natural localization isomorphisms, and def-sfb-right-derived-functor explicitly gives invertibility of the unit on K-injectives. Applying these to J and rJ gives the two typed maps. The K-injectivity of rJ is the actual hypothesis, not an inferred consequence of exactness. This is a direct application of stated properties and inverse cancellation.

For step 2, I checked that the derived-functor definition supplies a natural unit on the homotopy category, and the factorization statement supplies a natural isomorphism. Additivity preserves a chain homotopy by the written dk+kd identity. The two naturality equations then give the delta equation by the explicitly stated multiplication by inverses. Thus the step does not silently assume H or H' preserves quasi-isomorphisms.

For step 3, lem-weil-pbc-kinjective-hom-derived explicitly states the Hom bijection for any source complex and a K-injective target. Both endpoints here are K-injective and the target condition is satisfied. This supplies every derived map between them, not only a chain map over some chosen resolution. The statement of def-weil-abstract-derived-category is a localization of the complex category: represent an object by a complex and compose its representing isomorphism with Q of the assumed resolution. No resolution-existence theorem with stronger assumptions is cited. This is the sole non-elementary proof step, using the existing Mathlib Hom-bijection leaf.

Steps 4-6 use only the results already established inside this proof and category identities, so their uses lists are empty and they are marked elementary. I checked the orders and domains in t=v u inverse for independence and t=v f u inverse for naturality. The displayed conjugation calculations establish independence of the target representative and the chosen isomorphism, then naturality for every derived morphism f. The inverse naturality follows by multiplying by the component inverses. Normalization follows from the identity representative. Finally the normalization equation cancels a_J only on K-injectives, and naturality along u determines every other component; no normalization on all complexes is smuggled in.

For small cases I checked identity squares with identical chosen derived pairs (delta and beta are identities), identity ordinary functors with differently chosen universal pairs (beta is the unit-compatible comparison rather than an assumed identity), zero functors/zero categories (all maps are isomorphisms between zero objects), acyclic source objects (their representatives and conjugation equations still apply), nontrivial automorphisms of QJ (step 4 forces independence), and arbitrary morphisms rather than just isomorphisms (step 5 uses unrestricted t). These checks expose no missing nonzero, boundedness, adjunction or tower hypothesis.

I also checked B: no new unsplit statement, unexplained notion, duplicate, false Mathlib claim or fake search record was introduced; C: every cited statement actually supplies its used fact and every non-elementary fact is cited; D: all six clauses are proved inside this item with no relabelled child; E: exactness and K-injectivity are used in their stated domains, with all comparison equations written out. The largest step is under 800 characters, so there is no over-2000-character step hiding a lemma. The six verbatim citations were checked against the current repository statements. No writes to the repository/launcher, git commands in the repository, Lean writes or compiler/build commands were made.
