# Q11 stage-1 delivery

Item: lem-sfb-henselian-unavoidable-component-valuation-section.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-henselian-unavoidable-component-valuation-section.json: statement unchanged; twelve-step split, using existing DAG statements only. Mathlib verdict: no matching theorem for the whole item.
- citations.json: one entry per step/cited node, quoting its actual statement verbatim.
- report.md: this report. searches.jsonl records the new searches actually executed by msearch.py. write_split.py is sandbox scratch work, not a DAG delivery file.

No new nodes and no new Mathlib leaves. The two unpublished nodes in the interrupted draft have been removed: the valuation clause is proved in steps 1-3; the proposed large component-section lemma is replaced by the argument in steps 4-12.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag, unavoidable, and henselian/component terminology found no finished declaration stating the item. The existing scheme-image base-change declaration supplies only an input, not this item. No Lean was written or compiled.

## Literature

WANTED: literature/anantharaman-groupes-dimension-un.pdf, Lemma 4.2.1, printed pp.55-56, for the finite-normalization model input used by this item. The local archive lacks the PDF. I read these pages in the primary Numdam scan https://www.numdam.org/article/MSMF_1973__33__5_0.pdf without downloading it into the repository. The source is about fpqc schematicity after normalization in a finite field extension; the current auxiliary statement is not claimed to be verbatim in that paper. The proof_origin is agent.

I read the relevant local Stacks statements and proofs: More Algebra 092X (integral domain over a henselian local ring), Algebra 09IG (finite-extension normalization is Dedekind), 00PD (DVR equivalences and uniformizer powers), Morphisms 01R8 (quasi-compact schematic image and topological density), 081I (flat base change of that image), Descent 03N0 (compatible opens descend fpqc), More Morphisms 05GU (nearby-open quasi-sections), Fields 09GU (embedding an algebraic extension), 0BR4 (normal embeddings differ by automorphisms), and the first paragraph of the proof of Varieties 04L7 (geometric component surjectivity, with 04KZ/038H). The reduced closed structure is the existing 01J3 node. No SGA source is used.

## Corrections and remaining work

The imported statement needs no correction. The interrupted draft did: it appealed to locally finite components on an arbitrary fpqc chart without proving a Noetherian hypothesis, and hid most of the target in a new lemma. The replacement takes a Noetherian finite-normalization model first. It then uses quasi-compact scheme images, whose flat base-change theorem has no Noetherian hypothesis, to descend the complement. Component closure arguments take place only on the Noetherian model. The draft also inaccurately said the Anantharaman PDF was locally present; the WANTED line above corrects that claim.

The initial resumed dry run exited with SEARCH CHECK FAILED for the two removed draft nodes, whose searches were not in this item's log. No push occurred. I have not invented or transferred search-log entries. The final split creates no nodes. All inherited item searches remain, and four further actual msearch searches have been added after reading their hits. The semantic hits concern generic points, arbitrary valuative squares or properness; they do not supply this nonproper section-existence theorem. The new Loogle and grep queries returned no hits.

No mathematical argument remains unfinished. The required final dry run and push are the remaining delivery actions.

## Blueprint and route

I read the chapter and unit records, GOAL.md and SETUP.md's three levels, and the latest blueprint's ctf-stability proof and direct-images proof (latest snapshot main-20261024). This is a pre-existing auxiliary input on the inherited long alteration/group-effectivity chain, serving the simultaneous-specialization argument after Anantharaman 4.2.4, not a replacement for the six-functor route. The item has no nearest imported blueprint ancestor (blueprint_refs ancestor reports None); its full inherited via list is retained. The blueprint search for unavoidable found no identical statement; same_as remains empty. Generic algebra, scheme-image, reduction and descent inputs from other units are recorded with individual reasons in split_report.tool_uses, for maintainer assessment.

## Not duplicates

No new nodes. The general henselian-permanence, finite-normalization, dense-generic-trait-selection, geometric-component-surjectivity, embedding and scheme-image/descent inputs already exist and are cited, rather than duplicated. In particular the two unpublished draft node files are not part of this delivery.

## Review by Q11

I checked delivery-errors B-E against the replacement split. There are no new statements to hide hypotheses or to restate clauses of the item. I opened each cited node's statement, and citations.json quotes those statements rather than their proofs. I checked the following uses and hypotheses.

Step 1 uses integral-closure-algebraic-extension-normal for the domain, integrality, normality and fraction field of B, and integral-component-henselian-permanence for locality and the local map. The idempotent hypothesis follows explicitly from the domain identity e(e-1)=0. Thus the closed point is actually over s.

Step 2 applies the same facts to each finite E/K, integral-closure-dedekind-surjective-fibres for the Noetherian dimension-one assertion, and normal-dim1-dvr only after normality and locality have both been supplied. The definition of a DVR supplies the principal-ideal/Noetherian and dimension-one hypotheses on R. No excellence or separability is used. Step 3 uses the unit-times-uniformizer-power statement for numerators and denominators and writes the two signs of the exponent; this proves the valuation condition rather than delegating it to a new node.

Step 4 uses exactly the finite-normalization schematic-model conclusion of fpqc-finite-presentation-normalization-model, the algebraic-extension embedding statement, and finite-type-over-Noetherian. Its base really is a normal dimension-one Noetherian domain: normality is proved by dividing a monic equation by a negative-valuation leading power. I corrected the draft's implicit assumption of normality of an arbitrary DVR by writing that argument. Step 5 uses finite Noetherian irreducible-component decomposition and the covering statement to prove clopenness by intersection classes. The quasi-compactness of C_L to Y is checked on every affine via the principal generic open and a closed immersion, so it does not assume that an arbitrary open immersion is quasi-compact.

Step 6 takes the closure equality from lemma-nagata-scheme-image-ideal-qc, and the actual closed-subscheme equality after flat pullback from scheme-image-flat-base-change. Both overlap projections are flat by fpqc base change. Thus it never substitutes ordinary closure for a flat-base-change theorem. Step 7 uses open-subscheme-fpqc-descent on each scheme test, not a descent assertion for an unrepresented X. The compatibility follows from step 6, and uniqueness supplies functoriality. The fpqc sheaf equalizer condition identifies the resulting subfunctor after pullback. Its generic fibre excludes precisely C; if the special closure were empty it would contradict exactly the given unavoidability hypothesis.

Step 8 uses finitely-many-components and components-cover to make a finite union of closures, and reduced-induced-closed-subscheme for the real reduced structure on one irreducible closure meeting the special fibre. Reduced plus irreducible is integral by the integral-scheme definition. Finite type is verified by quotient coordinate algebras on a finite affine cover. The generic factorization is through the open C_L; no closed-subscheme factorization is inferred merely from points. Step 9 checks every hypothesis of dense-generic-trait-selection: A is a DVR, W is integral finite type and dominant, and its special fibre is nonempty. The selected open is the whole nonempty generic fibre. The quoted statement explicitly gives a finite fraction field, a local injection and the desired generic and closed values.

Step 10 proves equality of the selected DVR with A_E; it does not cite valuation uniqueness with an unchecked field or completeness hypothesis. Integral elements belong to V by the explicit monic-equation argument. The uniformizer-power statement makes the exponent of the R-uniformizer positive and rules out every negative power in V. This yields the actual inclusion A_E=V in B used to pull back the section. The residue field of its generic point is a subfield of the finite extension E, hence finite over K.

Step 11 uses the precise surjectivity clause of geometric-connected-component-surjective, whose connectedness, nonemptiness, local finite type and finite-component assumptions on C were established in step 5. The reduction definition ensures it applies to the same underlying components as in the question. The affine fibre-product statement and finite-dimensional residue-algebra argument produce an Omega-valued point in the prescribed component over the same finite-residue-field point as the first section. Step 12 uses algebraic-extension-embeds-algebraically-closed to extend that embedding and normal-embeddings-automorphism-transitive to make it an automorphism, with algebraicity and normality of Omega/K verified. Applying the automorphism and its inverse to monic equations proves preservation of B. On points the composition sends alpha to tau alpha=beta; this fixes the contravariant direction. Locality from step 1 gives the special value.

I tested the argument on X with empty special fibre (then no nonempty C is unavoidable), on a component entirely confined to the generic fibre (its complement gives the forbidden U), on X=Spec R, on purely inseparable finite generic field extensions, and on a henselian DVR without an excellence assumption. Nilpotents in X are harmless because schematic images precede reduction and the selected closure is reduced explicitly. The geometric-component step uses the reduction only for underlying topology and imposes no reducedness or perfection hypothesis on C. These tests required no statement change. No step exceeds 2000 characters; the two elementary steps are the explicit uniformizer fraction and local-overring calculations from already cited facts, not hidden section-existence lemmas.
