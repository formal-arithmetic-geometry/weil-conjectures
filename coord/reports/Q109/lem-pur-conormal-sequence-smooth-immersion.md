## Worker report

Q109, stage 1, 2026-10-17. Item: lem-pur-conormal-sequence-smooth-immersion.

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-conormal-sequence-smooth-immersion.json: statement, split into eight proof steps; no exact Mathlib match for the scheme fibre assertion.
- citations.json: a verbatim statement quote for each of the twenty step/node citations. Full statements are quoted so that the hypotheses remain visible to the next reader.
- searches.jsonl: actual msearch results, retained with their original query strings and results. The new search records are appended to the item's inherited searches; the inherited records were not rewritten.
- report.md: this report.

New nodes: none. New Mathlib leaves: none. The proof reuses existing Mathlib leaves for the quotient differential sequence, affine closed immersions, affine stalks, the stalk map of Spec, quotient localization and tilde stalks, together with existing definition nodes. In particular, no new node packages the item's injectivity or full exactness.

Attachments: none. A search of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint id and for conormal terminology found no declaration of this item. The only conormal text hit was DeformationToNormalCone.lean:47, a TODO about a future construction, which I opened and did not treat as a proof. The item's slopmaster2 state is none. The upstream master checkout was not used as proof evidence.

WANTED: none. All sources used were available in literature/stacks-project/.

The imported statement is correct, including its generality: X need not be smooth, locally Noetherian or of finite type over k. Only Z is assumed smooth, and z need not be closed. I kept the statement and all its statement dependencies unchanged. The item had no proof; its source explains residue-field exactness using local freeness, but a more explicit split-sequence proof avoids needing a flatness argument. The split supplies this argument, including its square-zero lift, retraction, splitting identities, localization identifications and the two prescribed arrows. There was no statement dispute or source error.

Nothing mathematical remains unfinished in this one-level split. The subsequent second reading and delivery belong to the next worker. No Lean file, compiler, Lake, local preflight script, git command or shared-project file was used for a mutation.

## Sources and route

I read morphisms.tex, lemma-differentials-relative-immersion-smooth (Tag 06AA), including its reduction to the ring sequence, and lemma-differentials-relative-immersion, which specifies the differential arrows. I read algebra.tex, lemma-differential-seq (Tag 00RU) and its proof, lemma-differential-seq-split (Tag 02HP) and its derivation construction, lemma-differential-seq-smooth (Tag 06A8), and lemma-differential-seq-formally-smooth (Tag 06A6). I also read morphisms.tex, lemma-smooth-omega-finite-locally-free (02G1), to check the item's original fibre-exactness explanation. The proof instead exhibits a splitting and tensors its identities.

For lifting I read more-morphisms.tex, definition-thickening (04EX) and definition-formally-smooth (02H0). This definition does give a lift on the whole affine test scheme, exactly as the cited smooth-morphism definition says; no global lifting across a nonaffine test scheme is used. The open-image factorization is written from the open-subscheme definition, rather than asserted for a closed subscheme based solely on its set of points.

The chapter record sec-smooth-purity, unit record sk-prop-an, and current main-20261015 proof of lem-pur-regular-immersion-linearization were read. The latter's first paragraph displays this very fibre sequence, and the following sentence specifies [f_i] maps to df_i. Those are the exact places realized here. The item is not the unit's key statement and no unit record is changed. All statement lemmas used from other units are already Mathlib leaves; the other dependencies are definition nodes. Thus no off-route theorem or replacement of a unit step is involved, and no SGA source is used.

## Searches and existing nodes

Before writing, I searched the whole DAG for 06AA, 02G1, conormal exactness, square-zero retractions, quotient differential maps and localization. I used tools/blueprint_refs.py ancestor for the item and search with 'conormal sequence', 'conormal', 'differential-seq', 'square-zero', 'localization differentials' and 'smooth affine'. No blueprint node repeats the item's assertion in another form; blueprint.same_as remains []. I preserved its precise blueprint.from.place and ancestor.

The useful existing node is lem-weil-pbc-jacobi-zariski-differential-maps: its statement includes BOTH exactness at the tensor differential module and surjectivity of the map to quotient differentials, with the arrow formulas. It is not lem-weil-pbc-smooth-conormal-sequence-exact, which instead compares the two kernels in A -> B -> C when A -> B is smooth; that different theorem would not justify this step. I also rejected use of the fixed-dimension version lem-sc-smooth-omega-finite-locally-free for an unproved constant relative dimension. No new smooth-conormal lemma was created.

The actual item searches used msearch.py: LeanFinder with the fibre-sequence phrasing, a second phrasing for arbitrary surjective algebra maps, Loogle 'KaehlerDifferential, "exact"', grep 'conormal|differential.*stalk' in AlgebraicGeometry, grep of the conormal-exactness and split-injection names in RingTheory, and LeanSearch with the scheme fibre statement. All services returned results. The algebraic exactness hits are precisely the already-existing quotient differential leaf. I opened Mathlib/RingTheory/Kaehler/Basic.lean:839 and the nearby mapBaseChange_surjective declaration, and Smooth/Basic.lean:291. The latter needs formally smooth ambient algebra P, which the item does not assume. Neither these nor the closed-immersion hits give the full scheme/stalk assertion in one line.

## Not duplicates

No new nodes were created. The elementary square-zero retraction calculation, splitting calculation, tensor identities and conormal-localization calculation are proof steps of the item, not duplicate nodes.

## Review by Q109

I checked the statement against 06AA rather than silently adding smoothness of X. The source has an arbitrary immersion with smooth source; the item's closed immersion over a field is a legitimate specialization. Tensoring a merely short exact sequence with the residue field would not automatically preserve injectivity, so the proof first produces a splitting. None of the split's supporting facts is taken from an internal proof of another node: all twenty citations quote the statements actually used.

Step 1 uses lem-weil-pbc-closed-immersion-affine-cover-criterion for the two facts its clause (1) explicitly states: the inverse image of an affine open is affine and the sections map is surjective. def-weil-affine-spectrum supplies the ring/scheme correspondence. def-weil-pbc-kahler-differentials introduces the actual modules and derivations. Thus A -> B is a surjective k-algebra map, without any finite-generation claim about J.

Step 2 uses the SAME closed-immersion criterion, now clause (2) on the one-affine cover, for Spec(C/K) -> Spec(C). def-sbc-first-order-thickening supplies the square-zero test condition and the equality of underlying spaces. def-sbc-smooth-morphisms explicitly includes the lifting property for affine first order thickenings. Both T and T' are affine and all maps are over k. The lift lands in V because T -> T' is surjective on points; the restriction of a scheme map to an open subspace factors directly by restricting its sheaf map, as defined in def-weil-open-immersion. The affine spectrum correspondence then gives sigma with pi sigma = id. These are applications of the cited definitions with the required hypotheses and an explicit open restriction, so this step is elementary despite using the lifting property. I did not assume a theorem that S, a localization at a possibly nonclosed point, is a finitely presented smooth k-algebra.

Step 3 uses lem-weil-pbc-jacobi-zariski-differential-maps exactly for its displayed sequence, the generator formulas, ker(w) = im(delta), and surjectivity of w, substituting the ring tower k -> A -> B. Its statement has no smoothness hypothesis and supplies no left injectivity, which is why step 4 is necessary. I read the entire statement and the source proof of 00RU.

Step 4 uses the universal derivation in def-weil-pbc-kahler-differentials and scalar extension in def-weil-module-base-change. I checked the product computation in C explicitly: the product of the two D terms is zero, and C acts on K through B. D vanishes on k since sigma is a k-algebra map. For j in J the value is exactly its class, so tau delta = id. This is the short derivation calculation of 02HP, written out here and not hidden in a new node. In particular this step is an argument from definitions, not a definition cited as a substitute for an unstated theorem about flatness.

Step 5 has no external citation: the representative formula for s(p) is independent of the lift precisely by ker(w) = im(delta) from step 3 and tau delta = id from step 4. Subtracting the two representatives proves well-definedness and linearity. The four identities are then immediate substitutions. Step 6 uses the additive functoriality explicitly stated in def-weil-module-base-change. The displayed decomposition identity proves kernel equals image after tensoring, and both end conditions follow from the retractions. Thus neither preservation of general exact sequences nor flatness of the residue field is an uncited assumption.

Step 7 uses lem-weil-pbc-affine-open-stalk-localization for R and S, lem-weil-pbc-spec-map-stalk-localization for their actual ring map on fractions, and lem-weil-pbc-localization-at-prime-of-quotient for its kernel JR and quotient. The statements give these precise assertions, not just abstract existence of unrelated isomorphisms. I checked that p is the inverse image of q. The equality of ideal squares after localization is proved by multiplying fractions; injectivity of the conormal localization map is checked by a common denominator and the localization equivalence relation. The inverse tensor formula uses only that denominators outside q act by units on kappa. There is no appeal to an unstated exactness-of-localization theorem.

Step 8 uses def-sc-relative-differential-sheaf for the affine tilde descriptions and their specified derivations, and lem-weil-pbc-spec-tilde-stalk-localization for the germ-to-fraction identification of module stalks. Those are the exact available statements. I wrote both tensor comparison maps and their denominator inverses. Finally, using the Leibniz rule in def-weil-pbc-kahler-differentials, the term j t^(-2) dt is killed in kappa, proving the first-arrow normalization for an arbitrary local equation j/t. The second arrow is checked on differential generators and denominators. This makes the compatibility asserted by the item explicit instead of calling it transport.

Small cases: for the identity immersion J = 0 and the sequence reduces to the identity on differentials. For Z empty there is no z. For Z = Spec(k) in X = Spec(k[e]/(e^2)), the ambient scheme is nonsmooth, but J/J^2 and the differential fibre both have basis e and de respectively, so the left arrow is an isomorphism as predicted (also in characteristic 2). For a nonclosed generic point of a smooth positive-dimensional Z the construction still uses the original affine B in the lifting step and only then localizes, avoiding a finite-presentation error. Zero conormal module, positive characteristic, and varying component dimensions cause no change in any splitting identity. No separability or perfectness of k is used or needed.

I checked B1-B9: there are no new unsplit nodes or leaf records to audit, the item is self-contained, citations of notions are preserved, TeX is encoded once, and the blueprint ancestor/place is exact. For C1-C8 I opened every cited statement, recorded the full statement quotes, verified that proof_deps is the union of uses, and traversed dependencies to exclude a cycle back to the item. The theorem citations are existing Mathlib leaves, so they do not replace a unit route. D1-D5 are addressed by carrying the retraction and splitting arguments in the item itself rather than moving its content into a new node. For E1-E6 the affine test hypotheses, actual local-ring maps, nilpotent rather than reduced thickening, denominator compatibility, and residue-field tensor exactness were checked above. E7 revealed no source error. During self-review I added the affine closed-immersion criterion also to step 2, since its converse is what justifies calling Spec(B) -> Spec(C) a closed immersion. No other statement or node needed repair.

## Validation

The required server dry run is the final check. No local invocation of check_dag.py, review_split.py or preflight_delivery.py is permitted or used. This sandbox is for second reading; no push is authorized in this worker turn.

## Second reading by Q109

I reopened the source files and every cited DAG statement. The item statement agrees hypothesis by hypothesis with morphisms.tex Tag 06AA (lemma-differentials-relative-immersion-smooth), specialized to a closed immersion over the field k: X is arbitrary, Z is smooth over k, and the sequence is taken at an arbitrary z, including nonclosed points. The prescribed arrows agree with the differential maps in Tag 06AA and its underlying Tag 00RU construction.

Step 1: checked against Tag 06AA's affine reduction and the statement of lem-weil-pbc-closed-immersion-affine-cover-criterion, def-weil-affine-spectrum, and def-weil-pbc-kahler-differentials. Verdict: the affine rings, kernel J, quotient N, and differential modules are introduced with the required actions and no finite-generation hypothesis.

Step 2: checked against def-sbc-first-order-thickening, def-sbc-smooth-morphisms (Tag 02H0), def-weil-open-immersion, def-weil-affine-spectrum, and the converse clause of lem-weil-pbc-closed-immersion-affine-cover-criterion. Verdict: C=A/J^2 gives a square-zero affine thickening, the smooth lifting property applies to T=Spec B over Spec k, and equality of underlying spaces forces the lift through V; no localization is incorrectly assumed smooth or finitely presented.

Step 3: checked against the full statement of lem-weil-pbc-jacobi-zariski-differential-maps (Tag 00RU). Verdict: its displayed maps, formulas, right exactness, and only the claimed kernel equality are used; left injectivity is correctly deferred.

Step 4: checked against def-weil-pbc-kahler-differentials, def-weil-module-base-change, and the derivation construction in Tag 02HP. Verdict: the square-zero product calculation gives a k-derivation, JN=0 gives the B-linear retraction, and tau delta=id is explicitly verified.

Step 5: checked directly from Step 3's kernel equality and Step 4's retraction. Verdict: the representative formula for s is independent of choices, B-linear, and yields all four splitting identities; this is an elementary calculation rather than a hidden node.

Step 6: checked against def-weil-module-base-change. Verdict: tensoring the displayed splitting identities with the residue field proves injectivity, exactness, and surjectivity without an unproved flatness assertion.

Step 7: checked against lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-spec-map-stalk-localization, lem-weil-pbc-localization-at-prime-of-quotient, and def-weil-module-base-change. Verdict: the identifications R=A_p, S=B_q, I=JR, S=R/I, conormal localization, and tensor comparison are stated with the correct inverse-image prime and are justified by explicit denominator calculations.

Step 8: checked against def-sc-relative-differential-sheaf, lem-weil-pbc-spec-tilde-stalk-localization, def-weil-pbc-kahler-differentials, and def-weil-module-base-change. Verdict: both stalk comparisons and both canonical arrows are identified on generators; the Leibniz calculation for f=j/t kills the j-term after tensoring with kappa and proves the first-arrow formula.

New-node audit: there are no new unsplit nodes and no Mathlib-leaf records in this split. Every supporting fact is either an existing DAG statement quoted in citations.json or an elementary calculation written in its step. No duplicate, restatement, or Mathlib-available node was created; therefore B1-B7 and the existing-node search requirement are vacuous for new nodes. I checked the existing DAG for 06AA, conormal, differential-sequence, square-zero, and localization terms and confirmed the cited nodes are the applicable ones.

Edge cases checked: the identity immersion (J=0), the empty source, Z=Spec(k) inside Spec(k[e]/(e^2)) including characteristic 2, a nonclosed generic point, and zero conormal module. Each behaves as the statement predicts. No hypothesis is added or dropped, and no source error or statement dispute was found. I changed no node or citation; this section is the complete second-reading record.
