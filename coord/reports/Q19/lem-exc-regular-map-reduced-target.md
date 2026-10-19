# Worker report: lem-exc-regular-map-reduced-target

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-regular-map-reduced-target.json`: statement, split into five proof steps; Mathlib verdict: no exact match. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every cited node in each numbered proof step.
- `report.md`: this report. Search output files and `searches.jsonl` are local supporting records; `prepare.py` is an item-specific sandbox script.

## Attachments

`IsRegularLocalRing.isDomain` belongs to `lem-sc-regular-local-domain` (already recorded as slopmaster2 closed). Read `WeilConjectures/Mathlib/RingTheory/RegularLocalRing/Defs.lean:214–218`; this proves the domain input, not the item. No new attachment claim is made. Searches for the item id and for regular-map/reducedness concepts in the project found no declaration proving this item's full statement. The master reference is not treated as a finished proof.

## WANTED

None. The shared checkout lacks the untracked Stacks directory and blueprint documents. I read the existing Stacks TeX from `/home/ubuntu/weil-newtargets/literature/stacks-project/` on the server over read-only SSH instead of downloading or changing anything. The imported blueprint chapter and unit records and the ancestor node provide the blueprint text needed here.

## Corrections and route

The statement is faithful to Stacks 07QK, `lemma-reduced-goes-up`, and is unchanged: the map is regular, both rings are Noetherian, the source is reduced. There is no statement dispute. The item had no proof and no recorded own Lean declaration. Its regular-map definition citation really does include flatness and Noetherian geometrically regular fibres; it is not merely a G-ring predicate.

The proof follows the source's use of 031R, 0339 and 033A. I expanded the implicit fact that a regular fibre is reduced using the existing regular-local-domain and prime-local-injectivity nodes. The Noetherian Serre criterion then gives the exact fibre conditions used by the source's ascent lemmas. No regular-local Cohen–Macaulay theorem is silently assumed. No new node restates the item or a clause of it, and no elementary domain-to-reduced fact has been made a node.

The fixed chapter is `sec-smooth-purity`, and the item belongs to `sk-prop-a1-kummer`. I read its chapter and unit records. This is a generic commutative-algebra support lemma below the unit, through the existing ancestor `lem-exc-punctured-curve-branches` and `lem-exc-quasi-excellent-nagata`. The latter uses exactly this assertion in its step 4 to show that the completion of a reduced local domain is reduced. The chapter and unit routes are preserved, and neither record is changed. The three nonclosed algebra tools from another unit are declared only in `split_report.tool_uses`, with their precise purpose; no maintainer-owned top-level tool field is set. The domain input is already Lean-closed; prime-local injectivity and regular-ring terminology are existing Mathlib leaves.

## Mathlib and blueprint searches

Ran the mandated `msearch.py Q19 lem-exc-regular-map-reduced-target` command with two semantic phrasings, a Loogle pattern, source grep and LeanSearch. The final node records those exact query strings and command output. LeanSearch returned HTTP Internal Server Error and is recorded unavailable. The semantic results concern reduced localizations, geometrically reduced algebras and smooth flatness. The Loogle and grep candidate `IsReduced.tensorProduct_of_flat_of_forall_fg` is at `Mathlib/RingTheory/Flat/Basic.lean:642`; I read lines 638–661. It assumes reducedness of the tensor product with every finitely generated subalgebra, not the fibre hypotheses of this item, so it does not make this item a Mathlib leaf.

Searched the entire DAG by 07QK, reducedness/flatness/fibre concepts, regularity, and Serre conditions. This found the reused 031R, 0339 and 033A nodes. Ran blueprint search for `reduced goes up regular map`, `07QK`, `reduced`, and `regular map`, and the ancestor query. The displayed blueprint hits do not restate the assertion, so `blueprint.same_as` remains the concrete empty list. The preexisting precise ancestor place and via chain are retained. No new node needs a duplicate comparison.

## Not duplicates

No new nodes. All intermediate non-elementary results already exist and are cited directly.

## Review by Q19

I read Stacks More on Algebra 07QK and its proof, regular-map Definition 07BZ, and Algebra 031R, 0339, 033A, 00NP and 00HN in the server's existing TeX. I opened the statement of every cited node, rather than using a lemma hidden in its proof. I also read `coord/delivery-errors.md` B through E in full against this split.

Step 1 uses the regular-map and geometrically-regular clauses actually present in `def-weil-pbc-g-ring`, and the regular-ring clause of `def-weil-regular-scheme`. The degree-one field extension is allowed among finite purely inseparable extensions. Taking it gives regularity of each fibre, and the definition of regular ring gives its regular prime localizations. The scalar tensor identification is explicitly written in both directions. This is an elementary unpacking of the two cited definitions, not a claim that regularity ascent itself is elementary. Fibre Noetherianity is part of the regular-map hypothesis, so no finite-type assumption has been introduced.

Step 2 uses `lem-sc-regular-local-domain` on exactly those regular local rings, and `lem-weil-pbc-prime-localizations-jointly-injective` on exactly the commutative fibre ring. The former's statement gives a domain, and the latter explicitly includes the reducedness conclusion when all prime localizations are reduced. The elementary domain-to-reduced induction is written out. Thus this step does not cite a regular-ring definition as though it were the theorem that regular rings are reduced, nor does it use an uncited sheaf-local criterion.

Step 3 uses both applications allowed by `lem-weil-pbc-serre-criterion-reduced`: the base is Noetherian and reduced by the item's hypotheses, and every fibre is Noetherian by step 1 and reduced by step 2. Its statement gives precisely the pair (R_0), (S_1), not a different Serre convention. No local or finite-dimensional base assumption is needed.

Step 4 uses the complete statements of `lem-weil-pbc-regularity-rk-goes-up` at k=0 and `lem-weil-pbc-serre-sk-goes-up` at k=1. Each requires both rings Noetherian, the original map flat, the same-index condition for every residue-field fibre, and that condition for the base. I checked each hypothesis against the item and steps 1–3. The fibre remains B tensor_A kappa(p), not B/pB. The conclusions are exactly (R_0) and (S_1) for B.

Step 5 uses the converse implication of `lem-weil-pbc-serre-criterion-reduced` for the Noetherian ring B, supplied with the pair established in step 4. No step uses the contents of a cited proof. `citations.json` copies the full verbatim statements so the second reader can assess every use independently.

For the B checklist, no new statement-only node, deficient source tag, missing notion or unsupported Mathlib leaf is introduced; the statement dependencies still are exactly the two definitions the item needs. For C, every non-elementary inference is cited, the theorem statements give what the step takes, off-unit tools are explained, and no dependency back to the item is introduced. For D, the argument is exposed through the five steps and existing theorems, with no renamed copy of the goal and no unexpressed induction. For E, I checked both Noetherian hypotheses, the fibre rings and flatness at every application. There is no source error or implicit strengthening of the conclusion.

Small cases: a field and its polynomial algebra have regular fibres and reduced target; the identity on k[x,y]/(xy) shows the base need not be a domain or regular; A -> 0 has zero fibres and a reduced zero target, so the proof does not assume nonempty spectra; if A=0 the unital target is also zero. The map k -> k[epsilon]/(epsilon^2) is flat but fails the regular-fibre hypothesis, as it must. These checks validate the uses of domain only after taking prime localizations of regular fibres, rather than at the base or target themselves. No new statements remain to test.

## Unfinished work

No mathematical part remains. The sandbox is for a fresh second reader; this worker does not push or deliver it. Dry-run validation is recorded below.

## Second reading by Q19

Independent second reader, 2026-10-16. Read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the stage-1 contract, chapter sec-smooth-purity and unit sk-prop-a1-kummer. Opened the existing Stacks TeX by read-only SSH at ubuntu@the project server:/home/ubuntu/weil-newtargets/literature/stacks-project/; the local shared checkout omits those files. No Lean or build command was run, and no shared repository file was written.

- Item statement: PASS against more-algebra.tex Tag 07QK, `lemma-reduced-goes-up`, line 10533: regular map, Noetherian target, Noetherian reduced source, and reduced target are exactly its hypotheses and conclusion. No statement dispute.
- Step 1: PASS against the full statements of def-weil-pbc-g-ring and def-weil-regular-scheme, and more-algebra.tex Tag 07BZ, `definition-regular`, line 10375; algebra.tex Tags 0381/0382, `lemma-geometrically-regular`/`definition-geometrically-regular`, lines 47104/47151, and 00OD, `definition-regular`, line 27149. The identity field extension is finite purely inseparable in every characteristic (degree one, exponent zero); the displayed mutually inverse tensor maps give the original fibre ring. Flatness and fibre Noetherianity are part of the cited definition. The elementary marker is justified by this unpacking.
- Step 2: PASS against the full statements of lem-sc-regular-local-domain and lem-weil-pbc-prime-localizations-jointly-injective, and algebra.tex Tags 00NP/00HN, `lemma-regular-domain`/`lemma-characterize-zero-local`, lines 25715/4051. Each localization is regular local, so the domain theorem applies there; induction on a positive nilpotence exponent proves it reduced. The injectivity node explicitly supplies the reducedness consequence. For a zero fibre its spectrum is empty and that same consequence remains valid; no zero ring is asserted to be a domain. Read the existing closed declaration IsRegularLocalRing.isDomain at WeilConjectures/Mathlib/RingTheory/RegularLocalRing/Defs.lean:214–218 and the Mathlib injectivity declaration at Mathlib/RingTheory/Spectrum/Maximal/Localization.lean:166–173.
- Step 3: PASS against the full statement of lem-weil-pbc-serre-criterion-reduced and algebra.tex Tag 031R, `lemma-criterion-reduced`, line 43935. Both A and every fibre meet its Noetherian hypothesis, and reducedness is given by the item and step 2 respectively; its conclusion is precisely (R_0) and (S_1). Read def-weil-pbc-serre-conditions-rk-sk to check the conventions.
- Step 4: PASS against the full statements of lem-weil-pbc-regularity-rk-goes-up and lem-weil-pbc-serre-sk-goes-up, and algebra.tex Tags 033A/0339, `lemma-Rk-goes-up`/`lemma-Sk-goes-up`, lines 46460/46403. Both applications have the same flat map A to B and the required Noetherian rings; step 3 supplies the correct base and fibre conditions at k=0 and k=1. The fibres are B tensor_A kappa(p), not B/pB. These are cited non-elementary inferences, not implicit appeals to definitions.
- Step 5: PASS against the converse direction of the full statement of lem-weil-pbc-serre-criterion-reduced and Tag 031R. B is Noetherian by the item and satisfies both conditions by step 4, exactly as needed.
- New nodes: NONE; no elementary, duplicate, Mathlib-covered, or restated-goal node has been introduced. B1–B7 require no new-node repair. Searched the DAG by 07QK, 031R, 033A, 0339, 00NP and 00HN and reread the reused statements; blueprint searches `regular reduced`, `07QK`, and `reduced` found no duplicate of this item. The ancestor query confirms lem-exc-punctured-curve-branches; lem-exc-quasi-excellent-nagata step 4 uses exactly the present conclusion for a local-domain completion. Generic off-unit tools remain explained in split_report and the first report; no maintainer-owned tool_uses field was added.

Small cases checked independently: A=B=0; a nonzero reduced A with B=0; a field mapping to its polynomial ring; the identity on the reduced singular ring k[x,y]/(xy); and k mapping to k[epsilon]/(epsilon^2), which is flat but fails the regular-fibre hypothesis. All steps allow empty spectra. The nilpotence induction starts at exponent 1, and the two ascent applications use admissible indices 0 and 1. The singular reduced identity case confirms that neither A nor B is assumed regular.

Independent Mathlib searches were run with msearch.py and appended to searches.jsonl: leanfinder `A flat ring homomorphism with reduced base and reduced residue field fibres has reduced codomain` (8 hits) and grep `IsReduced.*[Ff]iber|[Ff]iber.*[Ii]sReduced|[Rr]educed.*[Oo]f.*[Ff]lat|[Rr]educed.*[Rr]egular` (13 hits). Read Mathlib/RingTheory/Flat/Basic.lean:638–661: IsReduced.tensorProduct_of_flat_of_forall_fg asks for reduced tensor products with all finitely generated subalgebras and is not the item. The broader grep also finds AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian; read Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean:45–113. This is a scheme theorem requiring geometric reducedness. Deducing that hypothesis from the present regular-fibre definition is a mathematical step, so the declaration is not an exact match or a one-line specialization of this item. No leaf conversion is warranted. The search of project sources likewise found no finished declaration of the full item.

Citation audit: all eight step/node citation records are the full verbatim statements of their nodes in the shared DAG. Each step uses only the stated clauses, and each non-elementary inference is cited. A traversal of all 68 transitive statement/proof dependencies found no path back to the item. No vague transport or omitted parallel argument remains.

Changes and reasons: preserved the correct statement, five proof steps, sources and citations; added this independent source-by-source review and two honestly logged Mathlib searches, including the newly found scheme candidate and the reason it is not a leaf. There are zero new nodes and zero new Mathlib leaves.

Validation: required `deliver.py Q19 lem-exc-regular-map-reduced-target --no-push` completed with `OK (not pushed)` at c6c71d859b; preflight passed.
