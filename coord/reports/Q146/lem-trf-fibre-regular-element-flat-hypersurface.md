# Stage-1 repair: lem-trf-fibre-regular-element-flat-hypersurface

Group Q146, 2026-10-23. Direct delivery; self-review, with independent maintainer review still required.

## Landing return repair: current DAG rebase

This retry addresses L's latest return in `coord/returns/Q146.md`, dated 2026-10-23 11:55 UTC, for returned head `5bb0347836e`: the independent reader approved the split, but landing refused the side completion because it had not been promoted into the live queue DAG. The required first dry run on 2026-10-23 exited 0 at `17b9ca65f57`, printing `OK (not pushed)` and `preflight passed`. The delivery tool constructs the commit on its freshly fetched current DAG. I made no git call in the shared read clone. Earlier dry-run receipts and successful pushes in the sandbox are history, not evidence that this return has landed.

I continued the retained five-node split, report, citations, complete allocation of the twelve old arguments, and actual searches. I compared every field of `returned-item.json` with the current shared item: they are still identical. The delivered item differs from the current shared item only in its proof, proof dependencies, and split report. Its statement and statement dependencies are unchanged. All five new ids are still absent from the current shared DAG. The released stage-1 repair note still orders at least three comparable statement-only nodes, an assembly of at most 3000 characters, and preservation of the old argument under `keep_plan: true`; the earlier reviewed twelve-step proof therefore does not supersede that order.

For this retry I opened all six supplying statements of the assembly and every external statement dependency of the item and new nodes. The sole external assembly theorem, `lem-sbc-scheme-fibre-stalk-quotient`, explicitly identifies the fibre stalk with the quotient by the base maximal ideal and sends each class to its stalk image. Together with the chart's stalk identifications, it supplies precisely the element-compatible quotient used in Step 3. The six entries of `citations.json` are still verbatim substrings of the current supplying statements. The other five supplying statements are the retained new nodes, whose mathematical text has not changed. No current cited statement requires a change to the assembly.

I checked the hypotheses in order: Step 1 supplies the flat finitely presented chart and exact representative of h; Step 2 supplies both Noetherian model rings and e(1 tensor a0)=a; Step 3 applies faithful-flat descent to the original regular fibre element, with a0 in q0 by contraction; Step 4 applies the Noetherian criterion only after obtaining that regular singleton and chooses g0 outside q0; Step 5 uses the resulting flat H0 and g outside q to return to the actual composite D to S. Each non-elementary assertion is in the cited statement. Every step is shorter than 2000 characters and the complete assembly remains 1934 characters. The five nodes remain statement-only, with empty proofs and proof-dependency lists.

I re-read the complete statement and proof of Tag 056Y, `lemma-slice-given-element`, and the newest blueprint under `literature/blueprint/latest/` (the 2026-10-23-1620 snapshot, `7284bb09daf97437d544c51882b325f9c52cd345`), including the chapter, unit, and ancestor `lem-trf-local-term-locality`. This local algebra repair preserves the recorded ancestry and route; it introduces no replacement of the trace or purity route. The five source allocations below still cover every old argument. The effective Cartier conclusion omitted by the original item remains outside its unchanged statement.

The boundary checks were repeated: an arbitrary zero or unit germ is allowed in the chart lemma, the model permits the zero algebra, and a designated prime forces the fibre-local ring nonzero in the regularity lemmas. Thus a zero regular element and a unit in the designated prime cannot supply spurious cases. Taking identical model and original rings gives the identity fibre comparison; g0=1 returns the whole affine chart. The current search log and its recorded hits were read and retained: no statement or search question changed, and no new search was asserted. This repair updates the report and split-report date and current-return record, then validates the updated packet in a fresh dry run before pushing.


### Current dependency snapshot

On 2026-10-23T12:26:53+00:00 I re-read the following current external supplying statements and definitions. SHA-256 below hashes the exact statement text, so a later reader can identify any intervening mathematical change. All still supply the hypotheses and conclusions described in the signed review above. The current shared item remains field-for-field identical to the retained returned baseline.

- `def-pc-scheme`: `55d53a3e530fc84c43a0044b77ada1324b7524d56d11884b2cfd670d09106830`.
- `def-pc-scheme-fibre`: `ac96aa912bbc2bc2e4e86223e849009aa4adf00a0ac05dc7c46a14bd8389959d`.
- `def-sbc-locally-finite-presentation`: `400cd6ef72ebfa7d79cabccea9fe4f7450fa8b40d06a2b09e1ef5eedeec8c6f7`.
- `def-weil-closed-immersion`: `216d86694ce9fe6fd87bf65dbf80c3bf4b45f95edbdf59729ab185c91587ef6c`.
- `def-weil-flat-morphism`: `650c52d56f263fc12deea8ae792628509100f4554244ac2c23150d264ea0a681`.
- `def-weil-pbc-faithfully-flat-ring-map`: `c9558d0fab074174aa61a510131a81e0a3a3062eb3b4605ccfd04b1f4b9b8277`.
- `def-weil-pbc-finitely-presented-algebra`: `198f3b55ceeeeb5fc5136752e12aedea52e4f8b3ea66e65598c45650508da264`.
- `def-weil-pbc-flat-ring-map`: `b622d6830fa3354f4fc7310886fe1c3af1acceb18d6e6da3d07b9949ed4cd0e2`.
- `def-weil-pbc-localization-at-prime`: `b34cb1e6c16531053348b02bebe428a4852ac3b602825bd5ce68c4c2182dc146`.
- `def-weil-pbc-module-tensor-product`: `79f34421ad3a00fa39713e6c4f73f08f4c0875f3495ae541e4488cdb93ab8fda`.
- `def-weil-pbc-noetherian-ring`: `89c441e59f4e749bcd421093e019e57ccfffe815a35da248acba958ca9182463`.
- `def-weil-pbc-regular-sequence`: `091ff9ad67386780106ac4cdb4a1d444b4427d51c463f7c1f708ffe03b04382b`.
- `def-weil-ring-localization-away`: `a73cefbf3ca2f718ec1dcf78b1f7103018794b5e2020b451ecb754f686b66246`.
- `lem-sbc-scheme-fibre-stalk-quotient`: `530035bb42d116969570f696b5aa60803ff32952e1e50f9090724cc58b6473dd`.
- `lem-weil-pbc-affine-open-section-vanishing-prime`: `188ba66d9b4fc4ab142e560ea7fdef474ea75b46f33062ddad301f5ddef37dba`.
- `lem-weil-pbc-affine-open-stalk-localization`: `56f9be91329387c6bdbe1dff632ef4e00a9abb21e3bf0f1331b083675a3874d3`.
- `lem-weil-pbc-faithfully-flat-universally-injective`: `c899636f2613a35de5055d1449a1328967141a1e664beab41510fe3b6a0eb0e5`.
- `lem-weil-pbc-fibre-product-affine-spectra`: `54ddf419c20ac9a99773095ac1822c86bad1913ca32223712c65bab2562429f8`.
- `lem-weil-pbc-field-extension-base-change-faithfully-flat`: `755b2bec32f9588ac5ce70f97928459a957d0caaa328355bd1030dc9d81faf91`.
- `lem-weil-pbc-finite-presentation-base-change-composition`: `abb3d715588028cd5ecab837ab749d3c6b59fe49d4afadd3bf73873e13feedc7`.
- `lem-weil-pbc-finite-type-algebra-noetherian`: `5519a621fad67ad59fdb896ef8bf44d6f71426129a05a7d3a02e0458a936cf3a`.
- `lem-weil-pbc-flat-finite-presentation-model`: `989f80a9646262a3d609648a01ef31ed0c86e18a548c07ea304315912913b1cf`.
- `lem-weil-pbc-flat-local-hom-faithfully-flat`: `50ba66d0eddc9628f8471dc54b579bfd717f8ae9ca6fe82a16051be8dbb41005`.
- `lem-weil-pbc-flat-local-ring-maps`: `c4db5e0b5cb130557a8ddfa5f7bc28a19b247c68d937b4668c1570b1ab54892c`.
- `lem-weil-pbc-flat-module-base-change`: `8580c3c59fe47d6780f89ce2cbfe2b16734b3aff31f75baafb2055220f3a8eeb`.
- `lem-weil-pbc-flat-morphism-affine-criterion`: `b53f660d0fb7f18e6935531a17a01c2a7681eb757889193ea71db76aea69d163`.
- `lem-weil-pbc-flat-over-localization`: `ddd3e871de111a385caecefa7c6b152ab9045ee6d155fd6ecfc11c3cb27ef58f`.
- `lem-weil-pbc-grothendieck-regular-sequence-flat`: `4451268a01fe8f217c7e763f7b789570f3d02ac2053da790e2c11a4b52185a4b`.
- `lem-weil-pbc-openness-of-flatness`: `b1e061cc5e55b194a2d25f3b9d528666ed61d6d27f62a7ca4a438c6447089ac5`.
- `lem-weil-pbc-spec-localization-away-basic-open`: `0a09402a7a70284eba822b9a7e288f7ea4868b4449a7aa94e5141f2e3ec25d19`.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-regular-element-flat-hypersurface.json`: same statement and statement dependencies; five assembly steps, 1934 characters in total.
- `dag/nodes/sec-trace-formula/lem-trf-flat-affine-chart-prescribed-germ.json`: statement, status `unsplit`; no exact Mathlib match or one-line specialization found. No proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-flat-noetherian-model-prescribed-section.json`: statement, status `unsplit`; no exact Mathlib match or one-line specialization found. No proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-model-fibre-regularity-descent.json`: statement, status `unsplit`; no exact Mathlib match or one-line specialization found. No proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-noetherian-fibre-regular-quotient-neighbourhood.json`: statement, status `unsplit`; no exact Mathlib match or one-line specialization found. No proof steps or proof dependencies.
- `dag/nodes/sec-trace-formula/lem-trf-model-principal-quotient-return.json`: statement, status `unsplit`; no exact Mathlib match or one-line specialization found. No proof steps or proof dependencies.
- `citations.json`: six exact full-statement quotations for the six step/node citations.
- `report.md`: this signed repair, full retained old argument, and retained historical report.

Five new nodes, zero new Mathlib leaves. Sandbox-only auxiliary files include the source baseline `returned-item.json`, actual `searches.jsonl`, complete printed search results `search-results.txt`, the search plan and the construction scripts. They are not additional DAG nodes. No Lean was written; no compiler, Lake, build, local DAG gate, shared-repository git command, or launcher edit was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and the fibre-regular, flat-quotient, prescribed-germ and model-section notions. I also read the existing `lean/Sheaf/AlgebraicGeometry/Morphisms/FibreRegularElementFlatHypersurface.lean`; the exact item declaration ends with `sorry`, so it is not an attachment. The project flat-model and regular-sequence theorems are inputs, not exact declarations of the five new statements. The old searches and their results remain unchanged in the item's JSON. The Q112 report's explanation concerning the global-fibre Cartier criterion remains applicable.

## WANTED

None. All source material used is in the read clone.

## Return and repair

The return requests spreading the 9073-character proof into at least three separate, comparable-sized statement-only arguments, with assembly at most 3000 characters, while keeping the item statement. The sandbox initially contained only dispatcher `.brief*` markers, no previous node, report or search log. I copied the current repository item as the retained returned baseline and read its previous Q112 report. I did not interpret the missing sandbox packet as invalidating the reviewed old mathematical argument. Its twelve steps are reproduced verbatim below and assigned without omissions to five independent nodes. The group sizes measured in old argument characters are 1736, 1683, 2000, 1579 and 2075 respectively. No node carries the whole argument; their common source is the respective paragraph of Tag 056Y, `lemma-slice-given-element`.

The item statement, specified germ, pointwise-flat hypothesis, arbitrary original base, and requested flat and locally finitely presented composite are unchanged. There is no statement dispute. The extra effective Cartier conclusion of 056Y was already excluded by the item's source and remains excluded. The old argument never needed the last annihilator calculation for that extra assertion. Chapter and unit records, the ancestry and current blueprint route are unchanged. Existing maintainer metadata is retained, not re-certified by this repair.

## Review by Q146

For the current landing return (`5bb0347836e`, 2026-10-23 11:55 UTC), I revalidated the retained delivery rather than treating its older successful pushes as completion. The first required dry run fetched the current server DAG and passed at `17b9ca65f57`. A field-by-field comparison of `returned-item.json` with the current shared item found no differences; the sandbox item changes only `proof`, `proof_deps`, and `split_report`. None of the five delivered new ids is present in the current shared DAG. I opened all current assembly inputs, the item and new-node definition dependencies, and the old twelve-step inputs retained below. The fibre-stalk statement still gives the element-compatible quotient isomorphism, the regular-sequence definition still requires a nonzero quotient, and the local-flatness theorem still assumes Noetherian local rings. The assembly verifies these hypotheses before each application, so no mathematical statement or dependency required amendment. All six citation quotations remain verbatim. I retained the existing searches after reading their actual results; neither the statements nor the search questions changed. The concrete repair is a delivery rebuilt on the current DAG with this corrected return record, while preserving the approved five-node split and every old argument.

I read the complete statement and proof of Stacks Tag 056Y, label `lemma-slice-given-element`, in `literature/stacks-project/more-morphisms.tex:6166` onward. I read the project's stage-1 contract, SETUP's three levels, GOAL, the chapter/unit records, and delivery-errors B–E in full. The new statements follow the first paragraph, the two portions of the approximation paragraph, the final Noetherian algebra paragraph, and the return from that model respectively. They do not change the fixed unit route or use SGA. The source's explicit flat Noetherian model, faithful-flat fibre-local comparison, and Noetherian local quotient argument are retained rather than replaced by a claim of arbitrary-base local flatness.

For new node 1 I checked that its input is only local finite presentation and flatness at the point, and that it promises the chosen germ exactly, rather than up to a unit. Its conclusion supplies an actual affine chart with a flat finitely presented coordinate map, plus stalk maps and prime membership. This is old steps 1–2: denominator shrinking followed by openness for the module B. The finite-presentation formula after each localization and passage from local to full affine flatness remain in the retained argument. It does not assume flatness of f on all of X. For node 2, the source's flat approximation alone does not descend the chosen element; old steps 3–5 retain the finite tensor sum, coefficient enlargement of the image of P, both reassociation maps, base-change flatness and finite presentation, and the two Noetherian arguments. The new statement includes both Noetherian rings and the equality e(1 tensor a0)=a, with no Noetherian assumption on the original base.

For new node 3 I checked every contraction and coefficient field: p0 is the common contraction, k0 maps into k by a field embedding, E0 tensor k identifies with the original fibre ring, and the point primes are localized before asserting faithful flatness. Its conclusion includes the two closed-fibre quotient identifications and their compatibility with B0. Old steps 6–7 retain their explicit tensor maps, field-extension flatness, localized local-map flatness, faithful flatness, universal injection, annihilator argument and the proper-ideal argument for a nonzero singleton quotient. Merely preserving regular elements under a flat map would be the wrong direction. No flatness or injectivity of the original change of base A0 to A is assumed. For new node 4, the hypotheses explicitly include both Noetherian rings, finite presentation, flatness, membership a0 in q0, and the regular singleton in the localized closed fibre. Old steps 8–9 apply the local Grothendieck theorem only after these checks, convert the local quotient to an A0-flat module, use its one-generator one-relation finite presentation in openness, and recover flatness of the whole localized quotient via its actual stalks. This intermediate algebra result does not give the item over a non-Noetherian base.

For new node 5, the input already supplies a model quotient flat on a prescribed basic open. Old steps 10–12 retain the explicit tensor-localization-quotient map and its inverse, base change of flatness, verification of the actual composite's stalk maps, finite polynomial presentation with inverse variable and extra relation, closed-immersion description, unchanged germ and containment of the point. Its hypothesis g not in q is necessary for the affine neighbourhood, while a in q is necessary for containment of x. This statement asserts neither a fibre-regularity criterion nor existence of the model flat open; the other four arguments supply those inputs. It allows arbitrary A0 to A, and does not assert that a closed immersion is itself flat.

I opened the statements of every input cited by the twelve old steps; the retained dependency lists below identify them individually. In particular the model node gives a flat integer model but not a section, the openness node concerns finitely presented modules over finitely presented algebras, the fibre-stalk node preserves the image of each element, the local-map node includes Noetherian localization, the regular-sequence flatness node gives flat prefix quotients, and the closed-immersion definition includes its affine-quotient criterion. Thus these supply the old arguments attributed to them. They are future proof inputs recorded in this report, not extra proof dependencies or hidden proof steps in the new unsplit files.

I checked all five assembly steps against the actual new statements (C3/C4). Step 1 takes node 1's exact germ, flat finite presentation, stalk identifications and a in q. Step 2 uses node 2 for the compatible element-model and both Noetherian rings. Step 3 uses the existing `lem-sbc-scheme-fibre-stalk-quotient` for the original fibre stalk and preservation of h, then node 3 for the compatible closed-fibre identification and regular singleton. The original affine stalk identifications are already supplied by node 1 in Step 1. Step 4 checks every Noetherian quotient-neighbourhood hypothesis from Steps 2–3, including a0 in q0 by contraction, then takes node 4's g0 and flat H0. Avoidance of g follows directly from contraction. Step 5 applies node 5 with exactly the affine charts, finite presentation, tensor isomorphism, a in q, g not in q, and flat H0 already obtained. It returns every requested clause for the actual composite to S and retains the germ. Renaming B_g is elementary. Each step cites its full supplying statement in `citations.json`; none of the assembly steps is marked elementary or longer than 2000 characters. Their total is 1934.

For B1–B9, every new file is self-contained with only a statement, empty proof and proof-dependency lists, source tag plus label and exact paragraph, correct chapter/unit, complete blueprint ancestry through the item, same_as=[], and inline explanations or existing definition dependencies for every specialized notion. I searched the whole DAG by 056Y/lemma-slice-given-element and by germs, model-section, nonzerodivisor, flat quotient and regularity-descent concepts. Whole-blueprint searches included `flat germ`, `flat model section`, `fibre regular`, `flat quotient`, `principal quotient`, and `nonzerodivisor`; their hits concern other notions, not these intermediate statements. The same-tag nodes and closest algebraic candidates are distinguished below. I searched Mathlib for every new statement with six actual calls: two differently phrased LeanFinder queries, Loogle, LeanSearch, and two source regexes. Their query text is copied exactly from the real log, not invented retrospectively. LeanSearch was rate-limited for nodes 4 and 5 and is recorded unavailable. Successful semantic, Loogle and source searches still ran for both. I read the hits, including `Algebra.Smooth.exists_subalgebra_finiteType` (requires smoothness), `RingTheory.Sequence.IsRegular.of_faithfullyFlat` (ascends a regular sequence after a supplied flat map), affine flatness criteria, and `Algebra.TensorProduct.tensorQuotientEquiv` (quotient comparison only). They do not state the full respective new results or specialize to them in one line; their components are not new duplicate nodes.

For E1–E5 I checked boundary cases explicitly. Node 1 works for a zero or unit germ because it has no regularity hypothesis; only its final conditional membership uses h in the maximal ideal. Node 2 permits the zero algebra and an empty tensor sum: a0=0 descends a=0; flatness of the zero module and finite presentation of the zero quotient are consistent. In nodes 3–4 the point prime guarantees the localized fibre ring is nonzero; a zero element cannot be regular there, and a unit cannot belong to the designated prime. Thus the maximal-ideal/nonzero-quotient clauses are justified without a positive-dimensional hypothesis. With A=A0 and B=B0, node 3 gives the identity fibre-local comparison, as it should. With A=k[t_i: i>=1], B=A[T], and the point prime generated by T and the t_i, the item for h=T still descends to a finite coefficient model: it does not assume the original infinitely generated base Noetherian. In node 5, g0=1 simply returns the full affine chart; g=0 cannot avoid q. If a becomes a unit the containment hypothesis fails; the statement does not incorrectly force a point into an empty quotient. Neither the base-change map nor residue-field extension is required to be finite or algebraic. All tensor comparisons in the retained proof display actual generator maps and inverses, avoiding the missing-comparison fault E5.

The original long-proof repair is preserved substantively by the five new statements and the following complete argument allocation. The current landing return requires rebuilding that approved packet on the current DAG and rechecking supplying statements; those checks are recorded above. New nodes remain open for independent workers.

## Not duplicates

lem-trf-flat-affine-chart-prescribed-germ vs lem-trf-fibre-regular-element-flat-hypersurface: it constructs a flat affine representative of an arbitrary germ without any fibre-regularity assumption or hypersurface conclusion.

lem-trf-flat-affine-chart-prescribed-germ vs lem-trf-cm-closed-point-flat-quasifinite-slice: it constructs a flat affine representative of an arbitrary germ without any fibre-regularity assumption or hypersurface conclusion; the existing node constructs a locally quasi-finite slice from a Cohen–Macaulay closed fibre point, an induction using 056Y, not this intermediate result.

lem-trf-flat-affine-chart-prescribed-germ vs lem-trf-smooth-separable-hypersurface-slice: it constructs a flat affine representative of an arbitrary germ without any fibre-regularity assumption or hypersurface conclusion; the existing node is the smooth separable dimension-cutting slice, not the flat Noetherian approximation argument here.

lem-trf-flat-noetherian-model-prescribed-section vs lem-trf-fibre-regular-element-flat-hypersurface: it constructs a Noetherian tensor model including a prescribed section, with no scheme point, regularity or flat-quotient assertion.

lem-trf-flat-noetherian-model-prescribed-section vs lem-trf-cm-closed-point-flat-quasifinite-slice: it constructs a Noetherian tensor model including a prescribed section, with no scheme point, regularity or flat-quotient assertion; the existing node constructs a locally quasi-finite slice from a Cohen–Macaulay closed fibre point, an induction using 056Y, not this intermediate result.

lem-trf-flat-noetherian-model-prescribed-section vs lem-trf-smooth-separable-hypersurface-slice: it constructs a Noetherian tensor model including a prescribed section, with no scheme point, regularity or flat-quotient assertion; the existing node is the smooth separable dimension-cutting slice, not the flat Noetherian approximation argument here.

lem-trf-model-fibre-regularity-descent vs lem-trf-fibre-regular-element-flat-hypersurface: it compares two fibre local rings under arbitrary base change and descends a regular singleton, without producing any flat hypersurface neighbourhood.

lem-trf-model-fibre-regularity-descent vs lem-trf-cm-closed-point-flat-quasifinite-slice: it compares two fibre local rings under arbitrary base change and descends a regular singleton, without producing any flat hypersurface neighbourhood; the existing node constructs a locally quasi-finite slice from a Cohen–Macaulay closed fibre point, an induction using 056Y, not this intermediate result.

lem-trf-model-fibre-regularity-descent vs lem-trf-smooth-separable-hypersurface-slice: it compares two fibre local rings under arbitrary base change and descends a regular singleton, without producing any flat hypersurface neighbourhood; the existing node is the smooth separable dimension-cutting slice, not the flat Noetherian approximation argument here.

lem-trf-noetherian-fibre-regular-quotient-neighbourhood vs lem-trf-fibre-regular-element-flat-hypersurface: it spreads a flat quotient only for a given Noetherian algebra and a given regular closed-fibre singleton; it does not descend to a model or return to an arbitrary base scheme.

lem-trf-noetherian-fibre-regular-quotient-neighbourhood vs lem-trf-cm-closed-point-flat-quasifinite-slice: it spreads a flat quotient only for a given Noetherian algebra and a given regular closed-fibre singleton; it does not descend to a model or return to an arbitrary base scheme; the existing node constructs a locally quasi-finite slice from a Cohen–Macaulay closed fibre point, an induction using 056Y, not this intermediate result.

lem-trf-noetherian-fibre-regular-quotient-neighbourhood vs lem-trf-smooth-separable-hypersurface-slice: it spreads a flat quotient only for a given Noetherian algebra and a given regular closed-fibre singleton; it does not descend to a model or return to an arbitrary base scheme; the existing node is the smooth separable dimension-cutting slice, not the flat Noetherian approximation argument here.

lem-trf-model-principal-quotient-return vs lem-trf-fibre-regular-element-flat-hypersurface: it returns an already-flat model quotient to a specified affine chart; its hypothesis supplies the flat quotient, rather than deducing one from fibre regularity.

lem-trf-model-principal-quotient-return vs lem-trf-cm-closed-point-flat-quasifinite-slice: it returns an already-flat model quotient to a specified affine chart; its hypothesis supplies the flat quotient, rather than deducing one from fibre regularity; the existing node constructs a locally quasi-finite slice from a Cohen–Macaulay closed fibre point, an induction using 056Y, not this intermediate result.

lem-trf-model-principal-quotient-return vs lem-trf-smooth-separable-hypersurface-slice: it returns an already-flat model quotient to a specified affine chart; its hypothesis supplies the flat quotient, rather than deducing one from fibre regularity; the existing node is the smooth separable dimension-cutting slice, not the flat Noetherian approximation argument here.

Additional close candidates: `lem-trf-flat-noetherian-model-prescribed-section` vs `lem-weil-pbc-flat-finite-presentation-model`: the latter gives P,Q and the algebra comparison but no chosen element, no finite coefficient subring of A containing its coefficients, or stated Noetherian pair; old steps 4–5 are the additional argument. `lem-trf-noetherian-fibre-regular-quotient-neighbourhood` vs `lem-weil-pbc-grothendieck-regular-sequence-flat`: the latter concerns a local Noetherian map and flat prefix quotients, not a basic neighbourhood in the unlocalized algebra (old step 9). `lem-trf-noetherian-fibre-regular-quotient-neighbourhood` vs `lem-pc-algebra-fibre-cartier-local`: that existing result assumes locally regular equations at every prime of the entire fibre; the new result assumes regularity only in one specified fibre local ring. `lem-trf-model-fibre-regularity-descent` vs `lem-weil-pbc-flat-local-hom-faithfully-flat`: the latter assumes a flat local map already; it does not identify the fibre rings, construct their flat local map, or compare the specified elements. None of the five new nodes restates an existing blueprint node or an item clause under the item's unchanged hypotheses.


### Current same-tag nodes rechecked for this landing return

lem-trf-flat-affine-chart-prescribed-germ vs lem-sfb-scheme-fibre-regular-slice-flat: the new node constructs a flat affine representative of any germ, with no fibre-regularity or quotient conclusion; the existing node states the arbitrary-scheme regular-sequence slice conclusion; it does not supply this intermediate construction or its ring comparisons.

lem-trf-flat-affine-chart-prescribed-germ vs lem-sfb-space-fibre-regular-slice-flat: the new node constructs a flat affine representative of any germ, with no fibre-regularity or quotient conclusion; the existing node concerns global equations on flat algebraic spaces and an etale fibre stalk; it does not supply this affine/model intermediate construction.

lem-trf-flat-affine-chart-prescribed-germ vs lem-trf-prescribed-germ-smooth-cartier-cut: the new node constructs a flat affine representative of any germ, with no fibre-regularity or quotient conclusion; the existing node assumes smoothness and nonzero relative differential and concludes a smooth Cartier slice; those additional hypotheses are absent here.

lem-trf-flat-noetherian-model-prescribed-section vs lem-sfb-scheme-fibre-regular-slice-flat: the new node constructs a Noetherian tensor model with a prescribed element, with no scheme point or regular-slice conclusion; the existing node states the arbitrary-scheme regular-sequence slice conclusion; it does not supply this intermediate construction or its ring comparisons.

lem-trf-flat-noetherian-model-prescribed-section vs lem-sfb-space-fibre-regular-slice-flat: the new node constructs a Noetherian tensor model with a prescribed element, with no scheme point or regular-slice conclusion; the existing node concerns global equations on flat algebraic spaces and an etale fibre stalk; it does not supply this affine/model intermediate construction.

lem-trf-flat-noetherian-model-prescribed-section vs lem-trf-prescribed-germ-smooth-cartier-cut: the new node constructs a Noetherian tensor model with a prescribed element, with no scheme point or regular-slice conclusion; the existing node assumes smoothness and nonzero relative differential and concludes a smooth Cartier slice; those additional hypotheses are absent here.

lem-trf-model-fibre-regularity-descent vs lem-sfb-scheme-fibre-regular-slice-flat: the new node constructs the faithfully flat comparison of two model fibre local rings and descends regularity, with no slice neighbourhood conclusion; the existing node states the arbitrary-scheme regular-sequence slice conclusion; it does not supply this intermediate construction or its ring comparisons.

lem-trf-model-fibre-regularity-descent vs lem-sfb-space-fibre-regular-slice-flat: the new node constructs the faithfully flat comparison of two model fibre local rings and descends regularity, with no slice neighbourhood conclusion; the existing node concerns global equations on flat algebraic spaces and an etale fibre stalk; it does not supply this affine/model intermediate construction.

lem-trf-model-fibre-regularity-descent vs lem-trf-prescribed-germ-smooth-cartier-cut: the new node constructs the faithfully flat comparison of two model fibre local rings and descends regularity, with no slice neighbourhood conclusion; the existing node assumes smoothness and nonzero relative differential and concludes a smooth Cartier slice; those additional hypotheses are absent here.

lem-trf-model-principal-quotient-return vs lem-sfb-scheme-fibre-regular-slice-flat: the new node starts with an already flat localized model quotient and returns it through a specified tensor isomorphism, with no regular-slice criterion; the existing node states the arbitrary-scheme regular-sequence slice conclusion; it does not supply this intermediate construction or its ring comparisons.

lem-trf-model-principal-quotient-return vs lem-sfb-space-fibre-regular-slice-flat: the new node starts with an already flat localized model quotient and returns it through a specified tensor isomorphism, with no regular-slice criterion; the existing node concerns global equations on flat algebraic spaces and an etale fibre stalk; it does not supply this affine/model intermediate construction.

lem-trf-model-principal-quotient-return vs lem-trf-prescribed-germ-smooth-cartier-cut: the new node starts with an already flat localized model quotient and returns it through a specified tensor isomorphism, with no regular-slice criterion; the existing node assumes smoothness and nonzero relative differential and concludes a smooth Cartier slice; those additional hypotheses are absent here.

lem-trf-noetherian-fibre-regular-quotient-neighbourhood vs lem-sfb-scheme-fibre-regular-slice-flat: the new node starts with a Noetherian algebra and proves ring flatness of a quotient on a principal open, including the localized quotient conclusion, rather than starting with an arbitrary scheme morphism; the existing node states the arbitrary-scheme regular-sequence slice conclusion; it does not supply this intermediate construction or its ring comparisons.

lem-trf-noetherian-fibre-regular-quotient-neighbourhood vs lem-sfb-space-fibre-regular-slice-flat: the new node starts with a Noetherian algebra and proves ring flatness of a quotient on a principal open, including the localized quotient conclusion, rather than starting with an arbitrary scheme morphism; the existing node concerns global equations on flat algebraic spaces and an etale fibre stalk; it does not supply this affine/model intermediate construction.

lem-trf-noetherian-fibre-regular-quotient-neighbourhood vs lem-trf-prescribed-germ-smooth-cartier-cut: the new node starts with a Noetherian algebra and proves ring flatness of a quotient on a principal open, including the localized quotient conclusion, rather than starting with an arbitrary scheme morphism; the existing node assumes smoothness and nonzero relative differential and concludes a smooth Cartier slice; those additional hypotheses are absent here.

The scheme regular-sequence slicing node generalizes the item's conclusion, but this released keep-plan repair specifically retains the existing model argument and spreads its work; it does not replace that argument by the general slice theorem. None of these newer same-tag nodes duplicates one of the five intermediate statements.

## Retained argument and exact allocation

These are the complete twelve proof steps of the returned repository head, verbatim, including each old use list and source. They are preserved as worker guidance in this report, not as proofs inside the statement-only nodes. Each old step has exactly one new-node owner. The combined owner workloads are comparable; no old argument disappears under the shorter assembly.

### lem-trf-flat-affine-chart-prescribed-germ: old steps 1, 2

Old step 1:

Choose affine neighbourhoods $V=\operatorname{Spec}A$ of $s$ and $U_1=\operatorname{Spec}B_1$ of $x$, with $f(U_1)\subseteq V$ and $B_1$ finitely presented over $A$, by the definition of local finite presentation. Write $\mathfrak q_1$ for $x$ and $\mathfrak p$ for $s$. The affine-stalk localization statement writes the specified germ as $h=b/t$ in $(B_1)_{\mathfrak q_1}$, with $t\notin\mathfrak q_1$. Replace $U_1$ by its affine principal open $D(t)=\operatorname{Spec}(B_1)_t$ and let $a=b/t$ be its section. It has germ exactly $h$. Finite presentation is preserved here directly: if $B_1=A[T_1,\ldots,T_n]/(F_1,\ldots,F_m)$ and $t$ is represented by $T$, then $(B_1)_t=A[T_1,\ldots,T_n,u]/(F_1,\ldots,F_m,uT-1)$. Rename this ring $B$, and the point prime $\mathfrak q$.

Inputs: `def-sbc-locally-finite-presentation`, `lem-weil-pbc-affine-open-stalk-localization`, `lem-weil-pbc-affine-open-section-vanishing-prime`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: first paragraph, affine restriction and extension of the germ to a section; explicit principal-localization presentation.

Old step 2:

The stalk maps identify flatness at $x$ with flatness of $A_{\mathfrak p}\to B_{\mathfrak q}$. By flatness over a localization, $B_{\mathfrak q}$ is also flat over $A$. Apply openness of flatness to the finitely presented $A$-algebra $B$ and the free rank-one $B$-module $M=B$. Choose a basic open $D(g)$ containing $\mathfrak q$ in that open locus. For every $\mathfrak r\in D(g)$, $B_{\mathfrak r}$ is flat over $A$, hence over $A_{\mathfrak r\cap A}$ by flatness over a localization. The affine-stalk identifications and the definition of flatness therefore show that $\operatorname{Spec}B_g\to\operatorname{Spec}A$ is flat. Its full affine chart in the affine criterion gives that $B_g$ is flat as an $A$-module. Replace $B$ by $B_g$ and $a$ by its restriction, retaining its germ and finite presentation by the same extra-variable presentation as in Step 1. Thus from now on $A\to B$ is flat and finitely presented, not merely flat at the specified point.

Inputs: `def-weil-flat-morphism`, `lem-weil-pbc-affine-open-stalk-localization`, `lem-weil-pbc-flat-over-localization`, `lem-weil-pbc-openness-of-flatness`, `lem-weil-pbc-spec-localization-away-basic-open`, `lem-weil-pbc-affine-open-section-vanishing-prime`, `lem-weil-pbc-flat-morphism-affine-criterion`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: first paragraph, openness of flatness; algebraic form is Tag 00RC and localization is Tag 00HT (2).

### lem-trf-flat-noetherian-model-prescribed-section: old steps 3, 4, 5

Old step 3:

Apply the flat finite-presentation model theorem to $A\to B$. It supplies a finitely presented $\mathbf Z$-algebra $P$, a flat finitely presented $P$-algebra $Q$, a map $P\to A$, and an $A$-algebra isomorphism $A\otimes_P Q\cong B$. Use this isomorphism to regard the chosen section $a$ as an element of this tensor product. This is the flat Noetherian-approximation input of 056Y, in its algebraic version (02JO), before ensuring that the one chosen section descends.

Inputs: `lem-weil-pbc-flat-finite-presentation-model`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: second paragraph, Algebra Tag 02JO (1), with the module equal to the algebra.

Old step 4:

Write $a=\sum_{j=1}^N a_j\otimes q_j$ with $a_j\in A$ and $q_j\in Q$. Let $A_0\subseteq A$ be the $\mathbf Z$-subalgebra generated by the images of a finite generating set of $P$ together with the finitely many $a_j$. The map $P\to A$ factors through $A_0$. Put $B_0=A_0\otimes_P Q$ and $a_0=\sum_j a_j\otimes q_j\in B_0$. Flat base change and finite-presentation base change give that $A_0\to B_0$ is flat and finitely presented. The maps $a'\otimes(a_0'\otimes q')\mapsto a'a_0'\otimes q'$ and $a'\otimes q'\mapsto a'\otimes(1\otimes q')$ are inverse $A$-algebra isomorphisms $A\otimes_{A_0}B_0\cong A\otimes_P Q=B$, and send $1\otimes a_0$ to $a$. Thus the section as well as the morphism has descended; no finite generation assumption on $A$ was used.

Inputs: `lem-weil-pbc-flat-module-base-change`, `lem-weil-pbc-finite-presentation-base-change-composition`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: second paragraph, descending the section after the flat model; the finite coefficient enlargement is written out.

Old step 5:

Every ideal of $\mathbf Z$ is generated by its least positive element, or is zero, so $\mathbf Z$ is Noetherian. The ring $A_0$ is of finite type over $\mathbf Z$ by its displayed finite generating set. The finite-type-algebra Noetherian theorem gives that $A_0$ is Noetherian. Since $B_0$ is finitely presented, hence of finite type, over $A_0$, the same theorem gives that $B_0$ is Noetherian. These are assertions about the model only, not about $A$ or $B$.

Inputs: `lem-weil-pbc-finite-type-algebra-noetherian`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: second paragraph, the affine Noetherian base and model; Algebra Tag 00FN.

### lem-trf-model-fibre-regularity-descent: old steps 6, 7

Old step 6:

Let $\mathfrak q_0=\mathfrak q\cap B_0$, $\mathfrak p_0=\mathfrak p\cap A_0$, $k_0=\kappa(\mathfrak p_0)$ and $k=\kappa(\mathfrak p)$. The map $A_0\to A$ induces a field embedding $k_0\to k$: first localize at the two primes, then pass to their residue fields. Put $E_0=B_0\otimes_{A_0}k_0$. The definition of the fibre and the affine fibre-product theorem identify the model fibre with $\operatorname{Spec}E_0$. They identify the original fibre chart with $\operatorname{Spec}E$, where $E=B\otimes_A k\cong E_0\otimes_{k_0}k$; the isomorphism sends $(b_0\otimes c)\otimes d$ to $b_0\otimes cd$ in $B_0\otimes_{A_0}k$, with inverse $b_0\otimes d\mapsto(b_0\otimes1)\otimes d$. Let $\mathfrak r$ be the prime of $E$ at $x$ and $\mathfrak r_0$ its contraction to $E_0$, the fibre point at $\mathfrak q_0$. The affine-stalk theorem gives $C=E_{\mathfrak r}=\mathcal O_{X_s,x}$ and $C_0=(E_0)_{\mathfrak r_0}$. The fibre-stalk quotient theorem also gives $C_0\cong (B_0)_{\mathfrak q_0}/\mathfrak p_0(B_0)_{\mathfrak q_0}$, preserving the images of $a_0$.

Inputs: `def-pc-scheme-fibre`, `lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-affine-open-stalk-localization`, `lem-sbc-scheme-fibre-stalk-quotient`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: second paragraph, the displayed cartesian model and the two local rings on its fibres; Schemes Tags 01I4, 01JQ and 0HA1.

Old step 7:

The field-extension base-change theorem makes $E_0\to E_0\otimes_{k_0}k=E$ faithfully flat, hence flat. Localizing at $\mathfrak r$ and its contraction $\mathfrak r_0$ gives a flat local homomorphism $C_0\to C$ by the flat-local-ring-maps theorem. A flat local homomorphism is faithfully flat. The universal-injectivity theorem, applied with module $N=C_0$ and $C_0\otimes_{C_0}C\cong C$, therefore makes this map injective. If $a_0z=0$ in $C_0$, its image in $C$ is killed by the specified fibre element $\bar h$, which is a nonzerodivisor by hypothesis. Its image is zero, hence $z=0$. Thus $\bar a_0$ is a nonzerodivisor in $C_0$. Moreover $a_0\in\mathfrak q_0$, since its germ $h$ lies in the maximal ideal at $x$; consequently $\bar a_0$ lies in the maximal ideal of $C_0$. The quotient $C_0/(\bar a_0)$ is nonzero, as that ideal is proper. By the regular-sequence definition the singleton $(\bar a_0)$ is therefore a regular sequence in $C_0$.

Inputs: `lem-weil-pbc-field-extension-base-change-faithfully-flat`, `lem-weil-pbc-flat-local-ring-maps`, `lem-weil-pbc-flat-local-hom-faithfully-flat`, `lem-weil-pbc-faithfully-flat-universally-injective`, `def-weil-pbc-regular-sequence`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: second paragraph, faithful flatness of the map of fibre local rings and descent of the nonzerodivisor.

### lem-trf-noetherian-fibre-regular-quotient-neighbourhood: old steps 8, 9

Old step 8:

Apply the flat-local-ring-maps theorem to the flat map $A_0\to B_0$. By Step 5 its localized map $(A_0)_{\mathfrak p_0}\to(B_0)_{\mathfrak q_0}$ is a flat local homomorphism between Noetherian local rings. Its closed fibre is precisely the quotient identified with $C_0$ in Step 6. Step 7 verifies the regular-sequence hypothesis of the Grothendieck regular-sequence flatness theorem for $c=1$ and $f_1=a_0/1$. That theorem gives $(B_0)_{\mathfrak q_0}/(a_0)$ flat over $(A_0)_{\mathfrak p_0}$. Flatness over a localization then makes this quotient flat over $A_0$.

Inputs: `lem-weil-pbc-flat-local-ring-maps`, `lem-weil-pbc-grothendieck-regular-sequence-flat`, `lem-weil-pbc-flat-over-localization`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: last paragraph, the application of Algebra Tag 00MF, equivalently the singleton case of 00MG.

Old step 9:

Set $M=B_0/(a_0)$. This is a finitely presented $B_0$-module, presented by $B_0\xrightarrow{a_0}B_0\to M\to0$, and $A_0\to B_0$ is finitely presented. Step 8 says $M_{\mathfrak q_0}$ is flat over $A_0$. Apply openness of flatness to obtain a basic open $D(g_0)$ containing $\mathfrak q_0$ on which every $M_{\mathfrak r}$ is flat over $A_0$. Put $H_0=(B_0)_{g_0}/(a_0)$. For a prime of $H_0$, let $\mathfrak r\subset B_0$ be its inverse image; then $g_0\notin\mathfrak r$ and $a_0\in\mathfrak r$. Its local ring is $M_{\mathfrak r}=(B_0)_{\mathfrak r}/(a_0)$: the identification sends $(b/g_0^n)/d$ to the same fraction in the quotient of $(B_0)_{\mathfrak r}$, with inverse induced by $b/t\mapsto(b/1)/(t/1)$. It is flat over $A_0$, and over $(A_0)_{\mathfrak r\cap A_0}$ by flatness over a localization. Affine-stalk identification and the definition of flatness show that $\operatorname{Spec}H_0\to\operatorname{Spec}A_0$ is flat. The affine criterion on its full affine chart now says $H_0$ is flat over $A_0$.

Inputs: `lem-weil-pbc-openness-of-flatness`, `lem-weil-pbc-spec-localization-away-basic-open`, `lem-weil-pbc-flat-over-localization`, `lem-weil-pbc-affine-open-stalk-localization`, `def-weil-flat-morphism`, `lem-weil-pbc-flat-morphism-affine-criterion`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: last paragraph, spreading flatness of the quotient by Algebra Tag 00RC; only the flat-quotient part of the claim is required.

### lem-trf-model-principal-quotient-return: old steps 10, 11, 12

Old step 10:

Let $g\in B=A\otimes_{A_0}B_0$ be the image of $g_0$, which is not in $\mathfrak q$ since $g_0\notin\mathfrak q_0$. The affine principal open $U=\operatorname{Spec}B_g$ is therefore a neighbourhood of $x$ inside the original $X$. Restrict the section $a$ to $B_g$. There is an $A$-algebra isomorphism $A\otimes_{A_0}H_0\cong B_g/(a)$, given by $c\otimes\overline{b/g_0^n}\mapsto\overline{c\,b/g^n}$. Its inverse is induced from $A\to A\otimes H_0$, $c\mapsto c\otimes1$, and $B_0\to A\otimes H_0$, $b\mapsto1\otimes\bar b$; $g_0$ is a unit and $a_0$ is zero there, so it factors through localization and quotient. The two maps are inverse on the ring generators. Since $H_0$ is flat over $A_0$, flat base change makes $H=B_g/(a)$ flat over $A$.

Inputs: `lem-weil-pbc-affine-open-section-vanishing-prime`, `lem-weil-pbc-flat-module-base-change`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: second paragraph, returning the quotient to the original base; direct base change of the flat quotient suffices because the Cartier assertion is not part of this item.

Old step 11:

Put $D=\operatorname{Spec}H$. For every prime $\mathfrak t$ of $H$ with inverse image $\mathfrak v$ in $A$, flatness of $A\to H$ gives the flat local homomorphism $A_{\mathfrak v}\to H_{\mathfrak t}$. These are exactly the stalk maps of $D\to V\subseteq S$ by affine-stalk localization. The stalks of the affine open $V$ equal the stalks of $S$ at its points, so these are also the stalk maps of the required composite $D\to U\to X\to S$. The definition of flatness proves that this composite is flat at every point of $D$.

Inputs: `lem-weil-pbc-flat-local-ring-maps`, `lem-weil-pbc-affine-open-stalk-localization`, `def-weil-flat-morphism`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: conclusion, flatness of the base-changed hypersurface over the original scheme.

Old step 12:

Finally write the current $B$ as $A[T_1,\ldots,T_n]/(F_1,\ldots,F_m)$, and choose polynomials $G,H_a$ representing $g,a$. Then $H=B_g/(a)\cong A[T_1,\ldots,T_n,u]/(F_1,\ldots,F_m,uG-1,H_a)$. This finite presentation and the affine neighbourhood $V\subseteq S$ witness local finite presentation at every point of $D$, by its definition. The surjection $B_g\to H$ makes $D\hookrightarrow U$ a closed immersion by the affine quotient description of closed immersions. The restricted section still has germ $h$. Since $h\in\mathfrak m_x$, its representing $a$ lies in the prime of $x$ in $B_g$ (the inverse image of the maximal ideal under the prime localization map). Thus $x\in V(a)=D$. Rename the ring $B_g$ as the $B$ in the statement; this is the required affine neighbourhood, section and closed subscheme.

Inputs: `def-sbc-locally-finite-presentation`, `def-weil-closed-immersion`, `lem-weil-pbc-affine-open-stalk-localization`.

Source: literature/stacks-project/more-morphisms.tex, Tag 056Y, lemma-slice-given-element, proof: conclusion, local finite presentation, the prescribed germ and containment of the point.

## Unfinished work

The five new statement nodes are intentionally unsplit and carry no Lean; later workers will supply their proofs in parallel, using the exact argument allocation above. No part of this item's stage-1 assembly is left without a stated dependency.

## Validation

The required initial remote dry run on 2026-10-23 exited 0 at `17b9ca65f57`, with server preflight passed and `OK (not pushed)`. After updating this report and the split-report repair record, I run the required remote dry run again and wait for it to exit successfully before the push. The final delivery command checks the packet again. No compiler or local DAG gate is run.

## Retained historical report (Q112, unchanged)

The following is archival context, not a claim about the present repair's number of new nodes or its current checks.

# Stage-1 report: lem-trf-fibre-regular-element-flat-hypersurface

Group Q112; direct-delivery worker; 2026-10-18.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibre-regular-element-flat-hypersurface.json`: statement node, now split into twelve proof steps. The statement and statement dependencies are unchanged. Mathlib verdict: no exact match or one-line specialization found; the inherited searches are retained and five actual Q112 searches have been appended.
- `citations.json`: forty step/node entries, with verbatim quotations from the cited statements.
- `report.md`: this report. `searches.jsonl` is the search command's actual log. `write_split.py` is the sandbox-local construction script, not a DAG delivery file.

There are **zero new nodes and zero new Mathlib leaves**. No unit record, shared file, Lean file or launcher file was edited; no compiler or build command was run.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag and the fibre/nonzerodivisor/flat-quotient notions. I did not find a declaration stating this item under its pointwise hypotheses. In particular, `Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber` in `WeilConjectures/Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean:981–992` concerns an ideal locally generated by regular elements at **every** prime of the fibre. That is not the hypothesis that the specified germ is regular at the one designated fibre point. Its existing node is `lem-pc-algebra-fibre-cartier-local`; I do not claim attachment of that declaration to this item.

The five recorded Q112 Mathlib searches returned flat affine/stalk criteria, smooth charts, flat localization, going down, and regular scalar multiplication on flat modules. I read the returned types and the source of the flat affine/stalk statements and `Module.Flat.isSMulRegular_of_nonZeroDivisors`. They neither construct this flat quotient neighbourhood nor specialize to it in one line. A second semantic phrasing asked specifically about a regular element on the closed fibre of a flat finitely presented algebra. No search failed or was recorded as absent when unavailable. Earlier Q19 searches remain intact, distinct from the Q112 log.

## WANTED

None. The item source and all inputs used here are already available locally.

## Problems found and corrections

The imported item is correct as written. I read `literature/stacks-project/more-morphisms.tex`, Tag **056Y**, label `lemma-slice-given-element`, statement and complete proof. The source has the additional effective-Cartier-divisor conclusion, explicitly omitted by the item's source field. I preserve exactly that omission: after constructing a flat quotient on the Noetherian model, its base change is flat without any need to kill the annihilator of the section or prove that the source's short exact sequence stays exact. Neither omitted fact is used anywhere in this proof. The ring presentation at the end separately proves the requested local finite presentation.

The existing blueprint ancestry identifies this as the 056Y input to the positive-dimensional slicing in 0570, below 055W/057J/057K and the recorded horizontal-curve flatification chain. I read the chapter/unit and the current ancestor, including its `blueprint_update`. This delivery addresses the specific auxiliary algebra input and changes neither the unit nor the ancestor. The generic off-unit tools (00RC, 02JO, 00MG and 0HA1) are declared in `split_report.tool_uses`, with their exact purpose; no maintainer-owned `tool_uses` field is set. No SGA source is used.

The main pitfalls I resolved explicitly rather than assuming them are (a) flatness only at the starting point, (b) descent of the *chosen section*, not just the algebra, to a Noetherian flat model, (c) descent of regularity through the localized extension of residue fields, (d) the nonzero quotient clause in the regular-sequence definition, and (e) recovering global flatness of the localized quotient from flatness at all of its points. No statement dispute or source error was found.

## Unfinished work

None in the stage-1 split. All cited dependencies already existed; this delivery does not attempt their own proofs or any Lean formalization.

## Review by Q112

I checked the split against sections B–E of `coord/delivery-errors.md`, with the item source and each cited node's actual statement open. This is my direct-delivery self-review, not a claim that another worker reviewed it. There are no new nodes to review or to test independently. The new proof is an argument inside the item, rather than a new node restating its flat-hypersurface clause.

1. In the affine reduction I used `def-sbc-locally-finite-presentation` for exactly the finite-presentation affine pair that it gives. I used `lem-weil-pbc-affine-open-stalk-localization`, part (c), to express the particular germ as a fraction, and `lem-weil-pbc-affine-open-section-vanishing-prime`, part (b), for the affine principal open with localized ring. The finite-presentation localization formula is written explicitly, with the inverse variable and one relation; I did not assume a theorem about arbitrary open immersions being finitely presented.

2. The initial flatness shrink uses `def-weil-flat-morphism` and the stalk-localization node to start with the correct local map. `lem-weil-pbc-flat-over-localization` explicitly equates flatness over the base localization and the original base. Thus the module version of `lem-weil-pbc-openness-of-flatness` really applies to `M=B`, a finitely presented module over the finitely presented algebra `B`. The basic-open node supplies an actual principal neighbourhood. At every point of it I return to flatness over the appropriate localized base. Only after the definition gives a flat scheme map do I use `lem-weil-pbc-flat-morphism-affine-criterion` on its full affine chart. That criterion was not incorrectly used with just one affine pair in its reverse implication.

3. `lem-weil-pbc-flat-finite-presentation-model` states the integer model, its flatness and finite presentation, and the compatible algebra isomorphism; all hypotheses were obtained in Step 2. I use only its statement, not a stage or a construction hidden inside its proof.

4. The model theorem does not itself promise a model for the selected element. I therefore descend it by writing its finite tensor sum and enlarging the coefficient subalgebra by exactly those finitely many coefficients. The base-change flatness statement `lem-weil-pbc-flat-module-base-change` and clause (1) of `lem-weil-pbc-finite-presentation-base-change-composition` give the properties of the enlarged model. Both directions of the tensor reassociation map are displayed, and the chosen element is tracked. This is a finite-coefficient construction from those statements, not an invocation of an unprovided general descent lemma.

5. The only Noetherian theorem used is `lem-weil-pbc-finite-type-algebra-noetherian`, applied first over the integers and then to the finite-type model algebra. The elementary ideal argument establishes its integer-base hypothesis. I never assert that the original base or original algebra is Noetherian.

6. `def-pc-scheme-fibre` specifies the actual scheme-theoretic fibre. `lem-weil-pbc-fibre-product-affine-spectra` identifies its coordinate algebra as a tensor product, with the projection maps. I give the tensor maps for the residue-field base change, not an unsupported identification of `A/pA` with a fibre. The affine-stalk node identifies the two fibre stalks. `lem-sbc-scheme-fibre-stalk-quotient` states the closed-fibre stalk quotient **and preservation of each element**; that is the precise equality used later to apply the local regular-sequence theorem.

7. `lem-weil-pbc-field-extension-base-change-faithfully-flat` applies to an arbitrary extension of fields, so no finiteness or algebraicity hypothesis on the two residue fields is introduced. `lem-weil-pbc-flat-local-ring-maps` applies to its flat ring map and the prime and contraction actually chosen in Step 6. `lem-weil-pbc-flat-local-hom-faithfully-flat` then applies to the resulting local map. `lem-weil-pbc-faithfully-flat-universally-injective` with module the source ring gives injection of the local rings, after the elementary source-tensor identification. I write the kernel argument showing that regularity descends. For `def-weil-pbc-regular-sequence` I also check the often-missed second condition: the descended element belongs to the maximal ideal, so its quotient is nonzero.

8. The Noetherian clause of `lem-weil-pbc-flat-local-ring-maps` is available because both model rings were proved Noetherian. `lem-weil-pbc-grothendieck-regular-sequence-flat` assumes a flat local map between these rings and a regular sequence in its closed fibre; Steps 6–7 verify precisely those hypotheses. I take its prefix quotient conclusion for the singleton sequence, not merely regularity of the lift. `lem-weil-pbc-flat-over-localization` then makes that quotient flat over the nonlocalized model base, which is the input the next openness theorem needs.

9. I read the module formulation of `lem-weil-pbc-openness-of-flatness` again for the quotient. Its finite-presentation hypotheses hold: the algebra was constructed finitely presented and the module has one generator and one relation. The basic-open node yields `g_0` avoiding the designated prime. The local rings of the quotient are identified explicitly with localizations of this module; then flatness over a localization, affine stalks and the definition prove scheme flatness. Again the affine criterion is used in its valid forward direction to obtain a flat global quotient algebra. This step does not assume a global theorem about sheaf tensor exactness or a global regularity statement.

10. The principal-open statement gives an affine neighbourhood in the original scheme because `g_0` avoids the contracted point prime. The tensor/quotient/localization isomorphism is proved on generators in both directions; the displayed inverse uses only that the denominator becomes invertible and the section becomes zero. `lem-weil-pbc-flat-module-base-change` is applied to the already-flat model quotient, and gives flatness over the arbitrary original base. The desired result does not require regularity of the base-changed element away from the point.

11. `lem-weil-pbc-flat-local-ring-maps` turns this global ring flatness into all the correct local maps. The affine-stalk statement includes the equality of stalks under the affine open immersion into `S`. Thus `def-weil-flat-morphism` gives flatness of the actual composite asked for, not merely flatness over a different target.

12. I explicitly exhibit the finite polynomial presentation after both localization and quotient. `def-sbc-locally-finite-presentation` then applies at every point with the same affine pair. The affine-quotient clause of `def-weil-closed-immersion` gives the asserted closed subscheme. The stalk localization formula checks the membership in the point prime and hence that this subscheme contains `x`. The germ has been tracked through each restriction, so it remains the specified `h`.

I checked small and boundary cases of the unchanged item. A point `x` makes its fibre local ring nonzero; a zero germ therefore cannot satisfy injectivity there. The assumption that `h` is in the maximal ideal rules out the unit case and ensures the descended singleton quotient is nonzero, even when the fibre dimension is not assumed. No reducedness, finite residue extension, Noetherian original base, or global flatness hypothesis was added. The formulas allow an empty tensor sum and zero or redundant presentation relations; where those would contradict the nonzerodivisor hypothesis the argument uses that hypothesis explicitly. Every proof step is shorter than 2000 characters, and the tensor/quotient comparisons are given by concrete maps rather than the word “transport”.

## Not duplicates

No new node is proposed. The existing `lem-pc-algebra-fibre-cartier-local` assumes local principality by regular elements at every prime of the entire fibre, whereas this item starts with one specified germ regular at one fibre point. I reuse the existing generic model, openness, regular-sequence, flatness and scheme-stalk nodes instead of creating versions of them in this chapter. Searches of the DAG by the relevant tags and keywords and searches of the whole blueprint found no exact additional blueprint statement for the item; its `same_as` remains empty. The statement, original reportable ancestry and inherited recorded searches are preserved.

## Dry-run repairs

The first delivery check requested longer quotations for the Noetherian finite-type theorem (Step 5) and the flat-local faithful-flatness theorem (Step 7). I replaced each abbreviated quotation with the entire cited statement, preserving the proof and its uses. This is a citation-format repair, not a change of mathematical dependency.
