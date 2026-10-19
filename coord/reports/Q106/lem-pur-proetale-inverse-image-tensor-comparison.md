# Stage-1 repair: lem-pur-proetale-inverse-image-tensor-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-proetale-inverse-image-tensor-comparison.json` — repaired split of the existing statement; statement unchanged; zero new nodes and zero Mathlib leaves.
- `citations.json` — current verbatim statements for every node cited in each of the eight steps.
- `report.md` — replaces the inaccurate review narrative of the returned version with the repairs below. Existing `mathlib_searches` and `searches.jsonl` are retained.

## Attachments

None. Searches for the exact blueprint tag and for inverse-image/tensor terminology under the read-only slopmaster2 `WeilConjectures/` found no project declaration giving the item with all its clauses. The master source is reference material, not evidence of a closed proof.

## WANTED

None.

## What was wrong and what changed

The returned head was identified by the maintainer as `f52f271a88`. Its retained sandbox proof matches the five-step version described in the return; the current repository still has the unchanged statement and original created.item/blueprint ancestry. The delivery tool rebases the sandbox delta on current main. No git command was run in the shared repository, and no shared or Lean file was written.

1. C4/E1: the old proof applied `lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail` without supplying its operation transport, scalar-extension, pushforward and module-adjunction witnesses. I replaced that application by the existing, more focused `lem-weil-pbc-canonical-ringed-tensor-comparison-construction`. Step 1 gives all its data: the actual sites and geometric adjunction, the inverse-image ring and module presentation with its operation transport, identity scalar map, and the objectwise and morphismwise scalar-extension functor. The construction's normalization is stated in `def-weil-pbc-canonical-ringed-tensor-comparison`, also cited. The unavailable hypotheses of the old application are not silently assumed.
2. C4/E5 (uniqueness): agreement on original pure tensors does not immediately give local generation after inverse image. Step 3 now passes to adjoints, verifies their scalar action with the module adjunction, uses the sheaf tensor universal property on the original site, and then uses injectivity of the adjunction. This also supplies the equality criterion actually used in the coherence clauses. The old local-bijectivity citation is removed.
3. C4/E5 (composition): step 5 invokes the existing composition-generators lemma, which explicitly states its adjunction-unit equation, with both site functors instantiated. It derives the section normalization of gamma and its uniqueness. Step 6 writes the product-projection and operation-naturality equations which show that gamma transports the ring and module structures. Step 7 then checks the two tensor composites and applies the justified adjunction equality criterion.
4. E3/E4: step 8 proves that `(U,id)` is INITIAL in I_U, terminal in I_U^op, and gives the restriction cocone H(W) -> H(U). The resulting presheaf is H, and the unit becomes the sheafification unit of the already-sheaf H. This corrects the reversed orientation of the returned proof.
5. B9: restored the exact repository blueprint ancestry: `lem-pur-finite-kummer-level`, via `lem-pur-tate-inverse-limit-base-change`, at the recorded final sentence about tensor naturality under base change. No historical origin was replaced by a claim of no origin. `same_as` remains empty after the earlier whole-blueprint comparison and the current searches; `created` and the unchanged statement are preserved.
6. C8: every generic cross-unit interface actually used in the repaired proof is declared individually in `split_report.tool_uses`, with its purpose. No maintainer-owned top-level `tool_uses` was written. These generic sheaf, tensor, adjunction and composition tools do not replace the finite-Kummer/purity route.

## Review by Q106

I read the item and the current repository version, the unit `sk-def-purity-conv` and chapter record, and the blueprint ancestor `lem-pur-finite-kummer-level`. The item's source is Stacks `sites-modules.tex`, Tag 03EL (`lemma-tensor-product-pullback`), together with Tag 03EK's bilinear characterization of the sheaf tensor product. I read those passages, Tag 03D2's product-based module operation construction, and Tag 03D7's module adjunction. I also read `proetale.tex` Tag 09A5 (`section-morphism`) and `sites.tex` Tags 00VE (`lemma-adjoints-u`), 00WX (`lemma-adjoint-sheaves`), and 03CB (`lemma-composition-morphisms-sites`). The coherence and uniqueness details are agent-written expansions, so `proof_origin.by` is now `agent`. There are no new statement-only nodes requiring additional source review.

For step 1 I opened the statements of the pro-etale inverse-image definition, algebraic inverse-image presentation, canonical comparison definition and its construction lemma. The first supplies a geometric adjunction and operation-map construction on the small pro-etale sites; the second requires precisely the operation transport recorded in the proof. The construction lemma assumes object and morphism scalar-extension equalities and an algebraic presentation, all explicitly specified here, and yields the normalized structure defined by the fourth citation. I use arbitrary commutative sheaf rings throughout, with S = RI = h^{-1}O, not an unidentified constant coefficient ring.

For step 2 the tensor universal-property citation states a bijection from module maps to bilinear pairings on sheaves, so it really supplies the map a_M and the equality test on pure tensors. The identities a_M q_M = 1 and q_M a_M(a tensor m) = 1 tensor am = a tensor m are written out. The canonical comparison definition supplies normalization for every test SHEAF Z, not just for representables. Taking Z = |F| times |G| avoids any subcanonicity assumption: naturality of the adjunction unit with its two projections gives the claimed normalization on original sections. The construction gives an isomorphism and simultaneous naturality, which are retained under the natural a_M identifications.

For step 3 I checked the actual module-adjunction statement, especially that its pushforward action is through the adjunct of c. At c = identity that map is eta_O, exactly the action needed by the two adjoints. The inverse-image definition supplies the underlying adjunction and unit. The tensor universal-property node supplies equality from the pairings on ORIGINAL F(V) and G(V). Thus equality is obtained on the original site before transposing back; the proof does not infer that every section after inverse image is a single original representative.

For step 4 I checked that restricting scalars of the larger-ring tensor pairing is bilinear for the smaller ring, so the same universal-property node gives pi and pi'. Both composites are linear over h^{-1}O and have the same source and target. Their values and naturality of eta for pi are written out, and step 3 applies with this target. No flatness, injectivity or surjectivity of the ring map is assumed.

For step 5 I opened `lem-trf-site-inverse-image-composition-generators`. Its statement supplies exactly the unit-normalized comparison for arbitrary small sheaf-preserving site functors and its generator formula. Here v = u_h and u = u_g satisfy those hypotheses by the pro-etale inverse-image definition. I use the inverse of its kappa, so the direction of gamma is the one in the item; I wrote the resulting unit formula. The cited pro-etale functoriality node supplies the composition isomorphism already named in the statement, and I do not attribute the missing unit or structure formulas to it. Uniqueness is explicitly an application of the set-sheaf adjunction.

Step 6 writes what structure transport means: the two projections force p_1 gamma_{A times B} = (gamma_A times gamma_B) p_0, and naturality for every binary operation then intertwines those operations. Terminal-object uniqueness handles zero and one. This is a direct argument from naturality and the cited definition of operations, rather than an additional structure-transport lemma hidden behind that word. The tensor universal property then defines the factorwise tensor maps. Step 7 uses the already-proved unit and pure-tensor formulas on each side, and the equality criterion of step 3 for h composed with g. Its only inputs are preceding steps, so it introduces no uncited black box.

For step 8 I compared both arrow directions against the literal definition of I_U and its opposite. On a one-arrow test category U -> W, the colimit diagram indeed runs H(W) -> H(U); this detects the old reversal. The sheafification definition states its universal property, which suffices for sheafification of an existing sheaf and its unit. The tensor universal property then proves the identity assertion. I also tested zero rings/modules and the empty scheme: the maps are still the unit/tensor maps of the corresponding trivial sheaves, and no use of a nonzero section, faithful stalk functor, nonempty cover or flatness occurs. General non-subcanonical small sites are allowed by all the generic tools used.

Every cited statement is open in `citations.json` verbatim. All eight proof steps are below 2000 characters (maximum 1275 in the current version), and I checked that the short elementary steps use only the displayed equations, definitions and preceding proved steps. The generic construction and adjunction arguments remain cited nodes rather than inline hidden lemmas. There is no statement dispute: it was the returned proof that failed, not the item statement.

## Mathlib searches retained

The eight recorded searches from the original attempt are retained unchanged, and I read their actual entries in `searches.jsonl`. Their two phrasings concern the same unchanged item; no new node or changed search question requires repeating them. LeanFinder/LeanSearch returned ordinary sheaf pullback, pullback/free-module and monoidal sheafification declarations, not the arbitrary-ringed pro-etale normalized tensor statement with uniqueness and coherence. I read the relevant pullback API in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, including `pullback`, `pullbackPushforwardAdjunction`, `pullbackIso`, and the identity/composition interfaces. Those do not themselves supply this item's tensor comparison. Both malformed Loogle responses remain recorded as unavailable, rather than being converted into a claim that a valid search found no theorem. No search not run is added to `mathlib_searches`.

## Not duplicates

`lem-pur-proetale-inverse-image-tensor-comparison` vs `lem-kun-inverse-image-monoidal`: the latter is a derived tensor comparison for etale sheaves with constant coefficients; this item is underived, arbitrary-ringed, and pro-etale, and adds change-of-rings and composition coherence.

`lem-pur-proetale-inverse-image-tensor-comparison` vs `lem-pur-isomorphism-inverse-image-tensor-hom`: the latter assumes the scheme morphism is an isomorphism and also treats internal Hom and inverse limits; this item applies to every scheme morphism and proves the module tensor comparison with change-of-rings and composition clauses.

No new node is introduced. Existing normalized ringed-topos tensor construction, module adjunction, tensor universal property and site-composition nodes are reused.

## Unfinished work

None in this stage-1 split. Validation and delivery are performed with the prescribed server-side delivery tool; no Lean files, compilers or build tools are used.
