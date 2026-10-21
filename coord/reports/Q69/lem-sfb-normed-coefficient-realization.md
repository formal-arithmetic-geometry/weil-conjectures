# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-normed-coefficient-realization.json`: existing statement, now split in ten steps. Whole-item Mathlib verdict: no match. No statement change.
- `citations.json`: 26 step/node entries with verbatim statements, including their hypotheses.
- `searches.jsonl`: actual msearch records, retaining the algebraic-embedding ingredient search as well as the whole-item searches.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed: this supporting item is not its unit's key statement. The sandbox also contains the item-scoped generation script `write_split.py`.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the blueprint tag, `normed.coefficient`, `coefficient.realization`, and isometric coefficient terminology. No declaration states the entire item without sorry. The existing Mathlib leaf `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed` already carries `IsAlgClosed.lift`; no new embedding leaf was created.

## WANTED

None needed for this split. The older absolute-value node mentions unavailable Serre/Bosch--Güntzer--Remmert books, but it is now a Mathlib leaf. I read the actual `spectralNorm_unique_field_norm_ext` declaration at Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:770, so this proof uses the available result rather than attributing a proof to an unread book.

## Faults and corrections

The item had a statement, earlier Mathlib searches and no proof. I retained its statement, source, inherited searches and blueprint provenance. Its source's reference to Bhatt--Scholze Remark 6.8.15 supplies conventions and ambient functors; that remark does not itself prove the isometric realization or the coefficient-normalized equivalence claimed here. The new proof is therefore explicitly agent-written. It does not assert that arbitrary internal locally finitely presented modules coincide with another adic or finite-Tor coefficient model.

I initially considered the existing sheaf-ring tensor-transport and condensed constructibility results. The latter concerns the different finite-Tor category, so it cannot prove this item's particular stratified locally finitely presented definition. Instead step 6 transports the finite cokernel presentation and keeps the same covers and strata. No irrelevant citation was retained. No statement dispute or replacement of the open-finiteness route is involved.

## Unfinished work

None for the one-level stage-1 split. This delivery writes no Lean and claims no new formal proof. Existing dependency nodes keep their own states.

## Not duplicates

No new nodes. The whole DAG and blueprint were searched for the algebraic embedding, absolute-value uniqueness, ring-isomorphism equivalence, exact derived functors, finite presentations and K-injective preservation. I reused the existing nodes rather than creating special cases. `blueprint_refs.py search` was also run for `isometric`, `ring-isomorphism`, `normed coefficient`, `ring-sheaf isomorphism`, `algebraic extension into` and `IsAlgClosed.lift`. None is a second blueprint statement of this whole item, so its `same_as` stays empty. The ancestor command gives `lem-sfb-dc-lower-star-preserves`, agreeing with the retained precise `blueprint.from.place`.

## Review by Q69

I read the stage-1 brief, the three blueprint levels in SETUP, GOAL, the worker role, the stage-1 document and delivery-errors B--E. I read the current six-functors chapter and open-coefficients unit, and the current blueprint text of `lem-sfb-dc-lower-star-preserves`. This item supports its normed-coefficient presentation clause, not its finiteness argument. I read Bhatt--Scholze Definition 6.8.1, the coefficient/constructibility context through Proposition 6.8.14, and Remark 6.8.15 in the local PDF. These give the intended coefficient fields and ordinary derived images. Each extra argument below is written out rather than being attributed to that remark.

For step 1 I opened the existing embedding node and Stacks fields.tex, Tag 09GU, `lemma-map-into-algebraic-closure`. Its statement supplies an embedding of an algebraic extension over the specified base. The powers argument verifies algebraicity from finite dimension; the image-basis argument verifies that the image is a finite intermediate field. I read Mathlib IsAlgClosed/Basic.lean:350 after msearch found `IsAlgClosed.lift`. It is exactly the already-existing ingredient, not a match for the whole item. No separability or normality hypothesis is required.

For step 2 I read the entire statement of `lem-weil-l-adic-extension-absolute-value` and the Mathlib uniqueness declaration cited above. Pulling the fixed algebraic-closure norm back along the injective base-linear embedding is an absolute value extending the *normalized* base value, so uniqueness applies to precisely the two norms at issue. This proves equality, not merely equivalence of topologies. The unit-ball equality and both directions of continuity then follow directly from that equality.

For step 3 I read both definition nodes it cites. The condensed-ring node explicitly says continuous homomorphisms act by postcomposition and do so functorially; the pulled-back-coefficients node explicitly says that pulling back ring objects is functorial. Thus the displayed inverses and the square of coefficient inclusions follow from their statements, without assuming a different definition of the full algebraic-closure condensed ring.

For step 4 I read clauses 4 and 5 of `sk-def-sfb-change-of-scalars`, both in its current node and its blueprint file. They explicitly give exactness, the inverse equivalence, and extension along an isomorphism as inverse restriction. I checked the directions: an S-scalar acts by its inverse image under c. I read the exact-derived-functor and exact-triangulated-functor node statements and Stacks derived.tex Tag 015F. They apply to the additive exact module equivalence, so the derived extension is the required exact triangulated equivalence on the unbounded categories. No assumption about bounded complexes enters.

For step 5 I opened `lem-weil-pbc-exact-functor-complex-cohomology` and read the homology.tex Tag 010N context. Its natural identification of kernels and images gives precisely the cohomology comparison used. Applying it to both inverse equivalences proves preservation of every upper and lower bound, including zero objects.

For step 6 I opened all five cited definitions/results: constructible module, change of scalars, finitely presented module, locally finitely presented module and bounded constructible. Finite presentation here really is a finite cokernel presentation of copies of the regular module. The inverse restriction carries that regular module to the new regular module using c, preserves the finite biproduct and cokernel by exact additivity, and commutes with the specified pullback of actions. Therefore the same local covers and finite strata work in both directions. This is a short consequence of the stated equivalence and definitions, not a new independent node or a claim about finite-Tor constructibility.

For step 7 I opened `sk-def-sfb-coefficient-morphisms` and `sk-def-sfb-module-pushforward-pullback` in full. Alpha is explicitly a component of the natural point-pullback comparison, and eta is explicitly its mate. Naturality gives the coefficient square and its adjunct square. Substitution of the inverse square in the given module-action formula proves that the identity on the actual underlying direct image is linear. This checks the maps induced from the point, not just an unspecified isomorphism between abstract functors.

For step 8 I read `lem-sfb-comap-preserves-k-injectives` and its current blueprint statement, as well as the derived-category and module-derived-pushpull nodes. The hypothesis requires finite-limit preservation for *every* scheme. Clause 5 of change of scalars proves this uniformly for the pulled-back inverse ring isomorphism. The cited K-injective theorem consequently applies in its stated direction to P. The module-derived node specifies K-injective computation for the total module direct image, so the two terms really are evaluated on I and P(I). I also opened `lem-sc-kinjective-quasi-iso-comparison`, whose statement explicitly gives the bijection from homotopy morphisms into a K-injective to derived morphisms, and read Stacks derived.tex `lemma-K-injective`, clause (3). Together with resolution existence from the derived-category node this gives the K-injective homotopy model equivalence; naturality is taken there. This extra citation was added on self-review because the derived-category definition alone did not state full faithfulness. This avoids mistakenly citing the bounded-below-only `lem-sp-kinjective-computes`.

For step 9 I reread the actual underived adjunction in the module-pushpull statement and sites-modules.tex Tag 03CZ, `lemma-adjointness-tensor-restrict`. I checked both tensor directions and the balancing equation. The two unit maps agree on 1 tensor m, and the two counit maps agree because c(a) acts in P(M) as a. These formulas supply the compatibility rather than saying that counits simply transport.

For step 10 I read `sk-prop-sfb-cartesian-coefficients`: its untwisted assertions have no invertibility hypothesis on the scheme, and its exactness applies to the embedded E' and O_E' coefficients for arbitrary scheme morphisms. The underived comparison and exact equivalences then give exactness for the abstract presentation. I read the full statement of `lem-sfb-resolving-derived-adjunction-normalization` and Stacks derived.tex Tag 09T5, `lemma-derived-adjoint-functors`. Its normalization explicitly applies to a universal left derived pair on a left resolving class and a K-injective target. Exactness permits taking all source complexes; step 8 supplies the corresponding K-injective targets. Its conclusion is precisely agreement of localized and ordinary Hom transposes. Thus the counit compatibility already checked in step 9 becomes the derived counit compatibility. The existing localization-universal-property node supplies equality/naturality after localization. I checked that no cited statement depends back on this item.

The two non-Mathlib off-unit tools, K-injective preservation and resolving derived-adjunction normalization, are declared in `split_report.tool_uses` with their purposes. They are generic categorical tools, not substitutes for the open-coefficients unit's route.

For delivery-errors B I checked that there are no fresh nodes or missing searches to disguise a new notion, and every cited statement is self-contained with its hypotheses available. The TeX uses single decoded backslashes. For C1/C4 I opened every proof citation and wrote a verbatim statement into citations.json; the preceding paragraphs specify what each step actually takes from it. Non-elementary steps cite the relevant results, and the elementary steps give the action, cokernel or tensor calculation. For D no clause has been moved to a new node, no claimed argument is circular, and no new statement merely relabels the item. For E I tested E=Q_ell, zero modules/complexes, m=0 or n=0 in a presentation, the empty scheme and identity scheme maps. The formulas still apply; no nonempty, finite-type, Noetherian or ell-invertibility restriction is silently imposed. The choice of field embedding is not claimed canonical. All steps are shorter than 2000 characters (longest 1180), and I checked that none hides a separate standard comparison lemma.

## Validation

The standalone server review_split passed. The first complete dry run passed at 9cdb3eb30e6; subsequent self-review added the explicit existing K-injective Hom comparison citation to close C4 in step 8, so the final package is dry-run again before pushing. No local DAG check, compiler, Lake or build tool was run.
