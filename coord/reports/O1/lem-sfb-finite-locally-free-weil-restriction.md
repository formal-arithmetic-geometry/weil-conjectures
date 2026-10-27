# Stage-1 report: lem-sfb-finite-locally-free-weil-restriction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-weil-restriction.json`: item, statement preserved, split into three steps following Stacks 05YF.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-relative-hom-space.json`: new statement-only lemma, Stacks 05Y7 specialized to schemes Z and T; no Mathlib match.
- `citations.json`: four entries, one per step/node citation, with verbatim statement quotations.

One new node; zero Mathlib leaves. No Lean written or compiled.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact item blueprint tag, Weil restriction, restrictionOfScalars and the finite-locally-free/Weil combinations found no matching project declaration. Module/sheaf restriction of scalars is a different operation. The new relative-Hom statement likewise has no matching project declaration.

## WANTED

None. The complete relevant Stacks sources are archived in `literature/stacks-project/criteria.tex` and `spaces.tex`.

## Findings and route

The imported item is true as stated; its statement and statement dependencies are unchanged. It had no proof. I read Stacks 05YF (`proposition-restriction-of-scalars-algebraic-space`), 05YE (`lemma-fibre-diagram`), 05Y7 (`proposition-hom-functor-algebraic-space`), and the definition preceding 05Y2 (`equation-hom-functor`). The proof uses the relative Hom functor, not module restriction of scalars. The Hom functor allows arbitrary maps to E over T; the fibre over the identity endomorphism of Z imposes precisely the additional Z-linearity condition.

The source marks the verification of 05YE omitted. Here it is the explicit compatible-pair computation in step 3, including both inverse maps and their compatibility with restriction. It is a few-line computation from the descriptions of the Hom spaces and sheaf fibre product, so it does not become a new node. Steps 1 and 3 cite the substantive representability and closure results instead of disguising them as elementary.

I read the chapter record and the assigned unit record, the three-level rules in SETUP, and the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The relative finite Hilbert construction is an existing auxiliary branch of the alteration/moduli route; this split keeps that branch and supplies the exact Stacks input it already requested. The existing fibre-product theorem is a generic off-unit tool, declared in `split_report.tool_uses`, not a replacement for the unit route.

The live item's inherited `blueprint.from.node` is null, and `tools/blueprint_refs.py ancestor` reports None. I preserved that value and the entire precise place and via chain rather than inventing a different ancestor; the new node follows the same ancestry and adds the item at the front of via. The historical place itself explicitly identifies det-thm-sf-ctf-stability-direct-images proof (3). This is an inherited metadata defect, not a mathematical statement dispute.

## Searches and Mathlib verdicts

Before creating the new node I searched all DAG statements/sources for 05Y7 and `proposition-hom-functor-algebraic-space`, as well as relative Hom/morphism/mapping-space keywords. No node states relative-Hom representability from finite locally free sources. Whole-blueprint searches via `tools/blueprint_refs.py search` for 05Y7, 05YF, Weil restriction, Hom functor and finite locally free found no match; the Hom-functor hit concerns finite-projective coefficient modules. Searching the latest blueprint for the two Stacks proposition labels also found no duplicate.

All five new Mathlib searches were run through the required msearch command and are retained verbatim in `searches.jsonl` and in the item's and new node's `mathlib_searches`. Two LeanFinder phrasings, LeanSearch, Loogle and source grep found no match. I read the strongest candidates, `AlgebraicGeometry.Scheme.LocalRepresentability.representableBy` (Representability.lean:195) and `isRepresentable` (:210), including the hypotheses at lines 46–58 and their docstrings. They require a supplied Zariski open scheme atlas and its local surjectivity; they do not construct this Hom functor's atlas and do not assert algebraic-space representability. The other hits are finite/flat scheme base-change lemmas or ordinary presheafed-space morphisms. The grep in Mathlib/AlgebraicGeometry returned zero hits for AlgebraicSpace, WeilRestrict, homFromFinite, hom_functor. None of these is a one-line specialization giving the new lemma.

The seven older searches already recorded on the live item are preserved as historical records; I did not invent or repeat those searches. The new searches also checked the item's subject against Mathlib: no algebraic-space Weil restriction is provided by the returned declarations.

## Not duplicates

lem-sfb-finite-locally-free-relative-hom-space vs lem-sfb-finite-locally-free-weil-restriction: the new node represents all T-morphisms from the finite locally free source into an arbitrary T-space X, without any X-to-Z map; the item represents only the Z-morphisms into a specified Z-space E. The item's proof imposes that compatibility by an actual fibre product and writes the natural bijection, rather than merely applying a renamed clause.

lem-sfb-finite-locally-free-relative-hom-space vs lem-trf-space-fibre-products-etale-covers: relative Hom representability (05Y7) constructs a mapping space; the existing theorem (02X2/04T9) closes already algebraic spaces under sheaf fibre products. Neither statement supplies the other. No existing DAG statement/source shares the new node's Tag 05Y7.

lem-sfb-finite-locally-free-relative-hom-space vs def-pc-hilb-functor: the latter defines finite locally free closed subschemes (the Hilbert functor), and does not represent relative morphisms to an arbitrary algebraic space.

## Review by O1

I checked B–E against the actual JSON, source text and every cited statement. The only new node is self-contained, statement-only, introduces S, T, Z, X, p and f, writes its functor and restriction maps, and lists the scheme, universe, finite locally free, scheme-as-space, algebraic-space and fibre-product notions that it uses. Its source is Stacks 05Y7 with the exact local label, not a mutable section number. Its proof, proof_deps and proof_origin are empty/null, as required for the next worker. There are no unrun searches or unavailable services recorded as failures to find a theorem.

For step 1 I read the entire statement of `def-trf-scheme-algebraic-space`: it gives precisely the representable sheaf h_T (also h_Z) as an algebraic space, with identity atlas. I read the new relative-Hom statement against 05Y7 and the equivalent definition immediately before 05Y2. With targets E and Z its hypotheses are exactly those in the item: both targets map to T, by pq and p respectively, and the same finite locally free p is the source in both applications. In particular nothing requires E to be separated or of finite presentation. These two cited statements supply every non-elementary assertion in step 1.

For step 2 I read `def-trf-algebraic-space` in full. It explicitly says morphisms of algebraic spaces are natural transformations. Postcomposition by q and the projection map from U times_T Z have the same map a to T; their restriction equations follow directly from composition and the defining projection identity. This is an elementary construction of the two arrows, not an application of a missing representability lemma or a covert use of a cited proof.

For step 3 I read `lem-trf-space-fibre-products-etale-covers` in full. Its first sentence applies to arbitrary algebraic spaces F,G,H over S, and explicitly gives the sheaf fibre product as an algebraic space and as the categorical fibre product. Applying it to A, h_T and B gives precisely the pointwise compatible-pair description used in the step. I use none of that node's etale-cover assertions. The equality in B forces the same a on both components and q b = pr_Z; conversely that equation implies the T-morphism condition by composing with p. Both inverse functions were written and their restriction formula checked, so the result represents the exact requested functor, not an unspecified isomorphic modification. All citations have verbatim quotations in citations.json; no proof of a cited node is used as though it were its statement.

I tested p = id_T: the fibre-product condition fixes q b = a, so the resulting space is E over T. For Z empty (rank zero), all morphisms out of the empty base change are unique, so A and B and the restriction are h_T; no surjectivity of p was invoked. For E empty and Z of positive rank over a nonempty field, there are no such b, whereas over a rank-zero component there is the unique b, exactly as the formula predicts. Variable rank is allowed throughout, since no rank is chosen in any step. Nonreduced bases and nonseparated E cause no change: the argument is an equality of morphisms of sheaves, not a set-theoretic equality of images or geometric points. No Noetherian, flatness or finite-presentation hypothesis on E has been smuggled in.

No proof step exceeds 2000 characters. The substantial new theorem is strictly the source's Hom-space prerequisite, not an elementary closure lemma or one clause of the parent. The elementary cartesian-square computation remains in the parent. The only correction made was to fill the originally absent proof and expose the substantive Hom-space dependency; no mathematical statement was changed.

## Unfinished work

The new statement-only Hom-space node is left unsplit by design for a subsequent stage-1 item. Nothing required of this one-level split is deferred. Delivery-check results are recorded below after the tools return.
