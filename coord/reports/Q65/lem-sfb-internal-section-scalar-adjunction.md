# Stage-1 report: lem-sfb-internal-section-scalar-adjunction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-internal-section-scalar-adjunction.json: statement, split; no Mathlib match. Six proof steps, no new nodes.
- citations.json: one verbatim statement quotation for each of the 16 step/node citations.
- report.md: this report.
- searches.jsonl: the search command's own records, retained unchanged.

## Attachments

None. Searched the current lean/WeilConjectures source for the exact item id and internal-abelian-sheaf-module-equivalence id, then for internal module and sectionwise notions. The exact tags have no declaration. The internal module Hom, tensor and transport files concern pieces of the construction, not this ordinary and unbounded-derived scalar comparison with its specified units and counits. No upstream sorry declaration was treated as finished.

## Literature wanted

None. WANTED: none.

## Findings and changes

The sandbox initially had no item, split, report or previous search log; only dispatcher marker files. Started from the current repository item. Its statement is unchanged, and all original fields and original search records are retained. The original proof was empty. No statement dispute or established unit-route error was found.

Read GOAL.md, the current chapter and sk-prop-scalar-six unit, and the ancestor's det-prop-scalar-six-pullback.proof.md, especially paragraph (1). This split supplies the internal-to-sectionwise scalar identification used there; it does not replace any geometric coefficient-comparison step. The item is not the unit's key statement, so no unit record was changed.

The central reuse is lem-pe-internal-section-tensor-comparison, which already gives the same-ring generator comparison, exactness, and preservation/reflection of flat objects and K-flat complexes on a general small site. It does not state change of coefficients or comparison of the two scalar adjunctions; those are proved here. Also reused the general-site flat-term K-flat replacement, derived change-of-rings, and normalized scalar-derived-Hom comparison. No new clause-shaped nodes were made.

Mathlib queries were run only through msearch.py and are in searches.jsonl and the node. Used LeanFinder twice, Loogle, LeanSearch and two source grep queries. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean lines 33-43 (sectionwise restriction only), Sheaf/PushforwardContinuous.lean lines 374-410 (equivalence from equivalent sites, not internal module reconstruction), and ModuleCat/ChangeOfRings.lean around lines 764, 813, 860 and 885 (ordinary modules). These do not state all the item's clauses, nor specialize to it in one line. The single-file grep result formats its line numbers as file fields; its raw result was retained honestly, and the separate directory grep plus direct source reading supplies the actual paths and lines. No unavailable service was recorded as absence.

## Not duplicates

No new nodes. Searched the whole DAG by internal/sectionwise scalar and tensor notions, then read the candidate statements; searched the whole blueprint with blueprint_refs.py for 'sectionwise module', 'scalar adjunction', 'internal and sectionwise', and 'K-flat resolution'. No blueprint node states the whole item, so same_as remains empty. The more general same-ring tensor transport was reused directly. Its own dependency closure and those of all additional statement tools do not reach this item.

## Tool uses

The split_report declares five generic tools from other units: lem-pe-internal-section-tensor-comparison (same-ring tensor and resolution transport), lem-pc-sites-sheaf-tensor-bilinear-universal (balanced sheaf maps), lem-pc-kflat-resolution (unbounded replacements on a ringed site), lem-pur-derived-change-of-rings (universal K-flat derived extension), and lem-pur-sheaf-ring-derived-hom-comparison (the specified derived transpose). None replaces a step of the scalar-six unit. Definitions used from other units are notions, as required by the contract.

## Unfinished work

None in this one-level split. All lower non-elementary facts already have DAG nodes. No Lean was written or compiled. Repository, launcher and other workers' files were not changed.

## Review by Q65

I read the item's actual sources in sites-modules.tex: Tag 03EK (section-tensor-product) defines the sheafified sectionwise tensor and its balanced-bilinear universal property; Tag 0GMW (lemma-sheafification-tensor) makes sheafification compatible with this tensor. I read the current blueprint's ancestor paragraph (1), which needs this comparison before using ringed-site K-flat pullback. For the derived steps I read sites-cohomology.tex Tag 06YS (lemma-K-flat-resolution), Tag 06YY (lemma-derived-base-change), Tag 07A6 (lemma-adjoint), and derived.tex Tag 09T5 (lemma-derived-adjoint-functors). In particular, I used the ringed-SITE resolution theorem 06YS, not the ringed-SPACE theorem 06YF. There are no new nodes whose sources would require a separate review. Since the internal scalar normalization is an explicit expansion rather than a verbatim source proof, proof_origin is agent.

For step 1 I opened the statements of the internal/section module equivalence, internal scalar functors and sectionwise restriction. They say exactly that the equivalence fixes underlying sheaves and restrictions and that scalar restriction precomposes the action. Evaluating that composite gives a_U(r)n, so identity components suffice and naturality is literal identity on the underlying maps. I did not assume exactness of scalar extension.

For step 2 I read lem-pe-internal-section-tensor-comparison, sk-def-sfb-change-of-scalars, def-pur-sheaf-tensor-product and lem-pc-sites-sheaf-tensor-bilinear-universal. The first gives pure-tensor preserving relative tensor comparison for two R-modules; take those modules to be S restricted along a and M. The scalar definition gives precisely the same balancing coequalizer. I checked the extra S-action explicitly by t(s tensor m)=(ts) tensor m; this avoids treating an R-module isomorphism as automatically S-linear. Both site and universe assumptions of the tensor theorem are present. All pure-tensor checks extend to sheaf maps by the quoted universal property; no sectionwise equality of sheafification with its presheaf was used.

For step 3 the two cited statements supply the coequalizer adjunction and the sheaf balanced-bilinear property. The inverse transpose s tensor m maps to s g(m) is balanced by R-linearity; the two inverse identities are written out. These prove equality of the Hom bijections and thereby equality of the specified unit and counit, not merely existence of a left adjoint. This is an elementary calculation from those statements, so the step is marked elementary.

For step 4 the tensor-comparison statement explicitly supplies exactness and preservation/reflection of acyclicity, flat objects and K-flat complexes, including total tensors. I used the localization definition to descend the termwise equivalence and its inverse, including their inverse isomorphisms; I did not use a bounded-below equivalence for an unbounded conclusion. The internal scalar definition says restriction is exact, and the already proved ordinary square transfers that exactness to the sectionwise functor. Neither direction requires the ring map to be flat.

For step 5 the K-flat resolution node states the general ringed-site result with flat terms and a quasi-isomorphism. Its hypotheses hold for (C,R_sec). The derived change-of-rings node states both invariance under quasi-isomorphisms between K-flat representatives and the universal left derived functor, with canonical independence of representatives. This gives the internal left derived pair by conjugation with the exact equivalences, using the already proved ordinary extension square. Thus I did not assume a functorial flat-resolution hypothesis for an arbitrary abstract monoidal category without establishing existence in this site case. The displayed chain isomorphism actually represents the derived comparison on flat-term K-flat representatives. All required properties are in the cited statements, not merely their proofs.

For step 6 I opened lem-pur-sheaf-ring-derived-hom-comparison. It gives the normalized derived Hom transpose for a specified ordinary scalar adjunction and a universal left derived pair, with exact restriction. Steps 3-5 supply exactly these inputs. I checked the unit roof K <- P -> Res(Ext(P)) and counit map Ext(P) -> N, s tensor p maps to s q(p), against that normalization. The ordinary comparison fixes the generators, so each map and each augmentation is identified on both sides. This proves compatibility of the specified derived adjunctions. I never claimed that scalar restriction preserves K-flatness or that underived extension is exact.

I tested the identity map R=S (both comparisons become identity on pure tensors), zero modules and the zero target ring (all extension maps and their unit/counit formulas are the unique possible maps), and the nonflat map Z/4 -> F_2. For the last case a flat K-flat resolution, not the module F_2 itself, must be used: higher Tor can remain, and the proof does not discard it. Thus the no-flatness assertion survives its basic counterexample to underived exactness. No proof step exceeds 2000 characters; each non-elementary passage is supported by a cited existing statement. I checked B1-B10, C1-C8, D1-D5 and E1-E7 of delivery-errors against the node and the source passages: new-node checks are vacuous; no clauses were relabelled as children, no foreign hypotheses or coefficient category identifications were introduced, and every citation has an exact quotation in citations.json.
