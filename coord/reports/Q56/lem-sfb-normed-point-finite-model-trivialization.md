# Q56 stage-1 delivery: lem-sfb-normed-point-finite-model-trivialization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normed-point-finite-model-trivialization.json: statement, split into six steps; no Mathlib match for the whole item.
- citations.json: twelve verbatim statement quotations, covering every step/node citation.
- searches.jsonl: five actual Q56 searches, including two semantic phrasings, Loogle, LeanSearch and Mathlib grep. The item's previously recorded searches are retained.
- report.md: this report. write_split.py is a sandbox-only reproducibility helper, not a delivery node.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaf lem-sfb-scalar-finite-free-resolutions supplies the finite-basis assertion; lem-weil-pbc-fpqc-covering-axioms supplies arbitrary base change.

## Attachments

None. The exact blueprint tag and notion searches in lean/WeilConjectures produced no declaration of the whole item. AlgClosedFieldSite.lean:48 proves the narrower point-cover statement, already represented by lem-trf-point-cover-identity. It is reused, not reported as an attachment of the whole item. Mathlib's SheafOfModules.pullbackObjFreeIso addresses a component only and requires its own ringed-site presentation, so it is not a match for the item either.

## WANTED

None. The mathematical assembly here is agent-written from the obtained sources and existing statement interfaces; the report does not claim that Hemo--Richarz--Scholbach literally state this ordinary-module packaged assertion.

## Corrections and provenance

The mathematical statement is retained in full. The inherited JSON encoded doubled TeX backslashes in the statement; these were normalized to single TeX commands. No hypotheses or conclusions changed. In particular neither Noetherianity nor completeness was added.

The item had no proof. Its source's Lemma 4.1(2) is about dualizable derived objects, not directly an ordinary-heart free-module theorem. The split instead uses the supplied ordinary constant local model, an abstract finite basis, and explicit tensor coordinates. It does not assume an arbitrary lisse object is locally a finite constant heart module.

The ancestor command returns None: the inherited created.item chain ends at Sheaf.SixFunctors.CtfStabilityDirectImages, which is not a DAG node. I kept the inherited blueprint.from.node and via fields, filled the explicit finite-model-lifting place, and recorded the current blueprint Paragraph (3) provenance in split_report. The current main-20261015 stability statement/proof and chapter were read, together with the unit record. This is a local coefficient tool below the existing direct-image route, not a replacement of that route.

## Not duplicates

No nodes were created. Whole-DAG and blueprint searches by finite model, finite constant, covering sieve, weakly contractible, finite basis, and algebraically closed found component results but no equivalent statement. Relevant existing component nodes were read and reused. In particular no new point-cover, immersion-factorization, finite-basis or continuous-realization node was introduced.

## Review by Q56

I read Hemo--Richarz--Scholbach, Section 3 (Example 3.1, Remark 3.2 and Definition 3.5, printed pp.6--7), and Lemma 4.1 on printed p.8. Example 3.1 identifies the coefficient sheaf on any scheme with continuous functions on its underlying space; Remark 3.2 gives constant-module scalar extension. These statements do not require a complete field. Lemma 4.1(2) is useful context but is not needed in the proof. There are no new nodes whose sources need separate review.

Step 1 uses exactly the final sentence of lem-weil-pbc-field-point-factors-through-immersion: existence and uniqueness of a factorization with the same algebraically closed field. I read that whole statement and the field-valued-point discussion preceding Stacks 01J9 in schemes.tex, plus 01L7 (lemma-immersions-monomorphisms). The hypothesis is an actual immersion and the point's image belongs to its image, so the lemma applies to open, closed and general locally closed immersions. The argument is not the false claim that any morphism with set-theoretic image in a closed subscheme factors through it.

Step 2 uses the actual family condition of def-weil-pbc-proetale-covering, clause (3) of lem-weil-pbc-fpqc-covering-axioms, the base-change clause of sk-lem-pe-weakly-etale-stability, and the whole point-cover conclusion of lem-trf-point-cover-identity. I opened every statement and read Stacks 022D (topologies.tex, lemma-fpqc), 094U (more-morphisms.tex, lemma-base-change-weakly-etale), and 0982/098H (proetale.tex). I also read the existing proof of Scheme.ProEt.id_mem_of_mem_topology_of_iso in lean/WeilConjectures/SixFunctors/ProEtale/AlgClosedFieldSite.lean. The pullback is along the arbitrary scheme map y, not along a supposed site object. After that base change, the covering really is in the small site of s, so the existing point-cover statement applies with its identity isomorphism to Spec k. Membership of the identity in the sieve generated by this particular family is spelled out as factorization through an original family member. Thus it selects the same index j whose given model will be used, not a new unspecified model or a new extension of k. The fibre-product equation explicitly verifies v_j z = y.

Step 3 uses the field clause, not the DVR clause, of the existing Mathlib leaf lem-sfb-scalar-finite-free-resolutions. I read its statement, Mathlib match and the source declarations named there. Its hypotheses are exactly an abstract finitely presented module over a field, which the selected P_j is. It gives r and the actual basis isomorphism, including rank zero; no topology on P_j or continuity of an arbitrarily chosen linear equivalence is being presumed.

Step 4 is an elementary calculation from the constant-extension meaning in det-def-sfb-constructible-local-model and the tensor coequalizer definition in def-sfb-modobj-extension. I opened both complete statements. The model node explicitly supplies the constant scalar map and says Lambda_U tensor P means extension of the constant module sheaf. Both maps B and A are written, their balancing is F-linearity, and the two inverse identities are the basis and coordinate identities. These are defined on the presenting tensor and pass to sheafification. This avoids citing a theorem for finite coefficient-ring extensions when P_j is merely a module. The step does not extract a theorem from the proof of a definition node.

Step 5 uses the stated pullback formula and composition isomorphisms of sk-def-sfb-module-pushforward-pullback, the explicit additivity assertion in def-sfb-module-upper-star, and the coefficient isomorphism of lem-sfb-alpha-iso for an arbitrary condensed ring. I read those statements and the current blueprint module-pullback definition. The regular module comparison is proved by the displayed tensor multiplication/unit inverses. Additivity transports the displayed finite biproduct equations, so the finite-free comparison is a few-line calculation rather than an unmentioned monoidality theorem about arbitrary modules. The composition direction is y^* isomorphic to z^* v_j^*, with v_j z = y. The resulting basis is the pulled-back specified model and chosen abstract basis, as requested.

Step 6 uses only the full statement of lem-weil-pbc-condensed-field-continuous-realization, which I opened. It applies to any scheme and any totally disconnected normed field, hence in particular to s and this F. Example 3.1 was checked directly: continuous maps from the singleton |Spec k| to F are F, and constant sections are inverse to evaluation. The finite-biproduct coordinates are obtained by applying sections to the injection/projection equations; their preservation follows directly from sectionwise composition and addition. The scalar action is therefore the requested constant-section action. No unproved exactness of geometric stalks or conservativity for arbitrary pro-etale sheaves is used.

I checked B--E of delivery-errors point by point: there are no new statement-only nodes to malformedly introduce notions, no duplicate or relabelled clause, and all non-elementary inputs are the explicit cited statements. All twelve quotations in citations.json are verbatim substrings of the actual statements, and each is long enough to contain the relevant assertion. Each step is under 650 characters, so no long step conceals a new lemma. I traced statement/proof dependencies of every ingredient and found no path back to the item. The off-unit geometric and coefficient statements are declared as generic tools in split_report, not entered as maintainer-owned tool_uses.

I tested P_j=0/r=0 (all formulas are empty sums), a nontrivial nilpotent closed immersion (field-valued points kill the defining ideal), open immersions, empty components in the covering, and infinite covering families. An empty S is excluded by the assumed geometric point in its image; a completely empty cover cannot cover the nonempty s. Only one original member is selected, so no uniform rank, uniform trivialization, finite covering index set, Noetherianity, or completeness is needed. The norm topology is used only for the existing continuous coefficient realization. No SGA source, Lean writing, compiler, Lake or build command was used.

## Unfinished work

None in this one-level split. Existing cited unsplit component nodes remain their own items. The inherited missing root provenance is reported above; no unrelated node or contract file was edited.
