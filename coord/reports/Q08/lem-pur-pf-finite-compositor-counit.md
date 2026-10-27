# Worker report: lem-pur-pf-finite-compositor-counit

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-pf-finite-compositor-counit.json: statement item, now split into six proof steps; no Mathlib match for the full statement.
- citations.json: exact statement quotations for every citation in every step.
- report.md: this report. searches.jsonl contains the authentic new Mathlib search records. prepare.py is sandbox scratch work only.

No new nodes; no Mathlib leaves created. The original statement, statement dependencies, source record, creation record and blueprint ancestor chain are retained. The proof and its dependency union, proof origin, searches, blueprint place and split report were filled.

## Attachments

None. Searched the project WeilConjectures source for the exact blueprint tag and for composition, conjugation, counit and projection declarations. Read FiniteCoefficient/Derived/LowerStarComp.lean, the relevant portions of UpperStarCompCoherence.lean, LowerStarProjection.lean and UpperLowerStarCounit.lean. The source contains direct-image composition coherence and separate projection-counit statements, but no declaration stating the whole item. LowerStarProjection explicitly documents its dependence on sorryAx through derivedTensor; it is not evidence of an attachment.

## WANTED

None. All sources needed here are available locally.

## Problems found and corrections

The item was statement-only, with no existing sandbox attempt to preserve. No released stage-1 repair note exists for this item. Its substantive gap is normalization for the specified direct-image compositor: an arbitrary right-adjoint uniqueness isomorphism does not prove that the geometric derived comparison has the required counit. Steps 1–3 now prove that identification on resolutions and on the actual derived Hom bijections. The generic projection theorem already exists, so no new projection-composition node is appropriate. The ordinary ringed module construction and the finite operations are used directly; there is no passage through a condensed-module equivalence.

The initially drafted Hom calculation allowed an arbitrary complex K while invoking the pullback-composition lemma's K-flat normalization. Corrected Step 3 to choose a K-flat representative with flat terms and explicitly cite lem-pc-kflat-resolution. This satisfies that lemma's exact normalization hypothesis without treating its proof as part of its statement.

No statement dispute or weakening was necessary. No target or unit record was edited. The current blueprint was read through literature/blueprint/latest (COMMITS.txt: main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345), including the chapter, unit and the ancestor prop-pur-affine-space-composition-law proof. The current unit presents integration by iterated affine-line adjunctions; the proof here supplies a generic ordinary projection/composition compatibility below that route. No SGA source or smooth-purity trace route is used.

## Searches and reuse

Read the original item's recorded Mathlib hits and ran six additional authentic searches: LeanFinder with two phrasings, Loogle, LeanSearch, and two Mathlib grep queries. All services answered. The returned SheafOfModules.conjugateEquiv_pullbackComp_inv at Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:177 states the underived module-adjunction conjugacy only; read lines 150–200. CategoryTheory.conjugateEquiv_counit and its companions in Adjunction/Mates.lean:288–318 express general mate equations, without identifying these actual derived geometric comparisons. Slice-category chosen-pullback lemmas concern different functors. None is the full item's exact statement or a one-line specialization proving all its clauses.

Whole-DAG and blueprint searches used the item id, compositor, conjugate, projection, Tags 0DV0 and 0B56, and derived-mate terminology. Read and reused the existing general ringed projection-composition node and the existing K-injective, homotopy-adjunction and conjugation nodes. Blueprint search found no imported node exactly stating the whole item; same_as is empty. There are no new-node duplicate pairs to list.

## Review by Q08

I read Stacks categories.tex, lemma-compose-counits and equation-compose-counits (Tag 0DV0), sites-modules.tex, lemma-adjoint-push-pull-modules and lemma-push-pull-composition-modules (Tag 03D8 for the latter), sites-cohomology.tex, lemma-derived-pushforward-composition (0D6E), lemma-adjoint (07A6), equation-projection-formula-map (0B56), and derived.tex, lemma-derived-adjoint-functors (09T5), lemma-adjoint-preserve-K-injectives (08BJ). The direct-image-composition proof in Stacks uses uniqueness of right adjoints; the extra identification with the resolution-normalized geometric map is written out here, so proof_origin is agent. No new node needs a separate source audit.

Step 1 uses the operations definition's actual section formula, ordinary module adjunction and exactness. The composite-adjunction definition explicitly supplies the successive hom bijection and its unit. The pullback-composition statement specifies its termwise comparison on K-flat inputs. The fibre-product insertion and removal maps have the same coefficient action; tensor balancing gives the displayed ordinary pullback comparison and the unit insertion equation. This is the local calculation for this compositor, not a new general lemma hidden in the step.

Step 2 uses prop-pur-kinjective-resolutions-exist for the actual small module sites. The exact-left-adjoint hypothesis of lem-weil-pbc-right-adjoint-preserves-kinjective holds for all three pullbacks by the operations definition, because coefficients are identified constant ring sheaves. The general ringed derived-pushforward-composition statement explicitly says its component is the class of g_*j; choosing j to be the identity is legal because h_*I is K-injective. Its ordinary composite source is identified by the fibre-product map of Step 1. The finite direct-image-composition item fixes the same canonical finite operation on all unbounded inputs. No proof of exactness of direct image is assumed.

Step 3 uses the K-flat-resolution theorem to satisfy the precise computation hypothesis of the canonical pullback comparison. The termwise-adjunction-homotopy node explicitly states both homotopy adjunction bijections, and the K-injective-Hom node says localization is bijective on maps into the specified K-injectives. Its hypotheses hold for I and all the successive direct images by Step 2. Thus both derived Hom paths compute the ordinary paths of Step 1, proving conjugacy for the specified maps rather than merely existence of some isomorphism. The operations definition states that its derived adjunction is this canonical derived bijection. The conjugate definition supplies the natural-transformation bijection and its characterization. I checked both orientations: a:P_gh→P_hP_g has conjugate c^{-1}:R_gR_h→R_gh, not c.

Step 4 uses the explicit composite counit in def-weil-pbc-composite-adjunction and the conjunctive equivalence in lem-weil-pbc-adjunct-counit-identity. The conjugate definition says exactly that c^{-1} is the adjunct of e' composed with a. Cancelling P_gh(c^{-1}) against P_gh(c) gives the desired equality with its written source P_gh R_gh M. This uses no unproved preservation theorem.

Step 5 uses the full statement of lem-sfb-ringed-projection-tensor-composition: it asserts composition for arbitrary ringed topoi and arbitrary unbounded derived objects, and explicitly does not require an invertible projection. def-exchange-projection gives precisely the same counit-defined finite map, not an invertibility assertion. The finite clause of lem-pur-derived-pullback-tensor-iso identifies the same ambient canonical tensor comparison and gives compatibility with composition. I verified the endpoint normalization: the source is changed by c_M⊗1_N, and the target by c at M⊗P_gh N followed by R_gR_h(1_M⊗a_N). These are exactly the factors in the item's equation, with no swap of M and N.

Step 6 uses the finite direct-image-composition statement's identity clause, the conjugate definition's identity and inverse laws, and the generic projection node's naturality and identity clauses. The counit equation is natural because every factor is a natural transformation. Tested h=id, g=id, both identities, zero M or zero N, and the coefficient unit in degree zero: the equations reduce to the remaining map, the identity, or zero as appropriate. No boundedness, constructibility, étale origin or Tor-amplitude hypothesis was introduced. General ringed-topos tools used outside this unit are declared in split_report.tool_uses, with their purpose; they do not replace a unit proof step.

I checked delivery-errors B–E against these files: every cited node was opened and its statement read, no citation uses only a proof or definition for an unstated theorem, all cited hypotheses and coefficient categories match, proof_deps is exactly the union of uses, and citations.json copies genuine statement text. There is no new statement-only node, clause renaming, duplicate or elementary helper. Each non-elementary proof step is under 2000 characters; there is no long step concealing a separate comparison lemma.

## Unfinished work

None at stage 1. No Lean was written and no compiler, Lake or build tool was run.
