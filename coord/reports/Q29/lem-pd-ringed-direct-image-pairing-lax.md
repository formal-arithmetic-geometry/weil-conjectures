# Worker report: lem-pd-ringed-direct-image-pairing-lax

## Files written

- dag/nodes/sec-poincare-duality/lem-pd-ringed-direct-image-pairing-lax.json: existing statement split into six proof steps; not a Mathlib leaf.
- citations.json: one verbatim statement excerpt for each node used by each proof step (13 entries).
- report.md: this report. searches.jsonl is the search command's own output log.

No new DAG nodes; no new Mathlib leaves. The supplied sandbox contained only dispatcher briefs, so there was no earlier split to reuse. The repository item was copied without changing its statement, inherited citations, or inherited Mathlib searches.

## Attachments

None. Searched the project WeilConjectures tree for the exact blueprint tag and for direct-image pairing / pushforward lax terminology. The project PresheafOfModules.pushforwardLaxMonoidal and pushforward_μ_app_tmul concern presheaves; the sheaf and pro-etale monoidal declarations concern ambient or specialized categories and do not state unique normalized lax structure for arbitrary varying ring sheaves. Thus they do not give all clauses of this item. No sorry declaration was treated as a finished proof.

## WANTED

None.

## What was wrong or incomplete

The imported node was statement-only and had no proof. Its statement is correct under its explicit hypothesis that precomposition gives sheaf direct image. In particular, it does not need a left-exact inverse-image functor. I retained the statement. The source supplies direct image (03D6) and the tensor universal property (03EK), but does not explicitly state the uniqueness assertion: the proof is therefore marked agent-written, with the unit-forcing argument written out.

The created.item chain has no imported blueprint ancestor, as blueprint_refs.py ancestor reports. I retained its null ancestor and existing via list, and explained the precise parent step in split_report.blueprint. The item is a supporting lemma for def-pd-proetale-section-module-functors Step 2, below the Verdier-exchange route; it does not state the unit's key theorem, so no unit realized fields were changed. Blueprint searches for direct image pairing and lax monoidal found no equivalent blueprint item.

## Unfinished work

None in this one-level split. No Lean was written or compiled, and no repository or launcher file was edited.

## Not duplicates

No new nodes were created. Reused lem-pc-sites-sheaf-tensor-bilinear-universal instead of introducing a tensor universal-property node, and lem-pc-sheaf-modules-tensor-closed for the actual canonical constraints and the adjunction. No clause of the item was moved into a new lemma.

## Mathlib searches

Preserved the five inherited search records and read their reported hits. Ran five fresh logged searches for this item's unchanged question: LeanFinder in two phrasings, Loogle for SheafOfModules.pushforward, LeanSearch in words, and grep in Algebra/Category/ModuleCat. All five services answered successfully. The actual query strings and hit summaries from searches.jsonl were appended to mathlib_searches. Read SheafOfModules.pushforward in Sheaf/PushforwardContinuous.lean, unitToPushforwardObjUnit and its value lemma in Sheaf/PullbackFree.lean:60,68, and restriction-of-scalars lax structure and pure-tensor formula in Monoidal/Adjunction.lean:115,128. These are constituent facts only. General monoidal sheafification and constant-ring light-condensed modules do not specialize in one line to a unique lax structure on direct image for varying coefficient sheaves. The project presheaf result is also not the sheaf uniqueness statement.

## Review by Q29

I read Stacks sites-modules.tex, Tag 03D6 (definition-pushforward), Tag 03EK (section-tensor-product, including the displayed bilinear universal property), Tag 03EO (lemma-internal-hom-adjoint-tensor), and Tag 04TT (section-internal-hom, its definition and evaluation). I also read the chapter and unit records, the current blueprint Verdier-exchange statement, the parent's proof step citing this item, GOAL.md, the three-level restrictions in SETUP.md, and delivery-errors B through E. There are no new-node sources to audit.

Step 1 uses the statement of def-weil-sheaf-of-modules-category for the sectionwise linearity and restriction conditions. Its action is c_U(r)x, and the displayed restriction equation follows from naturality of c. The sheaf condition is already the explicit hypothesis on precomposition. The unit map is verified R-linear by the multiplication equation, rather than merely asserted to be a ring map.

Step 2 uses def-pur-sheaf-tensor-product for the restriction-compatible pure-tensor image, and the *statement* of lem-pc-sites-sheaf-tensor-bilinear-universal for existence and uniqueness of the resulting map into the sheaf P(M tensor N). I checked that the latter states the full Hom/Bilin bijection, not only a tensor definition or a fully-faithfulness assertion. All three modules in that application live on C with scalar ring R. Bilinearity is checked through c_U explicitly.

Step 3 uses the tensor definition for the tensor of morphisms and injectivity of that same Hom/Bilin bijection. Both sides are evaluated at f(x) tensor g(y). Step 4 uses the monoidal node's *statement* that the actual unitors are induced by the module unitors, and the bilinear node to detect equality. Both left and right unit composites are written, with value c_U(r)x, so neither unit equation is hidden behind the word coherence.

Step 5 uses the monoidal node for canonical associators, symmetry and the tensor-Hom adjunction, the bilinear node for testing maps out of the first tensor, and def-pur-sheaf-hom for the interpretation of sections as linear maps on localized sites. Currying the last factor and evaluating on all further restrictions justifies testing triple tensors without assuming that every tensor-sheaf section is a single pure tensor. The associativity composites are then evaluated explicitly. The citation for the monoidal node in this step quotes its entire statement, including closedness. All hypotheses are precisely sheaves of modules over a commutative ring sheaf on a small site.

Step 6 uses bilinear uniqueness to fix every tensorator, then uses the canonical left unitor at the regular S-module to force e'(1)=1. The module-morphism definition supplies R-linearity, which forces e'(r)=c_U(r). Thus uniqueness is proved for the unit as well as the tensor maps; the unit was not assumed normalized in proving its uniqueness.

For delivery-errors B and C I checked statements, tags, exact verbatim citation excerpts, and every uses/proof_deps entry. For D, the steps carry the construction and computations themselves, using only existing generic tensor tools. For E, I tested the one-object discrete site (ordinary restriction of scalars), identity coefficient maps, zero modules, the zero ring, and the empty site. The same equations work in all these cases; e'(1)=1 does not divide by a scalar or require 1 to differ from 0. No flatness, stalks, points, subcanonicity, geometric inverse image, or invertibility of c is used. Every step is under 2000 characters. The two off-unit statement tools are declared only in split_report.tool_uses with their purpose; they supply ordinary module machinery and do not replace the Verdier-exchange route. All other cited nodes define notions.
