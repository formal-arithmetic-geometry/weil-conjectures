# Stage-1 report: lem-pd-generalized-tensor-normalization-unit-equation

## Files written

- dag/nodes/sec-poincare-duality/lem-pd-generalized-tensor-normalization-unit-equation.json: item split into four proof steps; statement and stmt_deps unchanged. No new nodes and no new Mathlib leaves.
- citations.json: verbatim statement quotations for both uses of the existing tensor universal-property node.
- searches.jsonl: actual msearch log; inherited searches remain in the item.

## Attachments

None. The blueprint tag and concept searches in lean/WeilConjectures found no declaration stating this item. ScalarPullbackTensorCoefficient.lean concerns scheme/scalar coefficient morphisms with specified module adjunctions; it does not state the arbitrary-site, geometric-unit assertion here. TensorBilinearUniversal.lean proves the existing tool node, not this item.

## WANTED

None. The relevant Stacks source is present.

## Problems found and repaired

The item was statement-only with an empty proof. Its statement is well-typed and true; no STATEMENT-DISPUTED correction is needed. The proof now explicitly evaluates at a geometric-unit section of the product sheaf. This avoids imposing a subcanonical site or asserting that arbitrary tensor-sheaf sections are pure. Existing statement dependencies and provenance metadata are preserved.

## Unfinished work

None at stage 1. No Lean files were written and no compiler or build tools were run.

## Not duplicates

No new nodes were created. The whole DAG and blueprint were searched (tensor unit, bilinear, generalized normalization), and the already existing lem-pc-sites-sheaf-tensor-bilinear-universal is reused. Generic unit naturality is a defining natural-transformation identity and is written out as an elementary step; no new node is justified for it. The related lem-pd-ringed-pushforward-bilinear-transfer is not needed: the item assumes p exists with its section formula.

## Review by Q75

I read Stacks sites-modules.tex, section-tensor-product (Tag 03EK), including lemma-sheafification-tensor (0GMW), the following Hom/Bilin display, and lemma-tensor-product-pullback (03EL) with its proof. Tags 03EL and 0GMW were checked against tags/tags. The third equality of 03EL is the source of this item, but its explanation is brief; the geometric-unit calculation here is explicitly marked agent-written. I also read the Poincare chapter record, the Verdier-exchange unit record, the current blueprint unit text, and the parent's accepted proof. This item remains below the parent's tensor-mate comparison and does not alter the unit's route. The ancestor command returns null because the creation chain ends at the seeded new target; the existing blueprint.from place and via chain are retained, and the blueprint search found no same_as.

For Step 1 I opened the full statement of lem-pc-sites-sheaf-tensor-bilinear-universal. It explicitly gives the pure-tensor morphism of sheaves of sets. Taking its factors to be M,N over R supplies z. I wrote the short componentwise gluing argument for Z, so this test object exists on any site without representability or subcanonicity. The normalization hypothesis quantifies over all sheaves of sets Z and hence applies to this choice.

Step 2 uses no uncited theorem: a unit is a natural transformation, and its naturality identity is displayed and evaluated for each of x,y,z. The direct image on sets is precomposition by the item's hypothesis, so the unit of Z at U is a section of FZ at vU. The component indices and source/target sheaves in all three identities match. Finite-limit preservation and the algebraic presentation are stronger background assumptions than this calculation needs.

Step 3 substitutes these identities into the assumed generalized normalization at precisely that section. The equation defining eta_X supplies each scalar insertion a_X=q_X j_X, while P acts on underlying morphisms by evaluation at vU. Thus the left side really is P(mu) eta_T, and both factors on the right are the stipulated eta_M,eta_N. No module adjunction, invertibility, naturality of mu, or coherence is used.

For Step 4 the same cited statement gives a bijection between linear tensor morphisms and restriction-compatible bilinear pairings, not merely existence of a tensor. Its uniqueness part therefore detects equality from the sectionwise pure-tensor composites. Tensoring eta_M and eta_N is the induced map of their pure pairing; p has its required formula by assumption. The hypotheses explicitly make eta_X R-linear, and mu is S-linear, so both final composites have the R-linear type required by the universal property. The quoted statement in citations.json is copied verbatim for Steps 1 and 4. This is a generic module-sheaf tool outside the unit and is declared in split_report.tool_uses with its purpose.

I checked B1–B7: no unsplit new node or duplicate notion was introduced, all objects are introduced, TeX is single-escaped after JSON decoding, the correct Stacks tags/labels are recorded, and every added Mathlib query is an actual logged msearch invocation whose hits I read. I tried two semantic phrasings and the adjunction-unit and module-pullback names. PullbackFree only proves formulas involving the tensor-unit object, not this generalized tensor comparison; ordinary unit_naturality supplies just the elementary naturality identity. Existing searches are retained without presenting them as Q75 invocations.

I checked C1–C8 against the cited node's statement: the sole non-elementary tool is the existing Hom/Bilin bijection, whose source and project declaration were opened; no proof-internal construction is used. D1–D5 hold because all substance stays in the item's four steps, no statement is moved to a new node, and no dependency can point back through a new node. For E1–E7 I checked the small cases: on the one-object point site the calculation reduces to inserting 1 into each tensor factor; A=Z and S=Z/2 works without flatness; zero modules and the zero ring give the zero maps; identity pullback and alpha=id recover the same equality; an empty site gives a vacuous section calculation and tensor uniqueness still applies. The product test is in the common module universe. Every step is shorter than 2000 characters. No source error or hidden auxiliary comparison remains.
