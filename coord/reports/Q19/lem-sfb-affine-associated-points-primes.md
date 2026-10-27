## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-associated-points-primes.json: statement, split, no exact Mathlib match. Five proof steps, 2050 characters total.
- citations.json: verbatim statement quotes for every node used by each step.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none for this item. The existing declaration AlgebraicGeometry.Scheme.isLocalizedModule_affine_germ belongs to lem-sbc-affine-module-germ-localization; its source was read at lean/WeilConjectures/AlgebraicGeometry/Morphisms/AffineModuleGermLocalization.lean:47 and its DAG audit is already closed. It is only an ingredient, not an attachment for the item.

WANTED: none.

The item statement agrees with Divisors Tag 02OK (lemma-associated-affine-open), including the converse for a finitely generated prime and no finiteness requirement on the section module. No statement change was necessary. The Noetherian-ring consequence follows directly, even though the source phrases its consequence using a locally Noetherian ambient scheme.

The pre-existing blueprint.from.node was null. blueprint_refs.py ancestor also returned None because the created.item chain ends at the module-named item of lem-sfb-admissible-direct-image. I read that final node in the existing via list: its blueprint.from.node is det-thm-sf-ctf-stability-direct-images. That blueprint node exists and its current source is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md. I filled this ancestor in this item's metadata and retained the entire existing place and via chain. Paragraph (3) contains the compactification/direct-image argument which this prerequisite chain serves. The item is not the unit's key node, so no unit record is changed.

Whole-DAG tag and concept searches and blueprint_refs searches for “02OK”, “associated points”, “associated primes”, and “stalk localization” found no duplicate blueprint comparison. Existing algebra and stalk inputs were reused. Mathlib searches made with msearch.py are retained verbatim in searches.jsonl and appended to the existing item search history. I inspected the current AssociatedPrime/Localization.lean and Basic.lean: Mathlib's associated primes use radical annihilators in general (Basic.lean:33–40), with equivalence to annihilator primes under Noetherianity. Therefore its algebraic localization theorem alone is not an exact match for this item's non-Noetherian scheme comparison. The second LeanFinder phrasing found affine ring-stalk and tilde-stalk localization only. RingHomProperties.lean grep hits refer to general properties of ring homomorphisms, unrelated to associated points.

Nothing remains unfinished mathematically. Validation and delivery use the mandated remote tools only; no Lean writing or compiler invocation.

## Not duplicates

No new nodes were created. The existing Noetherian-associated-prime-from-localization leaf assumes a Noetherian ring and cannot supply the item's finitely-generated-prime converse over an arbitrary ring. Its stronger ring hypothesis was not imported. The existing general forward localization node is used directly.

## Review by Q19

I read the item source in literature/stacks-project/divisors.tex, Tag 02OK, from the statement through the end of its proof, and the parallel algebra proof of Tag 0310 in algebra.tex. I also read Schemes Tag 01HV, parts (1), (2), (6), and (7), and the existing affine-germ localization declaration and its proof. There are no new nodes needing source review. The proof follows the source's localization route, not a relabelled instance of the whole item.

Step 1 uses the actual statements of lem-weil-pbc-affine-open-stalk-localization and lem-sbc-affine-module-germ-localization. The first identifies the ring germ with localization at the prime corresponding to x; the second says that the module germ is localization of sections, with no Noetherian or finiteness assumption. The module action compatibility follows since denominators act invertibly; the induced action of a/s is a times that inverse. def-weil-pbc-localization-at-prime explicitly states the maximal ideal pR_p, and def-trf-relative-assassin defines associated points by annihilators in the module stalk. Thus this is the module-stalk comparison the proof needs, not merely the ring-stalk comparison.

Step 2 uses the precise conclusion of lem-weil-pbc-associated-prime-localize-at-prime: an actual element with annihilator p localizes to an element with annihilator pR_p. Its statement explicitly makes no Noetherian assumption and uses element-annihilator associated primes, so the hypothesis matches exactly. This generic algebraic tool is recorded in split_report.tool_uses because it belongs to another unit. The affine germ input is already Lean-closed and the ring localization input is a Mathlib leaf.

Step 3 is an elementary calculation from def-weil-pbc-module-localization, whose statement gives fraction representatives, the zero-fraction criterion, and invertibility of denominators. The associated-point witness w=m/f is multiplied by the unit f without changing its annihilator. Finitely many prime generators give finitely many s_i outside p killing a_i m. Their product kills every generator, hence the ideal. This writes the denominator argument out rather than appealing to exact localization or an uncited finite-module annihilation lemma.

Step 4 checks the other annihilator inclusion explicitly. If a kills sm, then a/1 kills m/1 after cancelling the unit s/1, so a/1 is in pR_p. Every member of the extended ideal is b/t with b in p; the ring fraction equality from def-weil-pbc-localization-at-prime and primality imply a is in p. Membership of the extended ideal has this fraction form simply by putting a finite sum of ideal multiples over a common denominator. This proves equality of annihilators, so def-weil-pbc-annihilator-associated-primes gives precisely the requested notion of association. No radical-annihilator theorem is silently substituted.

Step 5 uses exactly def-weil-pbc-noetherian-ring: every ideal is finitely generated. It invokes no finite generation of M. The cited statements are copied verbatim into citations.json; none is merely a definition used as a substitute for an unstated theorem.

For edge cases I checked the zero module (neither side has an annihilator-prime witness), a field and p=0 (the empty generating family uses product 1), an arbitrary possibly infinite module (only generators of p are used), the empty affine scheme/zero ring (there is no x and no prime), and non-Noetherian rings with a finitely generated prime (the same finite product argument applies). No new lemma hides inside a long step: all steps are under 2000 characters and the only algebraic converse calculation is the item's own proof. All dependency lists are the union of the cited uses, the statement dependencies are retained, and no dependency points back to the item.
