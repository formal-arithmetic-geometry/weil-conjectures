# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sl2-universal-multiplicative-cover.json: existing statement, now split into nine steps; Mathlib has no declaration proving the whole item.
- dag/nodes/sec-six-functors-basics/lem-sfb-special-linear-picard-zero.json: new statement-only prerequisite, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-simply-connected-multiplicative-lifting.json: new statement-only prerequisite, unsplit; no Mathlib match.
- citations.json: one verbatim cited-statement quotation for every step/node pair.
- search-results.json and searches.jsonl: actual command outputs and the mandatory search log.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for SL2, PGL, SpecialLinear, multiplicative isogeny and universal covering. No project declaration states the item. Abstract-group centre and commutator results do not prove its group-scheme covering assertion. The existing commutator-generation Mathlib leaf is reused.

## WANTED

None. All mathematical source passages used are available in literature/milne-algebraic-groups_iAG2017.pdf, which I read with pdftotext. No SGA source is used.

## Problems found and corrections

The imported item has no proof and no lean_audit record. Its statement is correct, including characteristic two, and is unchanged. Milne 20.31 explicitly refers back to Example 18.20; I use that Picard/character proof (18.19) rather than the second normalizer-degree proof. This is a choice below the blueprint unit, not a replacement of its direct-image or alteration route.

Some tempting citations create a cycle: reductive-borel-pair-structure, semisimple-multiplicative-universal-cover, semisimple-characters-trivial and reductive-radical-quotient eventually depend on this item. They are not used. Semisimplicity is instead proved using the already existing general-linear-reductive, perfect-solvable-unipotent-torus and connected-action-torus-rigidity statements. The character group of SL2 is computed from the existing abstract-group commutator leaf, reducedness and the Nullstellensatz.

The inherited blueprint.from.node is null. The read-only ancestor command also returns None: following created.item ends at the non-node Lean module Sheaf.SixFunctors.CtfStabilityDirectImages after admissible-direct-image. I preserved this inherited null and the complete via chain, and named the exact ancestor proof place in from.place and split_report. I read the newest blueprint (main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), sec-six-functors-basics/sk-thm-sf-ctf-stability, especially direct-images proof (3). The unit and chapter records were read and not edited.

The source proof of 20.24 says 'at least three elements', although its choice b != +/-1 does not work over F3 (SL2(F3) is not perfect). The existing commutator-generation node has the correct explicit hypothesis a != 0 and a^2 != 1. Step 5 proves F infinite before applying it; thus this source slip is not imported into the split.

## Not duplicates

lem-sfb-special-linear-picard-zero vs lem-sfb-character-picard-isogeny-sequence: the existing node states an exact sequence for an arbitrary multiplicative isogeny, and does not compute Pic(SLn).
lem-sfb-special-linear-picard-zero vs lem-sfb-borel-characteristic-picard-sequence: the existing node states the characteristic exact sequence and does not compute Pic(SLn).
lem-sfb-simply-connected-multiplicative-lifting vs lem-sfb-semisimple-multiplicative-universal-cover: the existing node asserts existence of a simply connected cover, not the unique lift through another isogeny; it also has a cyclic dependence on this item.
lem-sfb-simply-connected-multiplicative-lifting vs lem-sfb-reductive-torus-simply-connected-cover: the existing node gives a central product cover of a reductive group; it does not state the universal lifting property.
lem-sfb-simply-connected-multiplicative-lifting vs lem-sfb-sl2-universal-multiplicative-cover: the new node is a general formal lifting theorem conditional on simple connectedness; it gives no assertion that SL2 satisfies that hypothesis, is semisimple, or has centre mu2. Steps 2--8 carry these substantive arguments.

Whole-DAG statement/source searches used Picard, SLn, special linear, 20.30, 18.8, 18.19, universal covering, simply connected and multiplicative isogeny. Whole-blueprint searches with tools/blueprint_refs.py covered Picard, special linear, simply connected, universal covering, multiplicative and multiplicative isogeny. No matching blueprint statement exists. Project Lean was searched before creating the two prerequisites. No new node bears a Stacks tag, since their source is Milne rather than Stacks.

## Review by Q92

I read the source for the item at Milne 20.31 (p.418), including its first sentence referring to Example 18.20, then 18.17--18.20 (pp.391--392), 20.24 (p.416), 20.30 (p.417), 18.5--18.8 (pp.388--389), 19.19 (p.401), 12.37 (p.244), and the radical discussion in 17.62 (pp.372--373). For the Picard prerequisite I read 20.30 and its use of GLn = SLn x Gm from 2.42. For the lifting prerequisite I read both 18.6(a) and the fibre-product proof of 18.8; over the algebraically closed F, perfectness supplies the reduced identity component used there. Their statements introduce all their objects and definitions, and have no proof text, proof dependencies or covert proof sketches. The Picard node points to determinant, affine spectrum and the general invertible-module definition, not the curve-only Picard definition. The lifting node explicitly defines multiplicative isogeny and its universal hypothesis.

Step 1 takes smoothness, geometric connectedness, finite locally free rank two, faithful flatness, and the scalar kernel from projective-matrix-central-cover. I opened that statement: it includes all of these, with no invertibility hypothesis on r. Identifying F[t]/(t^2-1) with F[Z/2] is elementary and keeps its nilpotents.

Step 2 uses no external result. I multiplied the two 2-by-2 matrices: the upper unit transvection gives c=0 and a=d; the lower one gives b=0. The determinant condition then gives a^2=1 over every commutative algebra. The converse holds after every extension, exactly the scheme-theoretic centre condition. No field-point density is used for this calculation.

Step 3 cites precisely general-linear-reductive, which says GLn has no nontrivial smooth connected normal unipotent subgroup. I checked the missing normality hypothesis explicitly: adjoining a square root of det(g) gives a monic free rank-two faithfully flat algebra even in characteristic two; its root is a unit, and g/t lies in SL2. Scalar conjugation is trivial, so the normality equations for U descend. This proves SL2 reductive without any root datum or classification input.

Step 4 cites perfect-solvable-unipotent-torus for the canonical unipotent subgroup, its normality in the ambient smooth group S, and the torus quotient. These are all clauses of the cited statement; F is perfect and N is smooth connected solvable as required. Step 3 kills that subgroup, and connected-action-torus-rigidity then makes the remaining normal torus central. Its statement applies to smooth geometrically connected S (over algebraically closed F) and arbitrary torus N. A Laurent polynomial ring of positive rank cannot be a finite-dimensional quotient of the coordinate algebra of mu2. This checks the absence of a radical without citing the circular radical theorem.

Step 5 uses sl2-field-commutator-generation only with an a satisfying its explicit square condition. It uses smooth-geometrically-reduced for the fibre S over Spec F, then the vanishing clause of affine-nullstellensatz-vanishing for the finitely generated reduced coordinate algebra and the single regular function chi*(t)-1. The cited node really says vanishing at all F-points implies zero. This proves equality of scheme characters, rather than just equality on points. Both generic off-unit facts are declared in split_report.tool_uses.

Step 6 takes exactly triviality of invertible modules from the new Picard statement with n=2, on the same affine determinant-one scheme. Milne's proof for the new node is a substantive prerequisite, not a clause of this item: GLn has factorial coordinate ring k[x_ij,det^-1] and hence trivial Picard group; the projection and identity section in GLn = SLn x Gm make Pic(SLn) a retract of zero. This proof sketch belongs here only, while its node remains statement-only.

Step 7 expands the torsion-freeness sentence used in Milne 18.19. The only cited input is smooth-geometrically-reduced for H. Nilpotents map to zero on its reduced coordinate algebra; over the algebraically closed field, the reduced finite scheme mu_n is a disjoint union of rational points, and a map from connected H is constant in that union. Its identity value is 1. This remains true when char(F) divides n and is a few-line argument from the cited reducedness and definitions, so it is an elementary step rather than a new lemma node.

Step 8 uses character-picard-isogeny-sequence for exactly its displayed four-term subsegment. I read it and checked that f is between smooth connected affine finite-type groups, with finite diagonalizable kernel; all are quantified hypotheses of this step. Steps 5 and 6 make restriction an isomorphism, not merely a surjection. Multiplicative-character-antiduality states X*(D(M)) = M and the contravariant equivalence, so zero character group forces the actual group scheme kernel trivial, including its infinitesimal part. Step 7 then kills the finite character group. The concluding isomorphism for a faithfully flat map with trivial kernel is written out as unique local lifting and sheaf gluing; no unstated isogeny-degree formula is used.

Step 9 takes exactly the unique lift from the new general theorem. Its field is algebraically closed, q has the required kernel by step 1, S has the hypothesis 'every multiplicative isogeny to it is an isomorphism' by step 8, and E,p are precisely the item assumptions. Its proof source 18.8 pulls back the isogeny and uses 18.6(a); it does not require the pullback group itself to be smooth, a subtlety I checked in the source. This is why a bare claim that the fibre product is smooth was not used.

For edge cases, the Picard prerequisite at n=1 is Spec k; the same GLn retraction works over arbitrary fields and in characteristic dividing n. In the lifting prerequisite H=G=1 gives E=1 when E is smooth connected and finite, and p=id or q=id agrees with the stated uniqueness. For S in characteristic two, mu2 has coordinate algebra F[epsilon]/(epsilon^2), its nontrivial character group is still Z/2, and all centre/antiduality arguments retain it. In step 7, mu_p has trivial reduction but is not assumed trivial before mapping out of a reduced scheme. The t^2-det algebra remains free of rank two regardless of separability. The trivial possible torus in step 4 is allowed. I also checked that GL2 itself is not an admissible E in the item (its scalar kernel has positive dimension), so no unintended infinite-kernel lifting assertion has been added.

I read the actual Mathlib search outputs in search-results.json. For Picard vanishing the closest hits were CommRing.Pic.mk_eq_one and subsingleton_iff; I opened Mathlib/RingTheory/PicardGroup.lean lines 493--530. They assume freeness or characterize it, rather than prove it for SLn's coordinate algebra. For lifting, Scheme.GrpObjAsOverPullback (Mathlib/AlgebraicGeometry/Pullbacks.lean:831) only supplies a group object after base change, not a section or a lift; topological simply connected lifting and abstract abelianization are different assertions. The second semantic phrasings also gave no match. Queries in the nodes are copied exactly from the commands and every output is preserved; no unavailable service has been treated as a negative result.

Against delivery-errors B--E: the two new nodes are self-contained, statement-only, sourced and searched, with one JSON TeX escape layer and explicit definitions or definition dependencies. No cited proof is used in place of its statement, no hidden non-elementary normality or point-to-scheme inference is left uncited, and no node merely renames a clause of the item. All proof steps are below 2000 characters (longest 788). The pre-existing unit/chapter, blueprint and metadata are preserved. No correction of the item's statement was necessary. There was no second worker in this direct-delivery workflow; this section is my own signed source and hypothesis audit as requested.

## Unfinished

The two new statement-only prerequisites join stage 1; this delivery deliberately does not split them. The item proof and citation audit are complete, subject to the mandatory server dry run and independent maintainer review.

## Dry-run repair

The first server preflight flagged the TeX smallmatrix row separator in step 2 as a doubled escape. I rewrote that same calculation using the four named entries and I_2+E_12, I_2+E_21, avoiding row-separator syntax. The mathematics and citations are unchanged. An independent reachability check of every cited prerequisite found no back-dependency on this item.
