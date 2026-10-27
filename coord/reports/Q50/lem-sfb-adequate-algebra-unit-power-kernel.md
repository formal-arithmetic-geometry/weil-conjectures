# Stage-1 delivery: lem-sfb-adequate-algebra-unit-power-kernel

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-algebra-unit-power-kernel.json: item split into three assembly steps; statement retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-ideal-quotient-comparison.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every step citation.

## Attachments

None. Searched the entire live lean/WeilConjectures source for the item tag and adequate/Adequate and adequate-moduli naming; no project declaration states the item. Existing Mathlib global-section and affine-space declarations concern schemes and do not attach the stack statement.

## Wanted literature

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, Algebraic Geometry 1 (2014), 489–531, published PDF, Lemmas 5.2.1 and 5.2.6, pp.507–508, and Proposition 3.3.5 with Remark 3.3.2, pp.497–498, for this item and its new input. There is no local Alper PDF in literature/. I read the primary published PDF online at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf. No download or repository change was made. Following the standing missing-document rule, proof_origin.by is agent; its route is Alper's polynomial-quotient argument.

## Corrections and unfinished work

The item statement has not changed. It was statement-only. The source identifies its algebra unit as an adequate homeomorphism; the delivered split exposes the polynomial presentation and ideal-quotient comparison rather than making a new node that merely restates the algebra unit. In particular it does not confuse arbitrary scalar extension of D with global sections after arbitrary base change.

The single new node is statement-only and joins the later splitting queue. Its proof remains to be formalized. The initially drafted polynomial-global-sections input was removed on final review: existing polynomial-flatness, affine-flatness criterion and flat scalar-sections nodes compute precisely the polynomial case needed. Its genuine searches remain in searches.jsonl; the draft is not delivered.

Intended proof of the ideal-quotient input: follow Alper 5.2.1. Factor the comparison through G/Gamma(I A). Power lifting supplies the adequate inclusion of this quotient into Gamma(A/I A). For the other factor use the Rees algebra of I A, obtained from the polynomial algebra on generators of I, and lift a power of a homogeneous section to show that Gamma(I A)/I G is elementwise nilpotent. Polynomial extensions give universal adequacy; the same ideal-contraction argument on polynomial extensions and their quotients gives the universal kernel assertion. Equivalently Alper 3.3.5 applied after each base change to the adequate homeomorphism of 5.2.1 gives exactly the stated consequence. Neither argument needs a separated absolute diagonal; the qcqs hypotheses suffice for the global-section calculations.

No Lean was written, no compiler or Lake tool run, no shared-repository file or launcher modified, and no agent started.

## Not duplicates

lem-sfb-adequate-ideal-quotient-comparison vs lem-sfb-adequate-algebra-unit-power-kernel: the new node is the separate ideal-contraction theorem Alper 5.2.1 for any adequately affine map, any algebra A and any base ideal I; it does not assume the Stein condition or identify its global ring with the base. The item uses its polynomial case only after constructing that identification.
lem-sfb-adequate-ideal-quotient-comparison vs lem-sfb-adequate-algebra-pushforward: the latter preserves a specified universally adequate sheaf-algebra map under direct image. It does not compare quotient by a base ideal with the global ideal, or assert a universally nil kernel.
lem-sfb-adequate-ideal-quotient-comparison vs lem-sfb-adequate-closed-substack-affinization: the latter constructs adequate moduli and a topological factorization of an arbitrary closed substack. It neither supplies the noninjective quotient comparison nor the positive-power assertion; its dependency route includes this item's parent, so using it here would be circular.
lem-sfb-adequate-ideal-quotient-comparison vs lem-sfb-polynomial-power-lifting-universal-homeomorphism: the existing ring lemma starts from injectivity and polynomial power lifting and yields topology; the new input establishes ideal contraction and universal power lifting for sections, with a possibly nonzero nil kernel.

Whole-DAG keyword/source searches and blueprint_refs searches for adequate, adequacy, adequate homeomorphism, polynomial algebra, polynomial sections, polynomial flat, quotient algebra and ideal contraction found no blueprint node stating the new input. No Stacks tag was invented: these are Alper lemmas. All Mathlib searches recorded on the new node were actually run by msearch.py; their raw result summaries and the persistent searches.jsonl are preserved. Second semantic phrasings returned affine scheme coordinates rather than either stack theorem.

## Review by Q50

I read the complete B–E checklist in delivery-errors.md, the worker brief, stage-1 contract, GOAL, SETUP's three route levels and the item's chapter/unit. I read the published Alper PDF at 5.2.6 and 5.2.1, and the meaning of the latter's adequate-homeomorphism conclusion at 3.3.1–3.3.5 and its base-change remark. These justify the strictly smaller ideal-quotient input rather than an unproved appeal to 5.2.6 itself.

For step 1 I opened def-sfb-adequate-moduli-space: its Stein isomorphism is the one used, and its etale-test condition includes the identity affine test and all algebras. The opened affine-target criterion converts exactly that global lifting condition to adequate affineness with the required qcqs hypotheses. The opened polynomial-ring definition supplies evaluation and its universal property. Choosing a variable for every c makes surjectivity immediate, even when C is not finitely generated.

For step 2 I opened lem-sfb-adequately-affine-affine-target-base-change: its target is affine and it permits the arbitrary map Spec P to Spec R with no diagonal condition. I then opened lem-nagata-polynomial-projection-flat and lem-weil-pbc-flat-morphism-affine-criterion: together they give flatness of the actual ring map R to P for any set of variables. Both are existing Mathlib leaves. I opened lem-sfb-stack-flat-scalar-sections, which applies to the qcqs map X to Spec R, the flat map R to P and O_X. Its canonical map identifies Gamma(Z,O_Z) with P as a P-algebra and sends 1 tensor s to the structural section. The structure-sheaf definition identifies the restriction of O_X with O_Z. Thus no new polynomial node is necessary; removing that draft corrected an elementary/duplicate-input fault before pushing.

For step 3 I checked the new quotient node with f adequately affine, algebra O_Z, base P, ideal I, and G=P. It states the nil-kernel and power properties after every algebra extension, exactly what is needed. I reread the relative-spectrum node's affine-test gluing, arbitrary base-change and global-section clauses for both the closed quotient over Z and the pulled-back algebra over X. The opened algebra tensor pushout node gives the universal property used to impose I: maps out of either chart algebra are precisely compatible maps from A and C, so the canonical isomorphism is forced. Tracking T_c proves that the comparison is u and tensoring it is exactly u_C'. This removes any hidden nonflat base-change theorem. This tensor lemma is a generic off-unit tool declared in split_report.tool_uses; no geometric route is replaced.

Edge cases checked: C=R and a polynomial C give an isomorphism; C=0 gives the zero map of zero rings; the arbitrary zero C'-algebra is harmless. Nonreduced quotients are included: the comparison's kernel is only elementwise nil, not asserted zero or nilpotent with one uniform exponent. Arbitrarily many variables and non-finitely-generated ideals are allowed in the quotient input and the polynomial presentation. If I=0 the quotient lemma is the identity; if I=P both source and quotient algebra are zero. The polynomial case also permits the empty variable set and zero rings. No uniform power bound is asserted. Alper's examples 5.2.3–5.2.5 warn precisely against strengthening the map to an isomorphism or making the power uniform.

The new statement introduces its objects and cites the notions used. It contains no proof or proof dependencies. The item's proof dependencies are exactly the union of its step uses. The three assembly steps are 468, 680 and 894 characters, so no long step hides a lemma. The report retains the future proof ideas separately from statement-only nodes. The review found no statement dispute and no route change.
