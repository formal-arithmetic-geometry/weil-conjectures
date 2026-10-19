# Worker report: lem-trf-log-chart-face-tor-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-log-chart-face-tor-comparison.json`: statement, split into eight proof steps; no exact Mathlib match.
- `citations.json`: verbatim statement quotations for every use in every step.
- `report.md`: this report. No new DAG nodes, no new Mathlib leaves, no unit record changes.

## Attachments

None. Searched the project under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag and chart/face/Tor notions. No project declaration proves every clause of this item. The upstream master is reference material, not evidence of a finished proof. No compiler or Lake was run.

## WANTED

None. The ILO volume and the Stacks source used below are present locally.

## Faults and corrections

The imported node had no proof. I wrote the algebraic comparison explicitly; it is not claimed to be a verbatim theorem of ILO. ILO VI 3.7(a) supplies the chart/splitting context; VIII proof of 3.4.3 supplies the monomial ideal/Tor application. The proof origin is therefore `agent`.

STATEMENT-DISPUTED: the unit twist needs a coefficient ring. Read as an automorphism of the adjacent integer monoid ring, it is ill-typed: take A=C[[t]], P=N, alpha(1)=it and b(1)=t. This A is strictly henselian; Q=N and u(1)=i, so the proposed image iz of z is not even an element of Z[z]. The faithful interpretation, now explicit in the statement, is the automorphism of A[Q] after extending coefficients to A. No hypothesis or Tor conclusion has changed. Step 7 checks that this extension still computes the relevant first-Tor kernels without requiring A to be Z-flat.

The reference for “strictly henselian” was a strict-henselization limit node that does not define that term. Replaced it with `def-weil-pbc-henselian-terminology`, whose statement defines it. The given sharp chart remains a hypothesis: `lem-trf-log-regular-sharp-chart` is not applied to assert existence under missing log-regularity hypotheses.

## Unfinished work

None at stage 1. All non-elementary inputs already have nodes. No Lean or stage-2/3 work was attempted.

## Searches and duplicate audit

Whole-DAG searches by face localization, sharp chart, unit twist, monomial Tor and Stacks 00M6 found the existing face-sharpening and ideal-kernel nodes. Blueprint searches for “face localization splitting unit twist Tor monoid chart”, “change of rings Tor monoid algebra face”, “monoid chart”, and “unit twist” found no second statement of this comparison. The nearest ancestor is `lem-trf-local-term-locality`; its ancestry and precise reduction place are preserved in `blueprint.from`.

The actual Q32 Mathlib queries are logged in `searches.jsonl`; the item retains its inherited Q64 audit and adds the useful Q32 queries verbatim. LeanFinder was tried both for a monoid-chart comparison and a general change of rings. LeanSearch returned generic localization/tensor statements, not the comparison. Loogle with the qualified name string found the seven definitions/naturality projections for CategoryTheory.Tor, whose source was read. The corrected grep rooted at CategoryTheory/Monoidal found `Mathlib/CategoryTheory/Monoidal/Tor.lean`, lines 12--42, and its definitions were read; the monoid-algebra/localization grep found no hit. Earlier invalid type queries and greps with the redundant Mathlib prefix were not used as evidence of absence. No recorded Q32 query is invented and no failed service is represented as a successful negative answer.

## Not duplicates

No new nodes. In particular the generic Tor kernel/naturality theorem and symmetry are reused, and the three elementary inverse tensor maps are steps, not additional lemmas restating clauses of the item.

## Review by Q32

I read ILO Expose VI 1.1--1.2 (printed p. 69), 1.6 (p. 70), 3.7(a) (p. 75), VIII 3.1.1--3.1.5 (pp. 98--99), and the proof of 3.4.3 (p. 110). These give the log/chart setting and the monomial ideal application. I also read Stacks algebra.tex at the labels for Tags 00M6 (remark-Tor-ring-mod-ideal), 00M3 (lemma-tor-left-right), and the tensor construction 00CX. The algebra below expands the comparison; the source does not independently assert the entire expanded statement. There are no new-node sources to audit.

1. `lem-trf-fs-face-sharpening` states that face localization has units F^gp and that its quotient is sharp with equality determined in the quotient group. Here F really is a face because a product is a unit iff both factors are units. I do not take a splitting from this node: its statement does not give one. The given monoid section produces the splitting and inverse by the displayed subtraction formula. This works even if P has torsion units.
2. `def-trf-fs-log-blowup` explicitly states the chart pushout and its defining congruence. I use only that definition, not its locally Noetherian/log-regular applications. Inverting F does nothing in the pushout because its images are already units. For the sharp chart its preimage of units is {0}, so its pushout is Q direct-sum A-units. The same characteristic identification places the other chart at (q,u(q)). The formula for multiplication proves u is a homomorphism, including its identity value. No cancellation in the ring A is used.
3. `lem-weil-pbc-tor-symmetry` states the natural interchange of the two arguments. Part (a) of `lem-weil-pbc-tor-ideal-kernel-naturality` gives exactly the injective connecting map with image the multiplication kernel; part (b) states the required semilinear ring-change compatibility. The rings here are commutative and all indicated ideals and modules have exactly the required types. These are generic off-unit tools declared in split_report.tool_uses; they do not replace the alteration/logarithmic route.
4. No external theorem is asserted. The ideal image is an ideal since P maps onto Q; its inverse image is H_F because H_F is stable under both signs of G. This proves the product description of the localized ideal rather than assuming it.
5. `def-weil-pbc-module-tensor-product` states both generation by pure tensors and the bilinearity relations. Those relations prove the localization map and its proposed inverse descend: equality of fractions is h+f'=h'+f, and their images have the common denominator alpha(f)alpha(f'). Balancing by p-f' is checked with its actual scalar. Every denominator lies in F and hence has invertible image. Multiplication commutes by the written formula.
6. The same tensor definition justifies the group-factor map. I checked balancing by a general monomial s(p)+g', its scalar c(p)v(g'), both composites, and its multiplication target. The inverse uses the given section, not a noncanonical assertion of flatness.
7. The same tensor definition justifies the twist. Its direction is important: from c to b the factor is u(q), not u(q)^-1, because c(q)=u(q)b(q). The relation for q+p and both inverses are written. On A[Q] the twist is an automorphism since u(q) is a unit, and it preserves the ideal with basis H_x. The explicit coefficient-extension inverses show that no hidden Z-flatness hypothesis enters.
8. The two cited Tor statements are the same statements used in step 3. Restricting an invertible map commuting with multiplication is elementary, and identifies the maps with ring-change maps by part (b). For splitting the ring inclusion is in the reverse direction, so its Tor map is inverted. The coefficient-extension maps also induce kernel isomorphisms; the unit twist therefore has the asserted meaning. Naturality is for fixed chart choices and compatible coefficient maps, as the tensor formulas show. No assertion of choice independence is made.

I checked the empty ideal (all ideal tensors and Tor groups are zero), H=P (quotients and Tor groups are zero), and an ideal meeting F (its image is the full sharp ideal; multiplication is an isomorphism after localizing). If P is a group, F=P and Q=0, and the same group-factor inverse proves zero on both Tor sides. For P=N, F={0}, and a unit multiple of a parameter, the twist is multiplication by the correct power of that unit. These checks need neither log regularity nor Z-flatness. The strict henselian hypothesis is retained, although this algebraic comparison uses only the chosen charts and their units.

Against delivery-errors B--E: the item introduces every object; no unsplit child carries a disguised proof; no new or duplicate node is created; the current blueprint ancestry and all import metadata are preserved. Each cited statement was opened and its used portion quoted verbatim in citations.json. I checked that no step takes a construction from a cited proof instead of its statement, and no parent monomial-Tor theorem is cited back into its own dependency. The maps, inverse maps, balancing equations and connecting naturality replace any appeal to an unspecified “transport” or “clear denominators.” All eight steps are shorter than 2000 characters. The substantive corrections during review were to specify the coefficient ring for the twist, use the actual henselian definition, and avoid applying log-regular chart existence.
