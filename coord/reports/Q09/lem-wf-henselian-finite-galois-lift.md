# Stage-1 report: lem-wf-henselian-finite-galois-lift

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-wf-henselian-finite-galois-lift.json`: statement, split in seven steps; no exact Mathlib match for the entire henselian residue-lift theorem.
- `dag/nodes/sec-purity-real-sheaves/lem-wf-finite-field-action-fixed-degree.json`: statement, Mathlib leaf; finite faithful field action gives a finite Galois extension over its fixed subfield with degree equal to the group order.
- `citations.json`: all eleven step/node occurrences, with their full verbatim statement text.
- `searches.jsonl`: actual search-command records, including exploration of the field-cardinality criterion and the ultimately used finite-action theorem.

## Attachments

None. Searched `WeilConjectures/` in the read-only slopmaster2 source for the exact blueprint tag and henselian/Galois terminology, then the RingTheory and Mathlib/FieldTheory areas for finite etale and fixed-field material. The henselian finite-etale comparison modules concern categorical lifting; none states all the normal-domain, fraction-field, degree, integral-closure and automorphism clauses of this item. The generic fixed-field facts used for the new leaf are Mathlib declarations, not project attachments. No upstream sorry declaration is treated as a proof.

## WANTED

None. All source text needed here is present in the shared literature checkout.

## Corrections and scope

The statement is unchanged; no STATEMENT-DISPUTED correction is needed. The imported node had no proof. Its source, Stacks 0BSW (`pione.tex`, `lemma-identify-inertia`, paragraph starting with a finite Galois residue extension), explicitly omits the fraction-field/degree calculation. The delivery writes it out and marks the resulting expansion as agent-written. It does not cite the inertia theorem as a black box to prove its own finite-stage input.

The item is below the fixed boundary unit. The current blueprint's `lem-wf-boundary-stalk-invariants.proof.md`, second paragraph, uses the fraction field of the strict henselization and automorphisms over the henselization; this split supplies its finite-stage algebra through the existing parent. No chapter or unit record is edited. The two off-unit statements about normality and henselian full faithfulness are declared in `split_report.tool_uses` as generic algebra tools. The remaining outside inputs are definitions or Mathlib leaves.

The local pinned Mathlib lacks `IsGalois.of_card_aut_eq_finrank`, although the live search services return it; source inspection also finds only a stale `tfae` mention in that file's introduction. I therefore did not claim that remote hit as a local Mathlib leaf. Instead the delivered proof uses the locally verified finite-action theorem and the existing degree-multiplicativity leaf. Its source and exact match are independent of that version mismatch.

## Unfinished work

None for this one-level stage-1 split. Existing cited open nodes remain their owners' tasks. No Lean was written or compiled.

## Not duplicates

lem-wf-finite-field-action-fixed-degree vs lem-weil-pbc-distinct-linear-factors-separable: the shared 09I3 tag is incidental to the latter's use in a proof; that node states separability of a polynomial and its divisors, not the fixed-field degree or Galois property of an arbitrary finite faithful action.

lem-wf-finite-field-action-fixed-degree vs lem-weil-pbc-normal-extension-purely-inseparable-then-galois: that node assumes an already normal algebraic extension and studies the full automorphism group's fixed field, including a purely inseparable lower extension; it gives no finite-action degree equality. Our action may be any finite faithful subgroup on an arbitrary field, with no prior normal-extension hypothesis.

lem-wf-finite-field-action-fixed-degree vs lem-weil-pbc-normal-extension-fixed-field-separable-normal: that node assumes an already normal algebraic extension and gives separability/normality over its full automorphism fixed field; it has neither an arbitrary finite faithful action nor the degree equality used here.

lem-wf-finite-field-action-fixed-degree vs lem-weil-pbc-finite-galois-fixed-field: the existing node starts with a finite Galois extension and identifies its full group order and fixed field; the new leaf starts with a finite faithful action and proves Galoisness and degree over its fixed field. The existing direction is used separately for the given residue extension.

lem-wf-finite-field-action-fixed-degree vs lem-wf-henselian-finite-galois-lift: the new leaf has no henselian ring, etale algebra, residue extension, integral closure or generic/residue comparison. It is a general field-theory ingredient, not the item or a clause renamed.

## Review by Q09

I read Stacks `pione.tex`, Tag 0BSW (`lemma-identify-inertia`), including both the invocation of finite-etale henselian equivalence and the omitted fraction-field calculation. I read `algebra.tex`, Tag 04GK (`lemma-henselian-cat-finite-etale`), Tag 033C (`lemma-normal-goes-up`), Tag 00NZ (`lemma-finite-flat-local`), Tag 00GK (`lemma-finite-is-integral`), and Tag 00GY (`lemma-localize-normal-domain`); and `fields.tex`, Tag 09I3 (`lemma-galois-over-fixed-field`), Tag 09I1 (`lemma-finite-Galois`), and Tag 09G9 (`lemma-multiplicativity-degrees`). I compared the current blueprint boundary proof and its unit/chapter records; the generic algebra expansion stays below that route.

Step 1 uses the exact statements of `lem-weil-pbc-localization-normal-domain`, `def-weil-pbc-normal-ring`, and `lem-weil-pbc-etale-over-normal-ring-normal`: first the localizations of H satisfy the definition of a normal ring, then normality ascends along the actual etale map, and B's locality identifies B with its maximal-ideal localization. This avoids assuming that an arbitrary normal ring is a domain. No Noetherian hypothesis is introduced: 033C and its cited node are valid without it.

Step 2 uses precisely the flatness conclusion of `lem-weil-pbc-etale-algebra-flat` and freeness conclusion of `lem-weil-pbc-finite-flat-local-free`. H is local and B is finite, so both hypotheses of the latter hold. A finite basis exists because a free finitely generated module has finite rank. Reducing the coordinate isomorphism identifies that rank with the given residue degree. The nonzero field e forces positive rank, and the coordinate argument proves H-injectivity without a hidden faithful-flatness theorem.

Step 3 is the elementary calculation from that basis. All denominators from H remain nonzero by step 2. Clearing a common denominator proves linear independence, while coordinate expansions prove spanning. Multiplication by a nonzero element of the resulting finite-dimensional domain has independent images of a basis, hence is onto; this supplies an inverse, identifies the localization with the entire fraction field, and gives the degree. The tensor identification is specified in both directions and checked on pure tensors, rather than asserted as an unexplained comparison. This is a few finite-basis calculations, not a separate geometric or descent lemma.

Step 4 uses the full statement of `lem-weil-pbc-finite-algebra-is-integral` for one inclusion. For the reverse inclusion the same monic H-polynomial is a monic B-polynomial and the normal-domain clause of `def-weil-pbc-normal-ring` applies in Frac(B). No finiteness of the normalization theorem is needed.

Step 5 is elementary after step 4: it writes the fraction formula, its inverse, the monic-polynomial argument preserving B, and the two inverse maps. The restriction really has target B because integral closure has already been proved. The formulas fix K and respect composition, so they produce group isomorphisms with the maps requested in the item.

Step 6 uses `lem-weil-pbc-henselian-finite-etale-map-bijective`, whose statement gives a bijection on all algebra homomorphisms, not merely an equivalence up to isomorphism of objects. Here S=T=B are finite etale and R=H is henselian local. I wrote out why lifting the inverse and then using uniqueness makes the lift an automorphism; reduction is the specified reduction modulo mB, identified with e by the supplied identification.

Step 7 uses the exact order/finiteness clause of `lem-weil-pbc-finite-galois-fixed-field` for the residue extension, whose Galois hypothesis is given, not for the generic extension being proved. The extended G action is faithful by restriction to B and fixes K, so the new field-action leaf applies to E. I checked its three clauses in the pinned Mathlib: the finite-dimensional instance in `FieldTheory/Fixed.lean:296`, `FixedPoints.finrank_eq_card` at line 346, and `IsGalois.of_fixed_field` in `FieldTheory/Galois/Basic.lean:94`. The input injective homomorphism is exactly a faithful action. The fixed-field extension F/K is finite by linear independence inside the already finite-dimensional E; thus both finiteness hypotheses of `lem-weil-pbc-field-degree-multiplicativity` hold. Positive n permits cancellation, and a degree-one extension equals its base by the basis {1}. This supplies generic Galoisness without assuming it prematurely.

Before creating the leaf I searched the whole DAG for 09I3, fixed fields, faithful finite field actions and candidate declaration names, and ran blueprint searches for 09I3, fixed field, faithful actions, automorphisms and finite Galois. The three existing tag matches have different statements as recorded above. The leaf is self-contained with field operations and action specified; it has only a statement, no proof or proof dependencies. Its four required searches are the exact commands recorded in searches.jsonl; all returned successfully. I read their hits and checked the local source, including the distinction between local and live-service versions.

Small cases checked: H a field reduces the item to the given finite Galois field extension; e=kappa forces rank and generic degree one; the zero algebra cannot satisfy the residue-field identification. H may be non-Noetherian, imperfect in positive characteristic, or of dimension greater than one, and no step uses completeness, a uniformizer, a finite residue field, or a DVR hypothesis. The new leaf holds for a trivial group (fixed field is L, degree one); the faithful hypothesis is necessary for the stated degree, as a nontrivial group acting trivially would violate it. Every non-elementary step cites statements that say precisely what it uses; citations.json copies those statements verbatim. Every proof step is below 2000 characters, and I found no hidden source-called-standard lemma. This review corrected the initial plan to use the unavailable local automorphism-cardinality criterion and replaced it by the locally available finite-action degree argument.
