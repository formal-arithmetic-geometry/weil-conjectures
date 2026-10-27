# Stage-1 delivery: lem-sfb-dvr-algebraic-normalization-structure

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-algebraic-normalization-structure.json: statement split; Mathlib verdict no complete match.
- citations.json: verbatim statements for every step/dependency pair.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Every needed tool already has a node; elementary finite-product and fraction calculations stay as proof steps.

## Attachments

None. Project searches for the exact blueprint tag, algebraic normalization, DVR normalization and related RingTheory declarations found no theorem asserting all clauses under these hypotheses. The normalized-compositum theorem concerns finite normalizations with extra ramification assumptions and cannot attach this item.

## WANTED

None.

## Issues found

The item's mathematical statement is unchanged. The reference to 09EM assertions (1)-(4) includes an unnecessary henselian clause (4); the proof only needs (1)-(3). No henselian, excellent, Nagata, separable or finite-module hypothesis was inserted. The latest blueprint direct-image proof (3) no longer contains this old supporting algebra route. The existing blueprint.from record honestly records that historical chain and its null ancestor; blueprint_refs ancestor confirms None. The item is not the unit's key statement, so no unit realized fields were edited.

An auxiliary search located Mathlib's dimension-zero Artinian criterion, but no node was needed: the existing reduced Noetherian total-fraction decomposition supplies the finite field product directly. Those real exploratory searches remain in searches.jsonl. Earlier inherited searches are preserved; current item searches were run with msearch and their real summaries appended.

## Unfinished

None at stage 1. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes were created. Reused the existing 09IG, Krull-Akizuki consequences, semilocal normalization, finite-minimal-prime, residue-field, flatness and integral-map nodes. Whole-DAG statement/tag searches and blueprint searches for 09IH, normalization, algebraic normalization, semilocal, Krull and 00KH were read before choosing this reuse.

## Review by Q94

I read more-algebra.tex, remark-construction (09EM) and lemma-big-extension-is-ok (09IH), and algebra.tex, lemma-integral-closure-Dedekind (09IG), lemma-finite-extension-residue-fields-dimension-1 (031F), Noetherian permanence (00FN), and their stated proof route. This delivery expands the omitted spectrum-surjectivity and semilocality details instead of treating 09IH as a black box. I opened the statement of every cited node; citations.json copies exactly those statements, not facts taken from their proofs.


Step 1: Normality and fraction field come from the arbitrary algebraic integral-closure statement; 09IG is applied only in the finite case. Integral dimension and maximal contraction apply to R/A. The primes over the nonzero uniformizer are all maximal, so finite minimal primes over that ideal proves semilocality without assuming finite normalization.
Cited statements read: lem-weil-pbc-integral-closure-algebraic-extension-normal, lem-sc-integral-closure-dedekind-surjective-fibres, lem-weil-pbc-integral-injective-dimension-equal, lem-weil-pbc-integral-maximal-contracts-maximal, lem-weil-pbc-integral-prime-over-maximal-maximal, lem-sc-finite-minimal-primes-over-ideal.

Step 2: The flatness node is for torsion-free modules over a PID, matching both B and R as subrings of fields. The local flat-map theorem applies to A to B. Integral base change is applied to A to R. The two tensor injections and uniformizer regularity use the actual injection-preserving definition of flatness, which is explicitly cited.
Cited statements read: lem-weil-pbc-pid-torsion-free-module-flat, lem-weil-pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-base-change, lem-weil-pbc-integral-base-change, def-weil-pbc-flat-ring-map, def-sc-discrete-valuation-ring.

Step 3: The localization-tensor statement gives precisely the simultaneous localization of the two factors. The denominator and nilpotence arguments are written out. This is a routine fraction calculation, marked elementary; it does not assume arbitrary algebraic tensor products have finitely many factors.
Cited statements read: lem-weil-pbc-localization-tensor-product.

Step 4: The field-extension base-change and faithful-flat injectivity statements prove the tensor algebra is nonzero. Integral base change applies to the algebraic (therefore integral) extension P/K. The integral-prime-over-maximal statement gives dimension zero, without claiming Noetherianity yet.
Cited statements read: lem-weil-pbc-field-extension-base-change-faithfully-flat, lem-weil-pbc-faithfully-flat-universally-injective, lem-weil-pbc-integral-base-change, lem-weil-pbc-integral-prime-over-maximal-maximal.

Step 5: The finite-dimensional Artinian node applies only when P/K is finite; its reduced decomposition provides the finite product. The 09IG node applies factor by factor, and finite fibres plus maximal contraction gives semilocality. Coordinatewise integrality is proved by multiplying monic polynomials, rather than misusing a product-base statement for the diagonal map.
Cited statements read: lem-weil-pbc-finite-dim-algebra-artinian, lem-sfb-reduced-artinian-residue-product, lem-sc-integral-closure-dedekind-surjective-fibres, lem-weil-pbc-integral-maximal-contracts-maximal.

Step 6: The finite-type Noetherian and localization nodes give exactly the Noetherian property of D. Integral dimension applies because B injects into D by step 2. All maximal ideals contain pi and every prime containing pi is maximal. Finite minimal primes over (pi) therefore gives semilocality, with no Jacobson or excellence assumption.
Cited statements read: lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian, lem-weil-pbc-integral-injective-dimension-equal, lem-weil-pbc-integral-maximal-contracts-maximal, lem-weil-pbc-integral-prime-over-maximal-maximal, lem-sc-finite-minimal-primes-over-ideal.

Step 7: The total-fraction decomposition is used exactly as its statement gives it, after checking reducedness and Noetherianity. Nonzerodivisors are units because maximal primes are minimal. The minimal-prime avoidance and integral incomparability statements justify matching these fields to D components; no finite degree over L is asserted here.
Cited statements read: lem-weil-pbc-localization-noetherian, lem-weil-pbc-reduced-noetherian-total-ring-fractions, lem-pc-minimal-prime-avoids-nonzerodivisor, lem-weil-pbc-integral-incomparability.

Step 8: The normalizations here are in each component own fraction field, so the existing semilocal normalization node applies, unlike the finite-field-extension theorem applied directly to infinite P. Integral transitivity identifies the two integral closures. Finite-product ideal decomposition is elementary and explicitly explained.
Cited statements read: lem-weil-pbc-integral-injective-dimension-equal, lem-sc-semilocal-dim-one-normalization, lem-weil-pbc-integral-transitive.

Step 9: Lying over is applied to the injective integral map G to C, not to D to C before removing nilpotents. The kernel equality was checked in step 3. Faithful flatness gives surjectivity from D to R. Primes chosen over a maximal ideal contain pi, so the cited integral maximality theorem really makes their lifts maximal.
Cited statements read: lem-weil-pbc-integral-injective-lying-over, lem-weil-pbc-faithfully-flat-surjective-spectrum, lem-weil-pbc-integral-prime-over-maximal-maximal.

Step 10: Maximal contraction is applied to B to C, which is integral, not to R to C (which need not be integral). Containing pi then proves maximality of the contraction in R. The Dedekind-localization node has all its Noetherian, normal and dimension-one hypotheses established. The induced local map and its denominators are explicit.
Cited statements read: lem-weil-pbc-integral-maximal-contracts-maximal, lem-weil-pbc-integral-prime-over-maximal-maximal, lem-sc-dedekind-localization-dvr.

Step 11: The residue conclusion of 09IG is stated in the cited node and applies in case (a), without a separability hypothesis.
Cited statements read: lem-sc-integral-closure-dedekind-surjective-fibres.

Step 12: The finite-residue theorem is applied to the one-dimensional Noetherian local domain obtained by localizing T_i, with identical fraction fields (degree one), so its hypotheses are checked. The other residue statement is applied to the finite type algebra U tensor R before localization; residue fields survive the quotient and localization. The finite-generation tower is then an elementary union of generators.
Cited statements read: lem-weil-pbc-integral-maximal-contracts-maximal, lem-weil-pbc-localization-noetherian, lem-weil-pbc-dim-one-residue-field-extensions-finite, lem-weil-pbc-finite-type-residue-field-extension-finitely-generated.


Small cases checked: P=K gives E=L, R=A and C=B; the residue extension in (b) is exactly the essentially finite type residue extension. A=B reduces to algebraic DVR normalization and allows an infinite unramified tower with Noetherian normalization; nothing in the proof incorrectly makes P/K finite. Finite purely inseparable extensions may give nilpotents in the tensor algebra, which are removed before the product decomposition; finite separable split tensor algebras give several genuine factors. Non-Nagata DVRs are allowed: 09IG gives Noetherian normalization, not a finite module. In case (b), the Noetherian hypothesis on R is used before D or E is claimed Noetherian. Each factor remains dimension one because its integral injection from B has lying over; no field is incorrectly called a DVR.

I checked delivery-errors B--E: all mathematical notions of the unchanged statement have its existing definition dependencies or inline definitions; there are no new statement-only nodes to audit, no restatement nodes, no invented search records, and no whole-item black box. Every non-elementary step has statement-level citations and the sources name Stacks tags and labels. All non-elementary steps are under 2000 characters, so no long step hides an extra lemma. Generic off-unit algebra tools are declared in split_report.tool_uses; they implement the source argument and do not replace a unit route. The statement was not disputed or weakened.
