## Files written

- `dag/nodes/sec-trace-formula/lem-trf-specialization-zero-section.json`: item, split, 15 proof steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-nearby-cycle-finiteness-exchange.json`: existing dependency from the repository.
- `dag/nodes/sec-trace-formula/lem-trf-dnc-generic-zero-section-vanishing.json`: existing dependency from the repository.
- `dag/nodes/sec-trace-formula/lem-trf-constant-family-defect-finite-projection.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-support-defect-conservativity.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-proper-specialization-borel-moore-compatibility.json`: new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quote for every use in every item step. Full statements are quoted to retain all domain restrictions.
- `searches.jsonl`: actual search-command log. The new lemmas each have LeanFinder, Loogle, grep, LeanSearch, and a second semantic phrasing; all services responded.

## Attachments

None. Searched the entire project `WeilConjectures/` in slopmaster2 for the item's blueprint tag and nearby-cycle, specialization and zero-section notions, and inspected the smooth-purity deformation candidates. Those concern the deformation of a smooth section's dualizing invariant, rather than arbitrary closed-subscheme Verdier specialization. No declaration states every clause of this item. Upstream master is reference material only.

## Wanted sources

None. The local Varshavsky PDF contains the source and its detailed proof, including §3 explicitly devoted to this zero-section theorem. No SGA source is used.

## What was wrong and what changed

Before the first delivery, the imported statement had no proof. Its first clause is Varshavsky Proposition 1.4.2 and equation (1.8), its constant-family assertions are Examples 1.3.3(a)--(b), and its final clause is the nilpotent-invariance argument used in Theorem 2.1.3(b). The statement is retained exactly; there is no STATEMENT-DISPUTED correction.

My initial draft quoted Proposition 1.4.2 instead of giving its argument, and incorrectly tried to apply the finite-type-over-k stability package to nearby cycles over a trait. Both gaps are repaired. The item now first proves constant-family constancy independently using Remark 3.2.5, then proves the zero-section theorem by the reduction and affine-hyperplane induction in §3.2.1--3.2.4. The two lower lemmas from the first delivery, now present in the repository, expose exactly the missing trait formalism and the genuinely smaller generic-point vanishing step. Neither lemma is a relabelling of the item or an entire clause: one is a general functor/exchange theorem without a zero-section conclusion, and the other only proves generic vanishing on a normal principal pair for complexes zero on the divisor. The item still carries the localization, blowup, hyperplane, and dimension induction needed to obtain the global theorem.

The finite-support projection is written explicitly using a nonzero vanishing polynomial, a direction avoiding its top homogeneous part, and the resulting monic equation. This supplies both finiteness on the support and absence of its projective closure at infinity. In particular the final conservativity argument is not justified by properness alone. The finite-stalk theorem makes it exact and conservative on the specified finite support. Both dimension inductions use bounded constructible etale complexes; `thm-dg-finite-type-constructibility` supplies their direct-image domain, whereas finite Tor amplitude is checked separately on the original item using the new nearby-cycle theorem and the comparison-amplitude lemma.

## Not duplicates

- `lem-trf-nearby-cycle-finiteness-exchange` vs `thm-sf-ctf-stability`: the latter concerns finite-type k-morphisms, not geometric nearby cycles from a geometric generic fibre over D. The same distinction separates it from `prop-functor-package`.
- `lem-trf-nearby-cycle-finiteness-exchange` vs `lem-trf-trace-specialization`: the latter is an equality of trace classes, not a preservation/exchange result for nearby cycles.
- `lem-trf-dnc-generic-zero-section-vanishing` vs `lem-trf-specialization-zero-section`: the new lemma is only the generic-point vanishing of Claim 3.2.3 under normality, a principal divisor, and zero restriction. It does not give the comparison on all of Z, any arbitrary-pair reduction, the constant-family unit, or the Borel--Moore identity.
- `lem-trf-dnc-generic-zero-section-vanishing` vs `thm-pur-dnc-invariance` / `sk-thm-dnc`: the purity statements concern smooth sections and their relative dualizing invariant. This lemma concerns arbitrary bounded constructible etale input zero on a principal divisor and its nearby-cycle generic stalks.

Whole-DAG and whole-blueprint searches for nearby cycles, generic vanishing, normal-cone specialization, and principal divisors found no existing statement of either new lemma. The source citations are to Varshavsky, not to reused Stacks tags. The supporting Stacks/Mathlib facts already have DAG nodes and are cited directly.

Additional duplicate review for this repair:

lem-trf-constant-family-defect-finite-projection vs lem-trf-specialization-zero-section: the new statement is independent affine geometry, not any specialization conclusion or clause of the item.
lem-trf-constant-family-defect-finite-projection vs lem-sc-p1-polynomial-projection-chart-iso: the latter identifies standard projective-line charts; it does not choose a linear projection finite on an arbitrary closed support or exclude infinity for its closure.
lem-trf-finite-support-defect-conservativity vs lem-weil-pbc-finite-stalk-formula-restriction: the latter gives the underived stalk product for finite morphisms; the new statement is detection for a bounded complex under a possibly nonfinite h with a specified finite closed support.
lem-trf-finite-support-defect-conservativity vs det-curve-finite-support-acyclic: the curve statement only treats finite sets of closed points over an algebraically closed field, not finite support over an arbitrary positive-dimensional base.
lem-trf-finite-support-defect-conservativity vs sk-lem-curve-finite-support: the latter states underived exactness and curve point-support cohomology, not derived detection on a finite-over-base closed support for a general h.
lem-trf-proper-specialization-borel-moore-compatibility vs lem-trf-nearby-cycle-finiteness-exchange: the latter gives functor exchanges and unit/counit compatibility; the new statement identifies the resulting proper-pushforward and specialization composites on dualizing Hom modules.
lem-trf-proper-specialization-borel-moore-compatibility vs lem-trf-specialization-cohomological-comparison: the latter supplies specialization data on fixed correspondence diagrams and refinement, not the Borel--Moore proper-pushforward equality for arbitrary proper lifted morphisms.
lem-trf-proper-specialization-borel-moore-compatibility vs lem-trf-trace-specialization: trace-class equality for a correspondence does not assert the proper-pushforward compatibility of arbitrary Borel--Moore sections.
lem-trf-proper-specialization-borel-moore-compatibility vs lem-trf-specialization-zero-section: the new statement assumes a proper lifted morphism and only compares two composites; it proves no constant-family identity, nilpotent isomorphism or zero-section result.

## Review by Q13

I read the local Varshavsky PDF at §§1.3.1(e), 1.3.2(b)--(c), Examples 1.3.3(a)--(b), Notation 1.4.1 and Proposition 1.4.2, Lemma 3.2.1, §3.2.2, Claim 3.2.3, §3.2.4, Remark 3.2.5, and the reduction paragraph of Theorem 2.1.3(b). The returned item statement and its Lean record are unchanged against the current shared repository. The unit is still `sk-i-curve-zero`, with nearest blueprint ancestor `lem-trf-local-term-locality`: this split supplies its normal-cone argument, not a different proof of the unit. No SGA route or source is used.

Step 1 uses the actual constructible-origin statement, both directions of comparison Tor amplitude, the Rees geometry, the nearby-cycle finiteness theorem and the specialization definition. The trait morphism is separated finite type; the coefficient ring is finite with ell invertible. Finite Tor amplitude is checked separately, not inferred from constructibility. The nearby-cycle dependency is already split in the current repository and is not delivered again.

Step 2 uses the nearby-cycle theorem's exactness, proper/smooth exchange and unit compatibility to form the constant-family defect. The definition of bounded constructibility gives the dense-open lisse cohomology. Exact/conservative geometric stalks detect the vanishing after etale trivialization. This argument precedes the zero-section comparison, avoiding circularity through (1.8).

Step 3 uses smooth exchange for locality, proper exchange for a closed immersion, exact closed pushforward from open-closed recollement and its invertible closed counit to reflect vanishing. The affine embedding is of finite-type affine k-schemes. Step 4 uses the new linear-projection statement on the proper reduced closed support Y; k is algebraically closed and therefore infinite, and n>0 is explicit. I changed this new node from an ill-scoped statement about a defect over an arbitrary infinite field to the independent geometric lemma actually used by both inductions.

Step 5 uses properness of the relative projective line, bounded constructibility under finite-type direct image, and proper nearby-cycle exchange. The induction applies to all bounded constructible inputs, not just finite-Tor inputs, so truncation remains available. Step 6 uses smooth exchange for the affine chart, the projection lemma for the closed finite support including the infinity section, and the new finite-support conservativity statement with h equal to the compactified projection. The support is closed: the closure of Y misses infinity, and the whole infinity section is closed and finite over the base. I repaired the retained conservativity statement, which had put K on S and referred to an undefined corresponding complex on W: it now explicitly has K on W, a closed i:V into W, and hi finite. Its source is the exact support argument of §3.2.4. Its future proof is localization K = i_*i^*K followed by the finite stalk formula, exactness, and conservativity; the new node has no proof or proof sketch in its statement.

Step 7 uses only the statements of Rees functorial geometry, flat tensor exactness, proper/smooth permanence, nearby-cycle exchange and special-fibre base change. The closed comparison to the Rees base change becomes an isomorphism for a flat map by the written subalgebra calculation. Step 8 uses localization, properness of a closed immersion and the constant-family case (now Step 6), including the empty-centre case. Step 9 uses the cited proper blowup, complement-isomorphism and principalization statements. Noetherianity supplies a finite-type centre ideal. Proper base change makes the unit an isomorphism separately on the centre and its complement. Exact stalks and conservative geometric stalks detect it; exactness and the invertible closed counit justify the affine hyperplane embedding reduction, which preserves the scheme structure of the centre.

Step 10 uses the existing generic-vanishing node on affine space and a coordinate hyperplane, with the input restriction zero by Step 8. Affine space is normal; the chosen hyperplane is principal. Its generic-stalk conclusion, together with constructibility, makes the support a proper closed subset. For n=1 this is already all of the point. Step 11 keeps the original dimension induction, now citing the same independent projection and finite-support lemmas instead of their inline arguments. The line lies inside H, so the quotient pair is exactly the lower-dimensional coordinate-hyperplane pair. Properness and the direct-image constructibility statement have the same coefficient hypotheses as Step 5. Step 7 identifies the canonical defects, and the finite-support theorem detects their vanishing.

Step 12 retains the naturality and adjoint-mate calculation for Borel--Moore specialization: sp(alpha) theta_A = theta_omega alpha and b theta_omega = id, hence b sp(alpha) theta_A = alpha. I checked these against the specialization definition, the nearby-cycle theorem's unit/counit compatibility, and the functor package. No properness of T or invertibility of alpha is assumed.

Step 13 applies the new proper Borel--Moore compatibility lemma with h = id_T and total lift r. Closed immersions are proper by the exact cited permanence clause. I repaired the retained new node, which merely repeated a specialization of the existing nearby-cycle exchange theorem: it now states the proper-pushforward/specialization equality on Borel--Moore Hom modules used here. This is a compatibility lemma, not the constant-family identity or the nilpotent-invariance clause being proved. Its future argument is the composition compatibility of compact-support exchanges in the specialization formula, ordinary units and exceptional counits; I read §§1.3.2 and 1.3.3 and the Theorem 2.1.3(b) reduction for precisely this use.

Step 14 uses the surjective-closed-immersion universal-homeomorphism statement to obtain all base changes, the unrestricted small-etale-site equivalence on the total trait schemes, and `i-topology` only on the finite-type special fibres. Dualizing composition gives r_0^! omega = omega_T. Step 15 uses exactly the proper pushforward definition: its ordinary unit and exceptional counit are invertible under the equivalence of Step 14, and full faithfulness then gives an isomorphism on Hom modules. Thus the specialization is the constant identity followed by the equivalence-induced map, with its actual canonical arrows identified by Step 13.

I opened every cited node's statement and rebuilt `citations.json` from those current statements, with one verbatim quote per use per step. I checked the independent geometry node against the monic-polynomial proof: choose a nonzero polynomial vanishing on Y and a direction where its highest homogeneous part is nonzero, make it monic along that direction, then homogenize in the relative P1 to exclude infinity. Ordinary Noether normalization in Mathlib allows nonlinear coordinates and does not assert this linear/no-infinity conclusion; `exists_monic_aeval_eq_zero_forall_mem_of_mem_map` assumes integrality and does not choose the projection. Etale direct-image support conservativity is not the Mathlib scheme structure-sheaf pushforward faithfulness appearing in the search results. The proper-specialization search hits concern topological stalk specialization, not Borel--Moore sections. Recorded searches use the exact logged query strings, including punctuation; none was invented or repeated merely to fill a record.

Small cases: empty support Y gives any projection; m=1 gives a zero-dimensional finite support over k and no infinity; K=0 and V empty give zero, while V=W and hi finite reduce to finite etale direct-image detection. A finite morphism need not be surjective for detection on its source. Identity proper lifts give a tautological Borel--Moore compatibility square. For the item I checked empty X or Z, Z=X, the zero input, nonreduced Z=V(x^e) in A1, j_!A with zero restriction, dimension one, and a square-zero thickening of the constant family. No smoothness of the original pair is assumed. I corrected damaged TeX escapes introduced in the retained rewrite and stale step-number cross-references. There are 15 steps, maximum length 1688 characters; the unchanged longer arguments remain below the 2000-character threshold. No Lean, compiler, Lake, live-project write, direct git command, or agent delegation occurred.

## What remains

The three new lemmas extracted in this repair are intentionally statement-only and unsplit. The two lemmas from the first delivery already exist in the current repository. The item proof is complete conditional on these cited statements; after the required dry run succeeds, direct delivery is authorized by the current dispatched brief.

## Dry run

The first complete split passed deliver.py --no-push on 2026-10-17 (commit 49fffb52dc). A final citation audit added the exact-stalk theorem, the invertible closed counit used to reflect vanishing, explicit properness of the nilpotent immersion, and the naturality formula for the Borel--Moore identity. The final files are submitted to the same dry run again; that earlier worker did not push at that point.

## Earlier second reading by Q13 (original ten-step numbering)

- Item statement: checked against Varshavsky Proposition 1.4.2 (equation (1.8)), Examples 1.3.3(a)--(b), and the final reduction in Theorem 2.1.3(b); all clauses and hypotheses agree, including arbitrary closed subschemes and the nilpotent-thickening clause.
- Step 1: checked against §§1.3.1(e), 1.3.2(a), and Notation 1.4.1(a)--(d), plus the cited etale/pro-etale comparison statements; the Rees lift, finite-Tor transfer, and category change are stated dependencies and the verdict is correct.
- Step 2: checked against Remark 3.2.5 and the constant-family defect argument; proper and smooth exchange is used on the unit maps, and the dense-open constructibility reduction is explicit; pass.
- Step 3: checked against Remark 3.2.5 and §3.2.4; the monic-polynomial finite projection, projective compactification, finite-support conservativity, and closed-counit faithfulness are all supplied; pass.
- Step 4: checked against equation (1.8), Lemma 1.4.3(c)--(e), and Lemma 3.2.1(a)--(b); the flat Rees algebra calculation and proper/smooth exchange hypotheses match; pass.
- Step 5: checked against §3.2.2(I), including $Z=X$ and $Z=\\varnothing$; localization and exact defect reduction are correctly applied; pass.
- Step 6: checked against §3.2.2(II)--(III) and the cited blowup, properness, and recollement statements; the nilpotent and nonreduced cases are retained; pass.
- Step 7: checked against Claim 3.2.3 and the $n=1$ base case; the generic-stalk conclusion is exactly the new lemma's affine specialization; pass.
- Step 8: checked against §3.2.4; the chosen direction lies in the hyperplane, the monic equation removes infinity support, and the finite projection is used conservatively; pass.
- Step 9: checked against Examples 1.3.3(a)--(b); the displayed naturality and mate calculation proves the identity without properness; pass.
- Step 10: checked against the final paragraph of Theorem 2.1.3(b), the universal-homeomorphism site equivalence, and $i$-topology; the total and special-fibre schemes are kept distinct and the closed immersion's properness is cited; pass.
- New node `lem-trf-nearby-cycle-finiteness-exchange`: checked against §§1.3.1(e), 1.3.2(b)--(c), and Remark 3.2.5; repaired the statement to quantify the bounded constructible generic-fibre inputs for both exchange maps; searches remain recorded and no duplicate exists.
- New node `lem-trf-dnc-generic-zero-section-vanishing`: checked against Claim 3.2.3 and its §3.1/§3.2 proof; removed an extra non-zero-divisor hypothesis absent from the source (the affine coordinate case remains valid); searches remain recorded and no duplicate exists.

Changes made: repaired both new-node statements for source fidelity and self-contained quantification; refreshed the affected verbatim citation quotes; no proof step or item clause was otherwise changed.


## Repair for returned delivery

The return required extracting hidden arguments from original steps 3 (2523 characters) and 10 (2235 characters), preserving the statement, Lean record, route and other steps. The retained interrupted attempt had already introduced three new nodes; I continued those same files, retained all search logs, and repaired their statements and usages as described above. Original step 3 is now Steps 3--6, and original step 10 is now Steps 13--15. Original step 8, now Step 11, reuses the same projection and conservativity nodes rather than repeating their arguments. Other original steps are retained with updated cross-references.

The first resumed dry run stopped at search validation, before any push: the recorded finite-support query lacked the period actually present in the log. I replaced its search entries with exact queries/results from the retained log and corrected all three new nodes' statements for self-contained quantification. The new nodes remain statement-only. No required mutation from an interrupted delivery was repeated while active.

The next dry run and direct-delivery results are recorded below when they exit.


## Resumed transport-failure retry, 2026-10-17

I continued the retained repair rather than replacing it. The current shared item still has the returned ten-step proof; the sandbox has the repaired fifteen-step proof and the three extracted statement-only lemmas. A field comparison confirms identical item statement and Lean record. I independently read the source text at §1.3.1–1.3.3, the final reduction of Theorem 2.1.3(b), and §3.2.1–3.2.5. The extracted geometry statement applies also to empty Y and m=1; the finite-support statement applies to bounded complexes on W, not on S, and does not require h itself finite; the proper-specialization statement compares arbitrary sections under a proper lifted morphism, rather than repeating the nilpotent-isomorphism conclusion.

I rechecked every current cited statement and all 52 citation quotes: each quote is verbatim, every step use is represented, and the union of uses is the recorded proof dependency set. New whole-blueprint searches for linear projection, finite support, proper specialization, Borel and nearby, and the corresponding whole-DAG scan, gave no replacement for any of the three extracted statements. The existing finite-stalk formula and curve finite-support theorems have the narrower conclusions described in Not duplicates. I read the retained Mathlib search log and kept its exact queries, results and service status. No new search claim was manufactured, and no search was repeated because of the transport failure.

The changes specifically requested by the return remain visible: original Step 3 is now Steps 3–6 with separate projection and finite-support citations, and original Step 10 is now Steps 13–15 with proper Borel–Moore compatibility cited before topological invariance. The other steps retain their route and argument, updating only cross-references and reusing the extracted lemmas. No non-elementary step exceeds 2000 characters (maximum 1688). The required dry run is running as a single queued invocation; it has not yet admitted the delivery for checking.
