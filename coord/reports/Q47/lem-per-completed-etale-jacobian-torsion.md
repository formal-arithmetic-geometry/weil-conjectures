## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-completed-etale-jacobian-torsion.json`: split statement; six steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-polynomial-conormal-completion.json`: one new statement-only lemma, Stacks 0GAF; no Mathlib match.
- `citations.json`: current verbatim statement quotations for every proof-step citation.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint id, completed Jacobians, rig-etale terminology, and completion/cotangent comparisons found no declaration stating the item or the new comparison. The Jacobian torsion data in Purity/RealSheaves/Jacobian.lean concern Jacobians of curves and do not state either result. The upstream master reference also has no completion/cotangent declaration matching the new lemma. No compiler was run.

## WANTED

None. All mathematical sources used are in the local Stacks source.

## What was wrong and what changed

The repository item has an empty proof. I retained the earlier attempt's completeness argument, ordinary etale criterion, finite-generation ideas, literature references, and all logged searches. The mandatory initial dry run finished with a duplicate-tag diagnostic for its helper `lem-per-topologically-finite-completed-presentation`: it shared 0AJP with the item and `lem-per-jacobian-torsion-closed-base-change`. In this finite-algebra case that helper is unnecessary: module generators give finite type, and the existing finite-presentation theorem gives an ordinary polynomial presentation. I removed the uncommitted helper and replaced it with the genuinely needed general conormal completion comparison (0GAF).

The earlier Step 4 incorrectly identified ordinary localization with the completed cotangent complex without a comparison theorem. The repair proves torsion for an ordinary polynomial presentation first and only then completes it using 0GAF and the already proved isomorphism E = E^wedge. The support/radical argument is replaced by the explicit finite-generator power argument in 0ALQ. This also avoids silently invoking the prime-ideal description of a radical. The item statement has not changed.

The earlier report's edge-case claims were wrong: r=0 does not imply J=0, and I=0 does not imply etaleness, since its complement is empty. The corrected checks below do not make either assertion. This is a repair of the retained proof and report, not a dispute with the item's true statement.

The blueprint ancestry was checked with `tools/blueprint_refs.py ancestor`. The current ancestor's Step 1 reaches arbitrary-field duality, then partial algebraization, then the Elkik input. Its literal blueprint statement has no Jacobian clause; the retained attempt's ancestry wording claimed one. The item now retains the current repository's precise supporting-input location. The new lemma's `from` records the same chain and its role in Step 6. The unit and chapter route have not changed.

## Not duplicates

- lem-per-polynomial-conormal-completion vs lem-per-jacobian-torsion-etale-shrink: both cite 0GAF, but the existing statement assumes a torsion bound in a completed presentation and concludes etaleness after shrinking by g in 1+IC. The new lemma compares the two conormal modules and their differentials for a fixed algebraic presentation, with no etale or torsion hypotheses and no shrinking conclusion.
- lem-per-polynomial-conormal-completion vs lem-per-completed-etale-jacobian-torsion: the item concludes existence of a torsion bound for a finite algebra etale off an ideal over a complete base. The new lemma supplies a canonical completion comparison for an arbitrary polynomial quotient over a Noetherian base; it neither assumes nor proves any torsion bound or etaleness. The item still proves that bound in Steps 2–5.
- lem-per-polynomial-conormal-completion vs lem-trf-completed-conormal-determinant-comparison: the existing statement concerns local complete intersections over a perfect field, regular power-series presentations and determinant normalization. It does not cover arbitrary Noetherian bases, ideals or polynomial quotients.
- lem-per-polynomial-conormal-completion vs lem-per-completed-differential-finite-conormal: the existing result concerns degree-zero completed Kahler differentials over a subfield in a complete local ring with finite residue extension. It supplies no isomorphism of algebraic and completed conormal modules for a polynomial quotient over an arbitrary base.

Before creating the replacement I searched the entire DAG for 0GAF, lemma-NL-is-completion, completed polynomial presentations and completion/conormal keywords, and opened the existing same-tag shrink node and the apparent comparison candidates. Whole-blueprint searches for 0GAF, topologically finite, conormal completion, completed polynomial and cotangent found no matching blueprint statement. The two cotangent hits were a Lie-algebra derivation definition and a trace local-term locality lemma.

## Mathlib searches and retained search evidence

The earlier `searches.jsonl` entries were read and retained. The item was already searched with two natural-language phrasings, Loogle `Algebra.H1Cotangent, AdicCompletion`, and grep `rig.etale|completed.*cotangent|cotangent.*completion`; the results concern ordinary cotangent spaces, smooth lifting and etale loci, rather than this completed Jacobian assertion. The removed presentation helper's four searches are still in that log, and were not rerun.

The new lemma has five freshly executed, exactly recorded queries: LeanFinder with two distinct phrasings, LeanSearch, Loogle and a Mathlib/RingTheory grep. I read every returned hit. In particular `AdicCompletion.kerProj` (AdicCompletion/Algebra.lean:482) completes at the kernel ideal and projects to the original quotient, which is different from completion at an arbitrary base ideal. `Algebra.SubmersivePresentation.cotangentEquiv` (Smooth/StandardSmoothCotangent.lean:129) assumes a submersive presentation; the new lemma has no smoothness assumption. AdicCompletion/LocalRing.lean:161 concerns the maximal-ideal cotangent space of a local ring. The Weierstrass results concern a distinguished polynomial and the power-series quotient. No returned hit states the new comparison or specializes to it in one line. No service failure was recorded as absence, and no query was invented.

## What I could not finish

The new comparison is intentionally unsplit and joins the stage-1 queue. No Lean work belongs to this delivery. Delivery validation is performed with the required server dry run.

## Review by Q47

I read restricted.tex Tags 0ALQ (lemma-rig-etale), 0AJU (lemma-equivalent-with-artin), 0GAF (lemma-NL-is-completion), and the displayed equation-NL defining the completed conormal differential. Tag/label pairs were checked in tags/tags. For the new node I read the full proof of 0GAF: exact completion on finite modules identifies the completed kernel with KP, flatness identifies the quotient by its square, and the derivative formula gives the comparison of differentials. Its statement is self-contained, uses only the displayed polynomial presentation and completion data, and has no proof or proof dependencies. It is a smaller structural input independent of the torsion assertion. I also read algebra.tex 00FP, 00MA, 08JZ and 00CS for the presentation, completeness, principal localization and exact localization used below.

Step 1 uses `lem-weil-pbc-finite-module-complete-over-complete-noetherian`: its statement gives exactly the bijective canonical completion map for a finite module over a complete Noetherian ring. All three hypotheses hold for A and E. `def-weil-pbc-finite-type-algebra` gives the finite-generator meaning; linear combinations explicitly prove the reduction assertion. The ring comparison is the canonical map, so its module bijectivity is an algebra isomorphism.

Step 2 uses `lem-weil-pbc-finite-type-noetherian-finite-presentation` for existence of a polynomial surjection with finitely generated kernel, not for Noetherianity of a completed polynomial ring. `lem-weil-pbc-etale-ring-map-conormal-criterion` states the formula and well-defined E-linear ordinary conormal map for exactly such a presentation. `lem-weil-pbc-finite-algebra-noetherian` applies to E finite over A; `lem-weil-pbc-noetherian-submodule-finite` therefore applies to the kernel inside the finite E-module K/K^2. The cokernel finiteness is the explicit image-of-basis argument.

Step 3 uses `lem-weil-pbc-principal-localization-open-immersion` to identify the principal affine open and its open immersion, and `lem-weil-pbc-basic-open-pullback` to identify its inverse image in Spec E. The assumed etale restriction is thus the map Spec E_g to Spec A_a. Parts (1)–(2) of `lem-weil-pbc-etale-composition-cancellation` give the etale composite to Spec A. The statement of `lem-weil-pbc-principal-localization-naive-cotangent` explicitly supplies beta, its finitely generated kernel K+(at-1), and the direct-sum complex with the invertible g summand; it is an ordinary polynomial presentation throughout. The conormal criterion applies to beta over A and makes its differential bijective. The cited localization node's injectivity and cokernel clauses then imply the needed bijectivity. No completed differential is localized at this step.

Step 4 uses the statement of `lem-weil-pbc-localization-module-exact` on the kernel/cokernel exact sequences, giving U_g=V_g=0. The zero-fraction equivalence is literally in `def-weil-pbc-module-localization`. The maximum of finitely many generator exponents supplies a uniform exponent, for each a and both modules; this is written out rather than invoking an uncited support comparison.

Step 5 uses only `def-weil-pbc-noetherian-ring`, whose whole statement is that every ideal is finitely generated. The monomial pigeonhole argument explicitly produces c=1+sum(n_i-1); if I has no generators it uses c=1. This is the elementary step, and not a separate node.

Step 6 uses every clause of the new comparison: completed surjection, kernel KP, conormal identification, and equality of the derivative maps. Its hypotheses A Noetherian, I arbitrary, finite polynomial presentation and finitely generated K were checked in Step 2. The completeness isomorphism comes from Step 1. `def-weil-pbc-module-tensor-product` gives the tensor generator relations used to write the inverse pair m tensor e -> em and m -> m tensor 1. Thus the completed map has precisely the previously controlled kernel and cokernel; no invariance under an unspecified change of presentation is used.

Small cases: for I=0 the etale hypothesis is vacuous and c=1 kills every module; this remains valid for non-etale E, for instance k[x]/(x^2). For nilpotent I the complement is likewise empty, and the monomial argument supplies a killing power. For I=A, completeness forces A=0 and hence E=0. For r=0 one may have a nonzero quotient kernel K; the zero-target conormal map is retained and the same etale-local and power argument controls K/K^2. The new comparison at I=0 is the identity for any polynomial quotient, at K=0 is the identity on zero conormal modules, and at I=A both completions are zero. The zero algebra and empty generator lists cause no excluded case.

I checked B1–B9, C1–C8, D1–D5 and E1–E7 against the files: no hidden proof is left in the new statement, no new definition or existing theorem is duplicated, every non-elementary inference has a cited statement, every quote is copied verbatim, and no dependency is drawn from a cited node's proof. No SGA source is used. Every proof step is under 2000 characters. The only non-Mathlib/non-closed off-unit input is finite-module completeness, declared as a generic tool in split_report.tool_uses. The repaired proof follows the existing Elkik input and does not replace a unit step. The two substantive corrections were the missing completion comparison and the incorrect earlier edge-case explanations.
