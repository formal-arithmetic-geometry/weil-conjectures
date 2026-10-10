# Worker report: lem-weil-pbc-regular-local-quotient-kernel-parameters

Date: 2026-10-10. Group: J1. Stage 1 only; no Lean edits, builds, or git operations.

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-local-quotient-kernel-parameters.json`: three-step split of Algebra Tag 00NR.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-regular-local-quotient-independent-generators.json`: new unsplit helper statement; Mathlib has no match, but a sorry-free source-repository declaration is attached.
- This report.

## Attachments

- `IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient` belongs to `lem-weil-pbc-regular-local-quotient-independent-generators` (source module `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`, lines 431-572; sorry map for the 71d63dcf done branch reports `sorry: false`).

## WANTED

None. The Stacks source is available at `literature/stacks-project/algebra.tex` and the source checkout supplies the closed cotangent-space helper.

## Corrections and argument

The item statement agrees with Algebra Tag 00NR (lemma-regular-quotient-regular), including the properness hypothesis and the cases `c = 0` and `c = d`. The source proof's key assertion is recorded as the new helper node in the exact form of the closed declaration: a finite set in the maximal ideal spans `I` and has linearly independent cotangent classes. Properness of `I` in the local ring gives `I ≤ m`, the explicit hypothesis needed by that declaration.

The item steps use only statements they cite. Step 1 applies the helper. Step 2 extends a finite independent set to a cotangent basis, uses the existing cotangent-dimension leaf to identify the basis cardinality with `d`, and applies the existing Nakayama generator criterion. Step 3 is the ideal-span identification. The linear-algebra basis extension and the set enumeration are the only elementary operations; all non-elementary regular-local facts are cited. The helper is deliberately unsplit because its source declaration is closed and sorry-free.

The three Mathlib searches for the helper (LeanSearch, LeanFinder, and source grep) found no Mathlib theorem; the grep also located the attached project theorem. The existing item searches were retained. The source and statements were checked for the hypotheses `R` regular local, `I` proper (hence inside the maximal ideal), and `R/I` regular local. Edge cases `I = 0` (`c = 0`) and `I = m` (`c = d`, when the quotient is the residue field) are valid; no nonzero or positive-dimensional assumption is used.

## Review by J1

I read Algebra Tag 00NR and its proof at lines 25749-25777 of the supplied Stacks checkout. The item statement matches the tag hypothesis by hypothesis: regular local `R`, proper ideal `I`, regular local quotient, and a minimal generating set of the maximal ideal with `I` an initial segment. The helper statement matches the attached declaration exactly after spelling out `m`, `kappa`, and the cotangent space; its explicit `I ≤ m` assumption is discharged from properness in step 1. The declaration was checked in `WeilConjectures/Mathlib/RingTheory/RegularLocalRing/Defs.lean` lines 431-572 and against the 71d63dcf sorry map.

Step 1 uses precisely the helper and the local-ring consequence that a proper ideal lies in the maximal ideal. Step 2 uses the existing cotangent-dimension statement and Nakayama's lemma; the cited statements supply the dimension and the generator criterion, while finite-dimensional basis extension is elementary linear algebra. Step 3 uses the helper's span equality and is a direct set/ideal identification. No step relies on an internal proof of another node. The new helper is an unsplit statement-only node with all objects introduced, source tag, three Mathlib search kinds, and `lean_audit.slopmaster2.state = closed`; its declaration has no sorry. The item has the required blueprint references and split report. Small cases `c=0` and `c=d` were checked explicitly, and the argument has no hidden characteristic, completeness, or finite-type hypothesis.

## B-E self-check

B: statements are self-contained, use TeX for mathematical notation, cite the regular-local definition, and carry the correct Stacks source place. The helper has no proof sketch and is status `unsplit`.

C: every non-elementary fact in the item proof is a cited node; no tag is used as an uncited theorem, no existing node is duplicated, and there is no dependency cycle.

D: the helper is strictly smaller than the item and contains no proof steps; the item steps perform the construction rather than merely restating the conclusion.

E: properness implies `I ≤ m`; finite independent subsets have cardinality at most the cotangent dimension; the basis-extension and Nakayama arguments work for empty and full sets. No false source step or extra hypothesis was introduced.

## Validation and unfinished work

The sandbox JSON files parse successfully. Repository-level `tools/check_dag.py` and `tools/review_split.py` are run by the delivery preflight against the merged tree; no Lean build is permitted at stage 1. Nothing remains unfinished.
