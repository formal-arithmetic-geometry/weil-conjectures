# Stage 1 report

## Files written

- `lem-pc-koszul-affine-detection.json`: item split into three proof steps; one auxiliary node created.
- `lem-pc-koszul-derived-module-detection.json`: statement-only unsplit node; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None. No sorry-free declaration in the project source states this item or the auxiliary ring-level statement.

## WANTED:

None. The proof follows the available Stacks Project Tag 09IR route.

## What was checked

I read the imported item and its blueprint ancestor `lem-sc-finite-duality`, plus the already split affine comparison node `lem-pc-affine-qcoh-derived-equivalence`. The item statement retains the affine scheme, principal-open complement, all positive Koszul powers, and the unrestricted derived Hom vanishing hypothesis. I searched the whole DAG and blueprint for Koszul detection and found no duplicate; the sibling Tag 09IR node explicitly identifies this item as its affine input.

The new node is strictly ring-level: it introduces a derived A-module and localization at each f_i, rather than repeating the sheaf statement. Its statement is sourced to Tag 09IR's use of Lemma 36.9.6 and is statement-only as required for an unsplit child. LeanFinder, Loogle, grep, and LeanSearch were run with the recorded queries; only generic derived-category orthogonality declarations appeared, and LeanSearch was unavailable.

Step 1 uses exactly the existing affine derived-equivalence statement to choose the module model and transport the Koszul complexes and Hom groups. Step 2 checks the hypotheses: the principal opens D(f_i) cover U, and the associated-sheaf description on principal opens turns restriction by zero into acyclicity after localization; it then invokes the ring-level node. Step 3 applies that node to obtain M=0 and reflects zero back through the stated equivalence. The only elementary identifications are the usual associated-sheaf/Koszul correspondence on Spec(A) and the principal-open localization calculation; all non-elementary conclusions are cited. I checked r=0 (U empty, the single Koszul complex A), r=1, and a zero complex as edge cases.

## Review by J1

I checked the item source (Stacks Tag 09IR, with the affine comparison of Tag 06Z0) and opened every cited node. The affine comparison node really states an equivalence D(A) to D_QCoh on Spec(A), including the image of shifts, which is what Step 1 and Step 3 use. The new ring-level node states both localization vanishing and the all-positive-power Hom criterion used in Steps 2 and 3; the quotes in `citations.json` are copied verbatim. The hypotheses are introduced before use: A and the f_i in the item, M and its localizations in the child, and the principal-open cover in Step 2. I corrected the initial item search records to match the actual msearch log and added the unavailable LeanSearch result. No existing Lean declaration or DAG node states either the item or the ring-level detection statement.

## Not duplicates

lem-pc-koszul-derived-module-detection vs lem-pc-koszul-affine-detection: the new node is a ring-level statement for an object of D(A) with explicit localizations M_{f_i}=0; the existing item is its sheaf-level Spec(A) formulation with restriction to U and quasi-coherent derived objects.
lem-pc-koszul-derived-module-detection vs lem-pc-perfect-generation-open-induction-step: the new node is the affine Koszul detection input, while the existing node constructs a global perfect generator on a quasi-compact scheme and does not assert any Koszul Hom criterion.
lem-pc-koszul-derived-module-detection vs lem-pc-perfect-generation-koszul-orthogonal: the new node is the ring-level affine detection lemma; the existing node is the open-immersion equivalence whose proof invokes this affine input and additionally compares E with a derived pushforward.

## Second reading by J1

- Item statement: checked against Stacks Tag 09IR, label `lemma-orthogonal-koszul-complex`, and the affine comparison Tag 06Z0; the affine scheme, principal-open complement, positive Koszul powers, and unrestricted derived Hom vanishing agree hypothesis by hypothesis; verdict: retained.
- Step 1: checked against the statement of `lem-pc-affine-qcoh-derived-equivalence`; its equivalence supplies the module model, associated Koszul complexes, and Hom identification; verdict: valid.
- Step 2: checked against Tag 09IR's affine reduction and the statements of `lem-pc-affine-qcoh-derived-equivalence` and `lem-pc-koszul-derived-module-detection`; the principal-open localization calculation is written explicitly as an elementary termwise-association argument, and the opens cover U; verdict: repaired and valid.
- Step 3: checked against the statements of `lem-pc-koszul-derived-module-detection` and `lem-pc-affine-qcoh-derived-equivalence`; the ring-level conclusion and reflection through the equivalence are exactly available; verdict: valid.
- New node `lem-pc-koszul-derived-module-detection`: checked B1--B7 against Tag 09IR, label `lemma-orthogonal-koszul-complex`, and the affine module reduction; it is statement-only, self-contained, strictly smaller than the item, and tested for r=0, r=1, and zero M; verdict: retained.

Changes made: corrected both source locations to name the Stacks tag and label; expanded Step 2's localization argument and marked only that short calculation elementary; recorded this second reading and its edge-case checks. The inherited `created` field on the item was left unchanged because it is a maintainer-owned field on the base node.

