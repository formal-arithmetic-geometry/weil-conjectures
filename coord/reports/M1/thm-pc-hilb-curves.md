# Stage-1 report: thm-pc-hilb-curves

## Files written

- `dag/nodes/sec-picard-framework/thm-pc-hilb-curves.json`: repaired item split with corrected proof dependencies.
- `dag/nodes/sec-picard-framework/lem-pc-hilb-separated.json`: statement-only node, no Mathlib match.
- `sk-thm-picard-hilb-curves.json`: realized statement and proof step metadata.
- `citations.json`: verbatim statement quotes for every cited node in each proof step.

## Attachments

No whole-item attachment. The source has separate declarations `AlgebraicGeometry.hilbertPresheaf_curve_representable`, `AlgebraicGeometry.hilbertPresheaf_curve_points`, and `AlgebraicGeometry.hilbertPresheaf_curve_add`; their transitive sorry dependencies make them unavailable as a sorry-free exact declaration of the combined item.

## Not duplicates

`lem-pc-hilb-separated` vs `lem-pc-hilb-representable`: representability constructs the Hilbert scheme, while the new node states separatedness of the representing scheme.

## WANTED

WANTED: `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-hilb-curves/thm-pc-hilb-curves.md`, the imported blueprint proof source (the repository contains only its recorded node text).

## What was checked

The target statement was compared with the item node and with the unit `sk-thm-picard-hilb-curves`. The source Lean file `WeilConjectures/AlgebraicGeometry/Hilbert/Curve.lean` was read at the three declarations and at the tagged helper declarations. The representability declaration supplies the smooth proper geometrically integral representing scheme and universal divisor; the points declaration supplies the effective-Cartier-divisor characterization; the addition declaration supplies the finite-flat binomial-degree map. The declarations are separate and the audit marks the representability/addition chain as resting on sorry-backed declarations, so this is a split rather than an attachment.

## Review by M1

Repair review: I reread Stacks Tags 0B9I and 0B98 and the statements of every newly cited DAG node. Step 0 now cites `lem-sc-proper-dim-one-projective` before applying the smooth projective curve ampleness lemma. Step 1 cites `lem-pc-hilb-separated`, the image-universally-closed, product-irreducibility, finite-proper, proper-base-change, proper-composition, and smooth-geometrically-reduced nodes; each statement supplies the corresponding separatedness, properness, product, irreducibility, or reducedness fact. The finite locally free map `pi_d` is surjective by its positive rank, so the prior geometric closed-point argument is removed. Step 3 records the proper-source/separated-target criterion (Tag 01W6) for `alpha` and cites the finite-proper node. I checked the $d=0$ and $d=1$ cases and the binomial rank edge cases. The prior bare Tags 03GN/038F and proof-only separatedness citation are removed.

I read the imported proof and checked each step against the statement of every cited node. Step 1 uses the representability, degree invariance, positive-degree ampleness, and affine-complement statements exactly for the affine-open hypothesis. Step 2 uses representability, smoothness, the morphism conventions for separatedness, the addition map, and the variety definition; the hypotheses are the given proper smooth geometrically integral curve hypotheses. Step 3 uses the Hilbert-functor and base-change definitions, the Cartier criterion, the degree definition and degree base-change lemma; over a field, finite locally free is flat, so the relative Cartier criterion applies. Step 4 uses the Cartier criterion for sums, the proper-plus-finite-fibres criterion, and flatness descent along a flat surjection. The verbatim quotes for these uses are in `citations.json`.

I searched the whole DAG and blueprint before creating nodes; all fourteen proof dependencies already exist, so creating a narrower lemma would duplicate an existing statement or merely restate a clause of this item. Cross-unit dependencies (`def-pc-morphism-conventions`, `def-pc-curve`, `def-pc-base-change`, and `thm-pqf-finite-iff-proper-finite-fibres`) are declared as tool uses because the unit route has no replacement nodes. I tested the boundary cases mentioned by the proof: $d=0$ gives the point `Spec k`, the addition with one degree zero has binomial degree one, and the Cartier criterion over a field reduces to finite flatness. No statement was changed.

The required LeanFinder, Loogle, Mathlib grep, and LeanSearch queries were run for the item. LeanFinder returned only generic smooth/projective declarations, Loogle and grep found no Hilbert/Picard scheme result, and LeanSearch was unavailable; these exact outcomes are recorded in the item JSON.

## What was wrong or incomplete

The imported node was marked `imported` despite having a multi-declaration Lean audit and no blueprint metadata. I filled its blueprint reference, marked it `split`, and realized the unit fields. No mathematical statement was altered.

## What could not be finished

The referenced blueprint markdown file is absent from this checkout; its path is recorded under `WANTED`. No new node was needed.

## Second reading by M1

- Step 0: checked against Stacks Tag 0B9I (the affine-open argument) and the four cited node statements; the closed-point choice and positive-degree complement argument agree with the stated hypotheses.
- Step 1: checked against Tag 0B9I and the representability, smoothness, diagonal, addition, curve, and degree arguments; found and repaired the `d=0` edge case by using `lem-sc-hilb-zero-base` before the `d\geq1` induction.
- Step 2: checked against Tag 0B9I and the Hilbert-functor, base-change, Cartier-criterion, degree, and degree-base-change statements; the field-extension and degree-rank specialization is correct.
- Step 3: checked against Tag 0B9I and the Cartier, proper-finite-fibres, and flat-source-descent statements; the addition map, finiteness, flatness, and binomial-rank calculation have the required hypotheses.
- New nodes: none; the item uses only existing DAG nodes, and no duplicate or Mathlib leaf was introduced.

Changes made: added the existing `lem-sc-hilb-zero-base` dependency and verbatim citation, and split Step 1 into the `d=0` base case and the `d\geq1` addition induction. This removes the undefined `H_{-1}` reference while preserving the theorem statement.

Additional second-reading repair: Step 3 previously used a short exact sequence for
the sum of two Cartier divisors without a regular-sequence hypothesis; that sequence
is false when the divisors share a component. I replaced it with the valid argument
that the product equation gives a relative Cartier divisor, whose finite fibres and
properness imply finite locally free by the proper case of the Cartier criterion.
I also corrected the affected citation quotes to be verbatim statements of the cited
nodes. The dry-run delivery checker passes after this repair.
