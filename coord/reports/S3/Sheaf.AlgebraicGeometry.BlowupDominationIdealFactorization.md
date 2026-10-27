## What changed

Kept the statement of
`AlgebraicGeometry.AffineBlowup.exists_hom_iff_exists_pow_eq_mul_of_radical_eq`
verbatim and replaced its hole by a proof from one per-chart intermediate lemma.
The main module now contains complete private proofs of:

- finite coefficient extraction from an ideal product;
- the finite-generation/binomial induction upgrading per-element colon relations
  to `K ^ n = J * L`, with `n ≥ 1` and `L.FG`;
- compatibility of the actual ideal sheaf associated to an affine ideal with
  products and powers;
- the affine/global blowup comparison, including transport along `ΓSpecIso`;
- the entire reverse implication, using principalization, invertible product
  factors and the existing blowup universal property.

The new module `Sheaf.AlgebraicGeometry.BlowupDominationColonPower` states the
remaining chart calculation. Its hypothesis only requires `K ≤ J.radical` and
finite generation of `J`; it does not require finite generation of `K`, and its
conclusion is a per-element membership in a colon product in `R`. The main proof
performs the subsequent uniform-exponent argument and finite coefficient
extraction explicitly. This is a genuine step of the original argument, not a
renaming of the equivalence or of its full forward implication.

Validation: `lcompile.py --all` compiled the new chart module (2.2 seconds);
the final `lcompile.py` compiled the item cleanly in 12.2 seconds. No global
build was run.

The item node's proof follows the implemented argument. The unit and chapter
route are unchanged. No existing public interface or definition was changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.AffineBlowup.exists_hom_iff_exists_pow_eq_mul_of_radical_eq`
(node `lem-per-blowup-domination-ideal-factorization`). There are zero holes left
in the item module.

Added one hole:
`AlgebraicGeometry.AffineBlowup.exists_pow_mem_mul_colon_of_hom`, in
`Sheaf.AlgebraicGeometry.BlowupDominationColonPower`, node
`lem-per-blowup-domination-colon-power`. Its whole proof is `by sorry`; its
docstring and node give the complete chart, evaluation and denominator-clearing
argument. There are no holes in definitions or private helpers.

This is a decomposition: one upper hole closed, one strictly smaller hole added,
net zero holes closed. The finite algebra and reverse implication are proved in
Lean without additional split statements. The reverse implication needs neither
radical equality nor finite generation of the factor, and its helper also works
for exponent zero.

## No longer needed

Removed these direct proof imports from the item:

- `WeilConjectures.Blowup.FiniteDegree.Algebra`;
- `WeilConjectures.Blowup.Affine.ChartAlgebra`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`;
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
- `WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections`;
- `WeilConjectures.Blowup.Gluing`.

`prop-nagata-affine-blowup-chart-cover` is no longer a proof dependency: the
intermediate statement works with each individual `b`-chart, so the forward
proof needs no finite chart cover. Finite-generation induction on subideals
replaces the explicit finite-list monomial pigeonhole argument. The module
`WeilConjectures.Blowup.FiniteDegree.Algebra` remains available transitively
through the universal-property import; this delivery does not withdraw it.

`def-nagata-blowup-chart-ring`, `def-sc-invertible-module`, and
`lem-sc-affine-invertible-sections` moved from the parent proof dependencies into
the new chart node's proof dependencies; they are still needed there. Likewise,
affine ideal extension and global blowup gluing are still used through the
remaining imports. Removed the obsolete parent `tool_uses` entry for
`lem-sc-affine-invertible-sections`; evaluation is now used by the new chart node.
No source-library declaration or module is withdrawn. No
whole-library pruning count is claimed merely from deleting redundant imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. I read ILO XX §4.4,
printed p.373 (PDF page 379), which states the domination criterion without its
proof, as the original node records. The supplied detailed proof is therefore
an explicit expansion of that criterion, using Stacks 07Z3, 02OS, 0B8I and 0806,
rather than a proof printed in ILO. I also read the corresponding Stacks chart,
principalization and universal-property passages and the recorded dependency
signatures.

The finite-list argument can be implemented more economically with
`Submodule.fg_induction` and the binomial expansion of ideal powers. The empty
generating-family case is handled by the singleton zero ideal in this induction.
For the new chart statement I checked zero rings, `b = 0`, nilpotent chart
denominators, `J = ⊤`, and `K = ⊥`: the argument permits an empty chart and clears
localization equalities by a further power, rather than assuming injectivity of
`R → R[1/b]`.

Mathlib searches ran via LeanFinder, LeanSearch, Loogle and grep; the useful
results were ideal radical/power APIs, not this blowup criterion. The blueprint
search for “blowup domination” found no blueprint node with this statement.
The existing item is the only DAG statement found for the complete criterion;
none of its recorded dependencies already states the per-chart colon relation.

## New nodes

`lem-per-blowup-domination-colon-power` isolates original steps 1–4. It states
positive-power membership for each individual denominator and leaves uniform
exponents and finite coefficient extraction to the main proof. It inherits the
item's chapter, unit and exact blueprint ancestry. Its source, three actual
Mathlib searches, complete natural-language proof, and Lean attachment are in
`dag/nodes/sec-deligne-laumon-a1/lem-per-blowup-domination-colon-power.json`.
No change record is required because no existing signature, public import or
shared definition changed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
