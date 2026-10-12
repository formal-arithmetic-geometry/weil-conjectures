## What changed

Proved `AlgebraicGeometry.Scheme.quotient_fibre_limit_transfer` in
`lean/Sheaf/AlgebraicGeometry/QuotientFibreLimitTransfer.lean`, with its existing
signature and visibility unchanged. Added proof-only imports of
`Mathlib.Algebra.Category.Ring.FilteredColimits` and
`Mathlib.AlgebraicGeometry.Morphisms.Separated`.

The private helpers construct the quotient ring diagram, its quotient projections,
and its cocone to A/I. The colimit universal property descends every quotient
cocone from A and kills I using stage representatives. No ring or scheme data is
chosen from an unproved existence theorem. The inverse scheme diagram consists
of the actual stage pullbacks. The limiting cone is proved directly by lifting its
two projected cones and applying pullback uniqueness. Spec preserves the limits
of the opposite ring cocones.

For affineness, the first projection at each stage is affine by base change. A
transition followed by the next first projection is affine by naturality. The
next first projection is separated, so `IsAffineHom.of_comp` proves the transition
affine. The stage isomorphisms are identities.

Updated the existing node's proof, proof dependencies, and proof origin to match
this argument. No statements, public imports, definitions used by targets, or
other modules were changed. The item does not realize a unit statement or step
in `dag/units/sk-thm-p1.json`; its enclosing unit route is preserved.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.quotient_fibre_limit_transfer`
(node `lem-weil-pbc-quotient-fibre-limit-transfer`).

One hole closed, zero holes added, zero split off. No `sorry` remains in the
item or in any delivered helper. This is a proof, not a decomposition. All private
constructions and their proof fields are complete.

Validation: the resumed worker independently compiled the complete earlier proof through
`lcompile.py` (exit code 0, no warnings). The delivery dry run also checks the axioms
of every declaration. Every original binder and conclusion is retained.
The edge cases I = top, I = 0, the zero ring, noninjective stage maps, and a
singleton index require no extra assumptions: quotient surjectivity, stage
representatives, and pullback universal properties still apply in each case.

## No longer needed

The proof no longer uses node `lem-weil-pbc-closed-immersion-base-change`.
It has a Mathlib match rather than a Sheaf module; no corresponding project
module is removed. The closed-immersion factorization from the old third proof
step is replaced by cancellation against an affine, hence separated, projection.
This is local dependency pruning, not a claim that the node is unreachable from
all other targets.

No original import was removed. The three original public imports are preserved.
An exploratory direct import of `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`
was removed because the filtered-ring-colimit import already supplies it.
No other original proof dependency is pruned: the proof uses elementwise stage
representatives, Spec limit preservation, pullbacks, and affine permanence.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old affineness argument is valid but unnecessary;
Mathlib's `IsAffineHom.of_comp` supplies a shorter route. The module originally
had only its three public Mathlib imports, not proof-dependency Sheaf imports;
the necessary dependencies here are Mathlib ingredients.

Read the source's General case quotient-colimit and closed-fibre-limit paragraphs
in [Stacks Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2), and the affine
Spec-limit statement in [Stacks Tag 01YW](https://stacks.math.columbia.edu/tag/01YW).
Local literature copies are absent on this remote machine, so the official online
text was read. The proof supplies the categorical details of those paragraphs.
LeanFinder, Loogle, and grep searches ran through the supplied `msearch.py` wrapper;
no theorem giving this entire transfer was found. Pinned Mathlib source inspection
located the quotient-map, colimit-representative, pullback, and affine-cancellation
ingredients actually used.

The resumed worker read and checked the earlier sandbox construction, independently
compiled it, and restored the original theorem docstring. The node retains the
updated argument; its quotient-colimit step is marked non-elementary because the
Lean proof constructs and verifies the full universal property.

## Second reading by R3

1. Compared the delivered module with the repository version. The theorem signature,
   visibility, and all existing declarations are unchanged; only proof imports and
   the theorem proof differ.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
   The proof uses only the permitted categorical and ring constructions.
3. Checked the node and searched the repository for duplicate declarations. The node's
   statement is unchanged and the proof text now describes the actual quotient-colimit,
   pullback-limit, and affine-cancellation argument. No new theorem was split off.
4. Read the proof from the target downward. The quotient colimit is constructed by
   representatives and `Ideal.Quotient.lift`; Scheme.Spec limit preservation and the
   pullback universal property establish the limiting cone; `IsAffineHom.of_comp`
   supplies the transition affineness. The old closed-immersion dependency is unused
   and has been removed from `proof_deps` below.
5. The unit route is preserved: this item remains the quotient-fibre transfer node of
   `sk-thm-p1`, and no unit statement or step is bypassed.

Changed the node metadata to remove the unused affine-permanence dependency. No Lean
source changes were needed during second reading.
