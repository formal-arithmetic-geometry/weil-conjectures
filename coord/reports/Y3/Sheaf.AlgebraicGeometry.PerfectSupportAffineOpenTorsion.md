## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.perfect_support_affine_open_torsion` by a complete Lean
proof combining two strictly separate parts of the original affine argument.
The original signature, universes, hypotheses, visibility and docstring are unchanged.

The proof first obtains affine module models with a full additive comparison functor.
It lifts `eP.hom ≫ β ≫ eM.inv` to a module-derived morphism using fullness, applies the
bounded finite-projective torsion result, and maps the resulting equality back.
Scalar compatibility at `f ^ n` identifies the mapped source scalar with the requested
localized-site scalar. Cancellation of the two isomorphisms gives exactly the original
conclusion. Evaluation of the compatible scalar family commutes with powers by `rfl`.

Added two new statement modules, each containing one named public theorem with its
complete source proof in its docstring and corresponding DAG node. The main module
uses ordinary proof imports for them. Updated the parent's proof and proof-dependency
records to match this Lean proof. No definition or existing statement was changed,
and no other existing module was adapted. A theorem-scoped `maxHeartbeats 400000`
allows the sheaf-ring coercion comparisons during elaboration; compilation stays
well below the 60-second limit. All three files compile in dependency order.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.perfect_support_affine_open_torsion`
(node `lem-sc-perfect-support-affine-open-torsion`). No `sorry` remains in the item.

Added exactly two holes, each the whole proof `:= by sorry` of its public theorem:

- `AlgebraicGeometry.Scheme.perfect_support_affine_module_model`
  (node `lem-sc-perfect-support-affine-module-model`, module
  `Sheaf.AlgebraicGeometry.PerfectSupportAffineModuleModel`). This constructs affine
  module models, elementwise torsion of target cohomology, and scalar comparison.
  It does not assert annihilation of derived morphisms.
- `DerivedCategory.bounded_projective_hom_power_torsion`
  (node `lem-sc-bounded-projective-hom-power-torsion`, module
  `Sheaf.CategoryTheory.DerivedCategory.BoundedProjectiveHomPowerTorsion`). This is
  the ring-theoretic induction from elementwise cohomological torsion to derived-Hom
  torsion. It has no schemes, supports, restrictions, or global scalar families.

This is a decomposition: one upper hole closed, two strictly separate lower holes
added, net holes minus one in progress terminology (one more remaining hole).
The main proof is complete, but still depends on these two unproved statements.
No data definition was introduced or selected from an unproved existence theorem.

Edge cases checked mathematically before stating the new results: a zero source and
empty affine open give zero Hom; the zero ring makes the module category zero;
`r = 0` kills every morphism with exponent one; a unit `r` forces the assumed
cohomology modules to vanish and hence makes the target zero. Empty finite generating
sets work with exponent zero. The target is allowed to be unbounded: the induction
uses one degree at a time and never a uniform exponent across all its cohomology.

## No longer needed

Removed the following direct proof imports from the original item:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`
- `Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison`

They and their nodes `lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-perfect-affine-bounded-projective`, and
`lem-pc-open-derived-restriction-comparison` remain needed by the affine model step,
and are imported by that new module. No node or module is globally pruned. The unit
route is retained: this is an explicit split of the originally planned affine
comparison and finite-projective Hom induction, not an alternative argument.

## Where the brief, the DAG or earlier work was wrong

The original dependencies provide the affine equivalence, bounded projective model
on Spec, and restriction of quasi-coherence and support. Their signatures do not
provide the assembled arbitrary-affine-open model or the scalar compatibility
needed by this theorem. The ring Hom induction also had no named dependency in
steps 2 and 3 of the parent. The two new nodes make those remaining tasks explicit.

No mathematical falsehood or signature defect was found. Mathlib searches found
projective single-term vanishing and K-projectivity, but no direct theorem matching
either new statement. LeanSearch returned Internal Server Error and is recorded as
unavailable; LeanFinder, Loogle and source grep ran. Whole-blueprint searches for
`08EJ` and `finite projective` found no duplicate statement. The automated ancestor
query returned None because the parent was created for a module rather than a node;
the new nodes retain its already recorded `lem-sc-finite-duality` ancestry explicitly.
The parent is not named in the unit's `realized` statements or proof steps.

The repository's recorded `literature/stacks-project/perfect.tex` is absent on this
machine. The relevant source paragraphs were read directly from the canonical
Stacks pages [08EJ](https://stacks.math.columbia.edu/tag/08EJ) and
[08EB](https://stacks.math.columbia.edu/tag/08EB).

## New nodes

`lem-sc-perfect-support-affine-module-model` records the affine geometry and scalar
comparison step in `PerfectSupportAffineModuleModel.lean`. It carries the three
original proof dependencies, retaining their role in the plan. Its cohomological
torsion condition is strictly prior to the derived Hom conclusion.

`lem-sc-bounded-projective-hom-power-torsion` records the algebraic single-projective
case and stupid-truncation induction in `BoundedProjectiveHomPowerTorsion.lean`.
Its detailed proof uses the maximum of finitely many annihilating exponents in the
base case and the sum of two exponents in the induction step.

There are no interface change records or forced adaptations.

## Second reading by Y3

1. Compared the sole existing delivered module with the repository by diff and
   checked its theorem signature byte for byte. Verdict: unchanged hypotheses,
   conclusion, universes and visibility; only proof, proof imports and a local
   elaboration option changed. No definitions or interface changes were introduced.
2. Compiled all three modules in import order with lcompile.py. Inspected all
   delivered declarations for forbidden constructs and hidden holes. Verdict: the
   parent proof is complete; the only two remaining holes are exactly the two
   named public theorems listed above. A scratch copy with #print axioms confirms
   only propext, Classical.choice, Quot.sound and the expected sorryAx. The
   existential models are eliminated inside a proof of a proposition; no data
   definition chooses an arbitrary witness from an unproved existence theorem.
3. Read both new statements and their complete docstring arguments against the
   canonical Stacks Tags 08EJ, 08EB and 06Z0. Verdict: they are true and strictly
   separate parts of the affine argument, not renamed copies of the item. Checked
   zero source, empty support interval, empty affine, zero ring, zero scalar, unit
   scalar and arbitrary unbounded target. In the ring induction, the top-degree
   term is the subcomplex and the shorter stupid truncation is the quotient;
   contravariant Hom exactness has the required direction. Repeated LeanFinder,
   Loogle and grep searches with different terminology, plus rg of both library
   roots. No duplicate or shorter complete proof found. The finite-module
   localization lemma can assist the base case, but neither split theorem can be
   closed in a few minutes from the available interfaces.
4. Checked the parent proof from its conclusion down through fullness, additive
   mapping, scalar compatibility at f^n, and cancellation of both isomorphisms.
   Verdict: it is a real reduction and uses precisely the two new lemmas. The
   three old direct dependencies remain below the model lemma, so none is globally
   pruned. Read dag/units/sk-thm-picard-duality.json: its realized lists are empty;
   no recorded unit step is bypassed or changed. The affine comparison and
   finite-projective induction route is retained. Trimmed redundant imports.
5. Checked the parent proof steps and proof_deps against the Lean proof, and both
   new nodes against their modules, proof docstrings, source, provenance, searches
   and ancestry. Verdict: consistent. Corrected the two new lean.statement fields
   from whitespace-normalized text to verbatim multiline declaration signatures.

Second-reading changes: removed redundant public import
Mathlib.Algebra.Homology.DerivedCategory.Linear from the model module (already
public through DerivedGlobalScalar); replaced the unnecessarily broad public
import Mathlib.Algebra.Module.FinitePresentation in the ring lemma by
Mathlib.RingTheory.Finiteness.Defs, which supplies the Module.Finite notion used
in its statement; wrapped one proof line to the 100-column convention; corrected
both new node signature records and added the independent search results. All
other imports are needed for statement notation, structures or recorded proof
steps. No proof or statement was rewritten. This remains a decomposition: one
original hole closed, two lower holes added, net closed-minus-added = -1; zero
modules globally pruned.
