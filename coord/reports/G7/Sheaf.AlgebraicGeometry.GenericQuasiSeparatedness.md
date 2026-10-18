## What changed

Proved `AlgebraicGeometry.exists_nonempty_open_quasiSeparated_restrict` in
`Sheaf.AlgebraicGeometry.GenericQuasiSeparatedness`, with its signature unchanged.
The proof follows Stacks Project Tag 052A: generic finite presentation of cyclic
chart-complement modules, compactness of their support complements, a common product
of principal shrinkings, and Mathlib's affine-cover criterion. Four fully proved
private helpers provide the quotient-localization comparison, the ring-level compactness
argument, its transfer to affine schemes, and the affine-base construction. The general
base case restricts to a nonempty affine open and transports the result back along the
canonical isomorphism between double and single restriction.

Added proof imports of `Mathlib.Algebra.Module.LocalizedModule.Submodule`,
`Mathlib.RingTheory.Localization.Ideal`, and `Mathlib.RingTheory.Localization.Module`.
Updated the existing node's proof to describe the implementation. No public interface,
definition, or target statement changes. No new modules are delivered.

Validation: the full proof was compiled through `lcompile.py`; the delivery dry run
checks the final module and its declarations. The argument includes empty source/cover
(the common product is 1), zero chart rings, and empty or full chart intersections.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.exists_nonempty_open_quasiSeparated_restrict`
(node `lem-pur-generic-quasi-separatedness`). Added 0 holes. No `sorry` remains in
the delivered module, and all four private helpers are proved.

The proof uses the existing declarations
`Module.Finite.exists_finitePresentation_localizedModule_powers`
(node `lem-pur-generic-finite-module-presentation`) and
`Module.isClosed_support_and_isCompact_compl`
(node `lem-pur-finitely-presented-support-complement`). Their existing holes are
unchanged dependencies, not holes added by this delivery. This is a proof from the
stated dependencies, not a decomposition into new obligations.

## No longer needed

Removed the redundant direct proof imports `Mathlib.AlgebraicGeometry.OpenImmersion`
and `Mathlib.RingTheory.Localization.Away.Basic`; the retained imports already provide
their APIs. No DAG dependency or Sheaf module is pruned: the original mathematical inputs
are still used. Instead of proving further localization preserves finite presentations,
the implementation intersects the already compact open with a compact basic open in an
affine spectrum. The project therefore needs no additional finite-presentation
localization comparison lemma for this step.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The DAG's product-before-support order
was replaced by an equivalent support-before-product order, using compact intersection
stability for further shrinking. The unit's route is preserved.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
