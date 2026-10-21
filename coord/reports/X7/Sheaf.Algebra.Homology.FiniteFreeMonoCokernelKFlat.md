## What changed

Proved `CochainComplex.finite_free_mono_cokernel_kflat` with its original signature
and constructions unchanged. The supplied cokernel gives a short exact sequence;
Mathlib proves its single-complex cone augmentation is a quasi-isomorphism and
normalizes its composite with the target inclusion. The cone differential formula
proves the final positive-sign equation.

A proved private finite-coproduct lemma establishes flatness using exact finite
biproducts. The regular module is the tensor unit, and the specified isomorphisms
transport flatness to both source objects. Canonical cone component isomorphisms
and zero-object flatness establish all termwise assertions, including rank zero.
The existing independent-universe bounded-flat theorem establishes all three
K-flatness assertions and hence the specified resolution.

Updated the existing node's proof and proof dependencies to match these arguments.
No public declaration, definition, attribute or public import was changed.

## Proved and sorry left

Closed the one existing hole:
`CochainComplex.finite_free_mono_cokernel_kflat`
(node `lem-sfb-finite-free-mono-cokernel-kflat`).
No holes were added or split off. No `sorry` remains in the delivered Lean module.
The private helper `flat_finite_coproduct` is proved.

## No longer needed

Removed private imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the argument uses complexes directly.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`: use the existing
  independent-universe closed structure from
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` instead. The generic
  tensor-closed node remains needed, as does the tensor unit.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`
  (node `lem-pc-sites-modules-coproduct-flat`): its same-universe general coproduct
  theorem is unnecessary. The private finite-family proof uses exact finite biproducts
  directly and works in the universes of the assigned theorem.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
  (node `lem-pc-bounded-above-flat-kflat-site`): replaced by the already proved
  `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
  (node `lem-weil-pbc-independent-bounded-flat-kflat`).

Removed the last two obsolete entries from the node's top-level `tool_uses` list.
No module is withdrawn; these modules may remain needed by other parents.
The integral-models unit's statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned coproduct-flatness and bounded-above-flat APIs assume the site and
coefficient universes coincide. The assigned theorem permits independent universes
and only relative essential smallness. The finite-coproduct argument and the
existing independent-universe bounded-flat theorem implement the same mathematical
route without adding any hypotheses or changing the conclusion.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
