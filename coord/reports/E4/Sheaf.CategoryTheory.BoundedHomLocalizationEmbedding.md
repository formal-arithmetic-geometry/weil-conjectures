## What changed

Proved `CategoryTheory.boundedHomLocalizationEmbedding` in
`Sheaf.CategoryTheory.BoundedHomLocalizationEmbedding` without changing either public
signature or the definition of `RawScalarLocalizationEmbedding`.

The proof restricts `scalarLocalization_derivedHom` to the given full subcategory.
It transports its degree-zero equivalence along the full-subcategory Hom equivalence,
the zero-shift isomorphisms, and Mathlib's localization/base-change equivalence.
The resulting tensor Hom equivalences send every pure tensor `a ⊗ f` to `a • F(f)`.
These maps define the functor on unchanged objects. Tensor induction proves its
composition law, and bijectivity of its Hom equivalences proves fullness and faithfulness.
Mathlib's `LocalizedModule.equivTensorProduct` proves that every tensor is a single
power-denominator fraction. The identity and composition equations then follow directly.

Added proved private helpers and the proof import
`Mathlib.RingTheory.Localization.BaseChange`. The existing four-step DAG plan and all
its declared proof dependencies are retained. No statement, definition, public import,
consumer module, unit route, or target changes.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.boundedHomLocalizationEmbedding`
(node `lem-per-bounded-hom-localization-embedding`).

Holes added: 0. Holes left in the item module: 0. No statements split off.
The private helpers `postcompLinearEquiv`, `inversePower_eq_mk`,
`tensor_is_fraction`, `tensorHomEquivalences`, and `rawEmbedding_of_tensorHom`
are fully implemented or proved.

## No longer needed

Removed redundant private imports `Mathlib.LinearAlgebra.TensorProduct.Tower` and
`Mathlib.Algebra.Module.LocalizedModule.Basic`; the new base-change import supplies both.
All five declared proof dependencies are used, through the supplied derived-Hom
comparison, raw scalar category, linear-functor API, tensor base change and localized
module API. No modules, nodes, or maintainer-approved tool uses are pruned.
Existing public imports are retained as part of the module interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. Mathlib provides the tensor/fraction
identification planned in Step 2, so its quotient relation does not need to be reproved.
The comparison uses `LocalizedModule.moduleOfIsLocalization`, whereas the direct tensor
identification also has a native localization action; the proof explicitly uses the
former action in the base-change equivalence to keep these interfaces aligned.

The argument uses neither injectivity of the scalar nor a nonzero coefficient ring.
The same constructions cover zero, nilpotent and invertible scalars, zero objects and
empty full subcategories. The paper's full-faithfulness implication in Proposition
6.8.14(2), pp. 61–62, and the unit's realized route are preserved.

Validation: the final single-file `lcompile.py` run compiled cleanly in 36.4 seconds,
with no errors or warnings. Text checks confirm unchanged public signatures, no
remaining `sorry`, no debug traces and no lines exceeding 100 characters.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
