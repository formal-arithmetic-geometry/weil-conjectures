## What changed

Proved all five theorems in `Sheaf.Paper.IntrinsicScalarNormalizationFormulas` from
existing specifications of the published constructions. Added two proved private
normalization lemmas on the specified index models, generalized only in the final
coefficient map. Equality elimination makes the endpoint transport reflexive.
Keeping the actual coefficient models fixed avoids costly conversions of their
field structures while checking the final specializations.
Updated the owning node's proof, proof dependencies and proof origin to this route. Existing public signatures,
definitions, docstrings and public imports are preserved.

## Proved and sorry left

Closed five holes, all owned by
`lem-pur-intrinsic-scalar-normalization-formulas`:

- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicOrdinaryScalar_exact`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicOrdinaryScalarComp_tensor`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicIntegralScalarAssociator_image`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicIntegralTransition_shift`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.intrinsicRationalScalarAssociator_image`.

No sorry remains in the item. No holes or public declarations were added, and
no theorem was split off. The complete delivery module compiled without warnings
in 27.6 seconds using `lcompile.py`. All five original public signatures were
checked unchanged, and no debugging options remain.

The proofs use existing library declarations, whose
transitive axiom status remains subject to the project's global audit.

## No longer needed

Removed these unused private proof imports:

- `Sheaf.CategoryTheory.ScalarLocalization`.
- `Sheaf.Paper.CompletedIntegralFiniteFree`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Mathlib.CategoryTheory.Functor.FullyFaithful`.
- `Mathlib.CategoryTheory.Shift.CommShift`.


The proof does not reconstruct finite-free exactness, sheaf tensor associativity,
localization descent, fully faithful lifting, or normalized shift transport.
Their existing defining specifications suffice. Thus the following original
proof dependencies are no longer direct proof dependencies of this node:

- `lem-weil-completed-integral-finite-free`.
- `def-pur-sheaf-tensor-product`.
- `lem-weil-pbc-exact-functor-derived-factorization`.
- `lem-weil-pbc-localization-universal-property`.
- `def-zl-normalized-integral-scalar-comparison`.
- `lem-sfb-fully-faithful-cancel-iso-components`.
- `lem-pur-fully-faithful-composite-shift`.
- `lem-weil-integral-constructible-triangulated`.
- `def-weil-rationalization-karoubi`.
- `def-weil-linear-scalar-localization`.

The construction modules still depend on the relevant underlying theory; this
is no claim that those modules can be withdrawn globally. No module is withdrawn.
The unit record has no realized statement or proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The proof plan expanded constructions whose existing chosen-witness specifications
already state all five required conclusions before the final equality transports.
Using those specifications gives a shorter proof without changing any statement,
coefficient universe, characteristic parameter, shift convention or unit route.
No mathematical error or statement repair was necessary. Local irreducibility
attributes keep completed scalar-extension data abstract during proof elaboration;
large construction bodies are not unfolded merely to compare components. Keeping
the normalization lemmas on the actual index models also avoids costly kernel
conversions during their final specializations. The existing algebraic-closure parameter is retained even where only finite coefficient subfields are used; the
unused-section-variable linter is locally disabled to preserve these signatures.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
