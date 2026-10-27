## What changed

Filled `WeilConjectures.RationalSmoothPurityCanonical.scalarShift_existsUnique`
using the existing scalar-localization universal property and Mathlib's
`Functor.commShiftOfLocalization`. The scalar functor's pure-tensor specification
supplies its equality with the localized integral functor. Both localization
comparisons are normalized identities at degree one; explicit heterogeneous
transport gives the required component formula. Integer induction, with
cancellation through the invertible shift functor in the negative direction,
proves uniqueness of the coherent integer-shift structure.

The category argument is factored into fully proved private helpers. The concrete
proof pins the category parameters and keeps the constructed localization shift
irreducible to avoid repeated reconstruction during elaboration. The file compiles
cleanly through `lcompile.py` in 52.8 seconds. Removed the
unused `CategoryTheory.Endofunctor` namespace opening, which also shadowed the
ordinary `Algebra` notation.

Only the item module is changed. Existing public declarations, statement
signatures, definitions, and public imports stay unchanged. The two added private
proof imports are `Mathlib.CategoryTheory.Shift.Localization` and
`Sheaf.CategoryTheory.SemilinearScalarLocalization`; the latter already occurs in
the original public imports' transitive closure.

## Proved and sorry left

Starting count: four holes. Closed:

- `WeilConjectures.RationalSmoothPurityCanonical.scalarShift_existsUnique`.

Three existing holes remain, all attached to
`def-pur-canonical-purity-source-transports`:

- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_existsUnique`.
- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_isIso`.
- `WeilConjectures.RationalSmoothPurityCanonical.tensorToOrdinary_existsUnique`.

Added holes: none. This is a partial proof delivery, not a decomposition.

For the remaining descent theorem, an isolated proof was checked from the existing
fully faithful restriction along the good-representative product localization.
Transport the canonical augmentation through the ordinary representative comparison
and the completed representative comparison, then descend this natural transformation.
At a finite-Tor pair its components are invertible by `tensorAugmentation_isIso`;
`NatTrans.isIso_app_iff_of_iso` transports that fact from any good resolution.
Naturality yields exactly the displayed conjugation formula, and essential
surjectivity gives uniqueness. Finite-Tor membership transports through an isomorphism
by keeping its uniform interval and composing each scalar-reduction presentation
with the inverse isomorphism.

That draft passed in isolation, but integrating it took 83 seconds for the full
file. Profiling assigned 17.8 seconds of kernel checking to its concrete descent
proof. Keeping the representative comparison abstract with an explicit component
specification and keeping `integralCompletedTensorComparison` locally irreducible
did not lower the full-file time. The delivered file retains only the scalar proof;
the descent draft and all debugging modules/options have been removed.

A useful existing dependency for the remaining invertibility theorem is
`GeneratorReduction.finiteTorOrdinaryTensorComplete` in
`Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete`. Its ordinary tensor is computed
on the good representatives by the calculus's `integralTensorModel.iso`.
`roosIntrinsicCompletenessEquivalence` identifies completeness with invertibility
of the specified completion unit; `completionUnit_existsUnique` then identifies
that unit with the quotient Roos augmentation. The normalized `tensorTowerIso`
gives the required tensor tower. These observations do not close another hole
in this delivery.

## No longer needed

None. Both existing public imports supply statements and definitions used in this
module. No module or node is withdrawn, and the unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The owning definition node has empty `proof` and `proof_deps` fields; its Lean
docstrings contain the plans for the remaining proof obligations. The scalar
proof implements its docstring's localization and coherence argument. No
mathematical statement correction was needed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
