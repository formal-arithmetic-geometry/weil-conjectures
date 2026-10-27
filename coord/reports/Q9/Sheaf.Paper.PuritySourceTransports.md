## What changed

Proved `WeilConjectures.RationalSmoothPurityCanonical.tensorToOrdinary_existsUnique`
from the existing strict augmentation and its finite-Tor invertibility theorem.
Fully faithful restriction to pairs of good representatives descends the augmentation,
conjugated by the ordinary and completed representative comparisons. Naturality
identifies the inverses of all transported comparisons; essential surjectivity supplies
representatives, and the normalization proves uniqueness.

Added fully proved private category lemmas for descent, inverse comparison and
transport, and product normalization, and a private proof that finite-Tor membership
transports across isomorphisms without changing its uniform interval. The abstract
descent lemma obtains full faithfulness and essential surjectivity from localization.
The concrete proof supplies the existing good-localization theorem. The complete
augmentation-descent construction is factored through the private, fully proved
`tensor_comparison_from_augmentation` over abstract categories, so that its kernel
check does not repeatedly expand the concrete sheaf data.

The ordinary comparison is restricted componentwise, retaining the model's original
representative maps and naturality proof. The tensor proof uses inverse components,
which contain the forward augmentation map rather than a chosen inverse. Local
irreducibility annotations keep large comparison constructions folded; the small
good-localization functor is locally implicitly reducible. Both transparency-respect
settings remain enabled. Sequential elaboration avoids concurrent checking overhead,
and the known algebra-module instance is prioritized. The total-complex constructor
and standard integral derived-category instance are locally implicitly reducible.
The augmentation normalization predicate remains locally folded after its construction.

The `ordinaryTotal` definition uses the definitionally identical signed total
presentation of `ProEtaleTensorModel`, with an explicit functor type. Using `def`
instead of `abbrev` avoids automatic expansion of the total-complex constructor.
No public theorem signature changes. Its 118
transitive importers have no direct use of the abbreviation and require no adaptation.
The original ordinary-model construction is factored through the fully proved private
`ordinary_model_from_comparison`, abstracting the coefficient sheaf and its recorded
comparison. The concrete theorem keeps its original statement and supplies its existing
calculus data once. The existing scalar-shift proof reuses the proved private
`rationalLocalizationShift_hom` for both coefficient fields and spells out its localized
integral-shift goal before applying the abstract lemma. The owning DAG node records
the tensor descent argument.

Proof imports added: `Sheaf.Paper.IntegralOperationsWellDefined` (including its proved
private good-localization theorem) and `Mathlib.CategoryTheory.Localization.Prod`.
The constructible isomorphism-closure instance is already publicly available through
`SfIntegralConstructibleLinear`. The known sheafification-adjoint projection is
prioritized alongside the algebra-module instance to avoid unnecessary class searches.

Validation: the final source passed `lcompile.py` cleanly in 56.5 seconds. The
delivery compiles it with the axiom probe and runs preflight. All profiler and trace
commands have been removed.

## Proved and sorry left

Starting holes: 3. Closed: 1,
`WeilConjectures.RationalSmoothPurityCanonical.tensorToOrdinary_existsUnique`.
Added holes: 0. Split off: 0. This is a partial proof delivery, not a decomposition.

The two unchanged holes remain under `def-pur-canonical-purity-source-transports`:

- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_existsUnique`.
- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_isIso`.

## No longer needed

None. The existing public imports and all public declarations remain needed. No module
or node is withdrawn and no unit step is bypassed. No additional mathematical theory
is needed for representative independence beyond the existing localization theorem.

## Where the brief, the DAG or earlier work was wrong

The owning definition node had empty proof and proof-dependency fields; the declaration
itself supplied the descent plan in its docstring. Those fields now record the formal
argument. No statement correction was required. The old ordinary-total presentation forced
repeated conversions to the model presentation; the definitionally identical expression
now shares that presentation. Change record:
`coord/changes/Q9-purity-ordinary-total-presentation.md`.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
