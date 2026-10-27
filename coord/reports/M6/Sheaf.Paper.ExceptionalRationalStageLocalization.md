## What changed

Replaced the hole in `exists_rational_stage_localization` by a construction from the supplied
integral operations and their scalar mates. The existing theorem signature, assembly record,
and `RationalStageAssembly.fields` are unchanged.

The new `ExceptionalIntegralAdjunctionLocalization` module constructs the proof-changing
integral representative functor, its full-domain extension, and both raw rational functors.
Their arrow maps are the base changes of the original integral linear Hom maps. The tensor
identity and composition laws are proved. Its remaining theorem concerns only the adjunction,
exact structures and identity localization comparison for these fixed functors.

The new `ExceptionalScalarMateLocalization` module states localization of one supplied
integral scalar mate, without a compactification, compact-support realization, assembly family,
or common-field descent.

In the item module, the rational compact-support realization is constructed componentwise
from the localized `A.integralLeft`. Its naturality is proved on pure tensors using integral
naturality and the tensor composition formula, then on all arrows by tensor induction. The
normalization, raw action on objects and integral arrows, and independence of the endpoint
localization shifts are proved in the assembly argument. Residue-field invertibility is
constructed from the finite base field and the existing residue-Tor theorem is used.

All added imports of the item are proof imports. No other existing Lean module or interface
is changed. The current source and its Lean attachment are preserved, including the module
listed in the rework table; no quarantine archive is removed.

Validation: `lcompile.py --all` accepted all three modules with exit code zero and no
warnings. All profiling options and temporary check modules were removed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_stage_localization`.
The item has zero remaining holes. This is a decomposition, not an unconditional proof:
one original hole was replaced by two strictly smaller algebraic obligations.

Added holes, each the complete body of a named public theorem with source and proof in words:

- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_integral_adjunction_raw_localization`
  (`lem-sf-integral-adjunction-raw-localization`): adjunction and exact structures on the
  explicitly constructed raw functors, plus their identity localization comparison.
- `WeilConjectures.ConstructibleExceptionalCoefficients.exists_integral_scalar_mate_localization`
  (`lem-sf-integral-scalar-mate-localization`): localization of one integral counit square
  between those already supplied adjunctions.

The raw functor data contain no holes or existential choices. Choosing the two remaining
structures does not choose an arbitrary coefficient object or arrow action: those are fixed
by the explicit Hom base changes, and the comparison components are prescribed identities
or localized supplied components. The scalar endpoint shift isomorphisms are also
prescribed on every integral representative and every integer shift by localization of
the given integral scalar shifts, so these data are determined. The identity localization
components force the rational counit to be the localized integral counit, determining the
adjunction. Their shift equations and the fixed endpoint shifts determine the raw operation
shifts on every integral representative. The predicate equalities make these representatives
cover all rational objects.

## No longer needed

No original import was removed, and no existing module is withdrawn. The following original
proof dependencies of this item are unused and removed from its node's proof plan:

- `lem-sf-exceptional-field-descent` / `Sheaf.Paper.ExceptionalFieldDescent`: no common-field
  output or separately normalized compact-support adjunction is needed.
- `lem-pur-coefficient-scalar-units` / `Sheaf.Paper.RingedCoefficientScalarUnits`.
- `lem-pur-ringed-coefficient-projection-cocycle` /
  `Sheaf.Paper.RingedCoefficientProjectionCocycle`.
- `lem-sf-open-tensor-normalization` / `Sheaf.SixFunctors.OpenTensorNormalization`.

The last three are unnecessary because this theorem asks for individual scalar comparisons,
not their identity or composition coherence. The given `A.comparison` is localized as it
stands. These modules may remain needed by other items; this delivery does not withdraw them.

`lem-coef-integral-residue-tor` is retained. The proof uses
`def-weil-compact-support-finite-action` for the actual rational Hom action. The unit route
and all `dag/units/` records are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement correction is made. The previous plan routed through field descent and
proper/open coherence unnecessarily for this output record. The replacement isolates the
single-adjunction and single-mate algebra, while proving the compact-support realization
and family assembly here rather than moving the original statement under another name.

The new statements were checked on the empty endpoint schemes, zero Hom modules, identity
coefficient embeddings, and repeated coefficient fields. They impose no absolute separatedness,
nonemptiness, unramifiedness, or additional geometric hypothesis. Membership changes affect
only proof fields. Tensor balancing uses the given integral linearity; the rational scalar
functor already uses the coefficient localization map valid for ramified extensions.

## New nodes

`lem-sf-integral-adjunction-raw-localization`, in the item's chapter and unit, records the
single-adjunction localization obligation and attaches the explicit supporting raw functor
constructions. It has no finite-field datum, morphism of schemes, compactification family,
or prescribed compact-support realization.

`lem-sf-integral-scalar-mate-localization`, in the same chapter and unit, records localization
of one already supplied integral mate. Its hypotheses include both already localized
adjunctions, their identity localization components and canonical endpoint localization
shifts, and the actual ambient scalar functor equalities. Its conclusion has no compact-support realization or family coherence.

Both nodes cite Zheng, Constructions 6.1 and 6.2, and carry complete proof plans and the actual
LeanSearch, Loogle, LeanFinder and source-grep search results. Blueprint-wide searches for
adjunction localization, scalar mates and linear adjunctions found no matching existing node.
The nearest blueprint ancestor is `sk-thm-sf-tensor-hom`; these are its coefficient and shift
compatibility step, through the existing coefficient-construction chain. No change record
is needed because no existing statement or definition is changed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
