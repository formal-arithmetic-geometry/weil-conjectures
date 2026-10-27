## What changed

Completed `AlgebraicGeometry.Etale.etaleProperOpenExchangeCube`, preserving its full
statement and both comparison-family definitions. The proof reuses the existing
proved arbitrary-scheme private construction, vertical-pasting and identity helpers
from `UnboundedProperOpenInterchange`, `UnboundedProperOpenComposition` and
`UnboundedProperOpenPasting`. All added imports in the existing item are private
proof imports; its public imports are unchanged.

Added three fully proved source results under `Sheaf.AlgebraicGeometry`: Cartesian
mate normalization, horizontal pasting, and the arbitrary-base-change cube. Their
common normalization predicate says that the derived comparison carries the
right-derived units to the termwise sheaf comparison. The chosen derived construction already
satisfies this equation and the stronger displayed representative formula.

The cube proof first proves equality of the ordinary sheaf maps by their monic
inclusions into a common direct image. A generic right-derived extensionality
argument then lifts that equality. Derived adjunction-mate and square-factorization
formulas identify the specified exchanges and inverse open-base-change maps.
No base-change exchange is cancelled. No Noetherian hypothesis is introduced.

Updated the parent's proof route and added matching nodes for the three proved
normalization results. No source-library declaration or consumer is modified.

Private generic wrappers keep the unit-normalization predicate intact at concrete
call sites. The representative formula follows from the unit equation and is
inverted in a generic category before instantiation. The construction’s unit
equation is also extracted generically. The proper identity uses the canonical
exact-derived identity compositor. This avoids repeated unfolding of the concrete module-sheaf structures.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Etale.etaleProperOpenExchangeCube`
(`lem-pur-etale-proper-open-exchange-cube`).

Also proved `AlgebraicGeometry.Etale.etaleProperOpenCartesianNormalization`,
`AlgebraicGeometry.Etale.etaleProperOpenHorizontalNormalization`, and
`AlgebraicGeometry.Etale.etaleProperOpenCubeNormalization` in their new modules.
The public predicate `ProperOpenUnitNormalized` is an explicit proposition, with
no postponed data. Every private helper is proved.

Original holes: 1. Closed: 1. Added: 0. Remaining in all four delivered modules: 0.
The final item compiled without errors or warnings (58.0 seconds); the revised
Cartesian normalization compiled without errors or warnings (15.2 seconds).
No theorem is split off with `sorry`. Existing imported dependencies keep their
existing proofs and assumptions; closing this item does not claim to close those
independent dependencies.

## No longer needed

Removed the following direct proof imports from the item:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.AlgebraicGeometry.DerivedCounitKInjectiveTermwise`
- `Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleModuleStalkCohomologyTest`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic`
- `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`
- `Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

These modules are not claimed to be globally prunable: the reused construction or
the new normalization proofs still use portions of their APIs transitively. No
module or node is withdrawn. No unit statement or realized proof step is bypassed.
The parent now records the actual three normalization dependencies and the reused
construction/pasting modules, instead of scheduling the original representative
argument independently in this module.

The simultaneous-resolutions argument in the old cube plan is unnecessary here:
right-derived extensionality and exact factorization suffice. In particular the
new cube does not use the representative-level K-injective map-lifting theorem
or the derived-extension-zero underived-compatibility theorem as direct lemmas.
Those existing declarations remain untouched.

## Where the brief, the DAG or earlier work was wrong

The public analogous proper/open coherence results assume Noetherian schemes,
whereas this item's quantified schemes are arbitrary. Their already proved
private generic construction and vertical/identity helpers have the generality
needed here, so the proof imports those helpers and supplies the missing general
Cartesian, horizontal and cube arguments. It never applies the restricted public
statements to arbitrary schemes.

The draft new-node records had inherited an obsolete unit and had described
representative normalization even after the proofs adopted unit normalization.
The delivered records use the parent's current `sk-prop-sf-cbc` unit and state the
actual normalization. Their blueprint ancestry points to the current
`prop-asd-smooth-base-change` proof, coherences (i) and (iii), with the parent route
recorded through `via`. This retains the compact-support base-change route.

The support-normalized sheaf choice is unique: its inclusion into the common
direct image is monic. Thus choosing it from the existing proved existence result
satisfies the project's object-determination rule. The derived comparison comes
from the existing explicit `constructedDerivedComparison`, not an arbitrary
witness of an unproved existence assertion.

## New nodes

`lem-pur-etale-proper-open-cartesian-normalization` records the proved identification
of any support- and unit-normalized comparison with the specified Cartesian mate.
Its proof uses monicity and the derived adjunction-mate unit equation.

`lem-pur-etale-proper-open-horizontal-normalization` records the proved horizontal
pasting identity. Its explicit unit-normalization predicate is shared with the
cube result. Its proof combines ordinary support pasting, exact compositors, and
right-derived uniqueness.

`lem-pur-etale-proper-open-cube-normalization` records the proved arbitrary-base-change
cube. Its proof has a generic exact-functor cube argument and an ordinary sheaf
cube argument, followed by verification of the specified transformations.

The first delivery attempt stopped before pushing because the cube module timed
out. Its two concrete conversion proofs were replaced by generic private lemmas
and an explicit private exact-square normalization predicate. The public cube
statement and its proof dependencies are unchanged.

No change record is needed: existing statements, definitions and public imports
are unchanged, and no other group's module is adapted.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
