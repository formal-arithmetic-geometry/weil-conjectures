## What changed

Proved AlgebraicGeometry.Scheme.RingedRestrictionExchange.degreeZero_normalization
from exchange_chainUnit. A private degreewise single-complex calculation, naturality
of the cochain unit and naturality of localization comparisons give the formula.
A native-category specialization fixes the module-sheaf instances while keeping
the functors variable. The fifth node proof step records this shorter route.

The theorem now expresses its exact previous equality through the transparent
proposition DerivedDegreeZeroExchangeEquation, with the same four canonical
comparison maps as explicit arguments. Expanding that proposition gives the old
equality, with identical hypotheses and conclusion. It contains no proof hole or
chosen data. The mathematical node statement is unchanged. This interface refactor
avoids expensive concrete kernel conversions; its change record is
coord/changes/c5-ringed-degree-zero-normalization.md.

The existing complete open K-injective proof is generalized to a functor-level
preservation instance in ProEtaleOpenPullbackKInjective. A second proved instance
in RingedUpperOpenPullbackKInjective specializes it to the upper map in a Cartesian
square over an open immersion. The item publicly imports this API. Both existing
complex-level theorem signatures remain; the library's generic map-complex instance
supplies their former instance inference. A generic cancellation lemma shortens
open_representative. These changes add no holes.

Profiling also identified the large OpenCube structure as costly. Its fields and
four face definition bodies move verbatim to RingedRestrictionOpenCube, publicly
re-exported by the item. All names, visibility, signatures, bodies and reducibility
are retained; its new definition node owns the five declarations. The separate
change record is coord/changes/c5-open-kinjective-preservation-api.md.

The file locally prioritizes the coefficient-universe local-bijection proof and
the native derived-category instance. The alternative reduction-module instance
also constructs HasDerivedCategory.standard. These priorities are not exported.
Only direct image needs its local semireducibility restored after degree-zero
normalization; no exported reducibility attribute changes. Existing data
construction bodies, all other mathematical assertions, and the source library
are unchanged. No Challenge target changes.

The downstream-use tool reports zero downstream modules. Direct-import search
finds none. Both named preservation theorems are used only inside the item. The
four DAG citers were checked, including unfinished parents:
lem-sf-native-weil-proper-natural-base-change,
lem-sf-continuous-adic-proper-base-change-restriction,
lem-zl-field-shriek-integral-component-naturality, and
lem-sfb-condensed-exchange-one-open-restriction.
They retain the same mathematical normalization and open-restriction clauses.
There are no unchanged Lean importers to compile or forced adaptations.

Validation through lcompile.py: the item compiled in 47.0 seconds after extraction;
the cube module in 12.1 seconds, native open preservation in 13.0 seconds, upper
preservation in 7.5 seconds and the equation definition in 2.8 seconds. Temporary
profiling options and one unused simp argument were removed for delivery. The
delivery tool performs the final compilation of the exact packet.

## Proved and sorry left

Closed one of seven original holes:
AlgebraicGeometry.Scheme.RingedRestrictionExchange.degreeZero_normalization.
Added zero holes and split off zero holed statements. All four added modules have
zero holes. This is a partial proof delivery, not a decomposition.

Six original holes remain, all owned by
lem-sf-ringed-restriction-exchange-open-descent in namespace
AlgebraicGeometry.Scheme.RingedRestrictionExchange:

- open_comparison
- open_sectionwise
- openCube_exists
- open_restriction
- open_descent
- identity_normalization

Each retains its original statement, source and complete proof in words.

## No longer needed

Removed these unused direct public imports:

- Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
- Sheaf.Paper.CondensedAmbientExchange
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

The remaining arbitrary-ring operations and ordinary right-derived APIs suffice;
none of these three extra interfaces occurs in the statements or proofs. No DAG
node or existing module is withdrawn: the definition owners remain needed.

Six proof imports move to the new native open preservation module: private
ProEtaleOperations, ScalarExtensionRingIso, RightDerivedFunctor.FullyFaithful,
ProEtaleRingedOpenComparison, RingedDerivedRestrictionGeneral, and
KInjectiveRestrictLocalizedOfUniverses. Their mathematics is still used, so they
are not pruned dependencies. The remaining clauses still need the original proof
dependencies. Step five avoids separately choosing K-injective resolutions and
comparing their composites, by using the existing cochain-unit equation instead.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. Step five is shorter using exchange_chainUnit.
The source-library rightDerivedBaseChange_single_unit is bounded below and does
not directly give this unbounded statement. Concrete kernel conversions, instance
registration and the large cube structure made the unsplit implementation approach
the time limit. Generic proofs, functor-level preservation, matching local instance
priorities and extracting the unchanged structure address those costs.

## New nodes

- def-sf-derived-degree-zero-exchange-equation: transparent notation for the exact
  normalization equality with all four comparison maps explicit; zero holes.
- lem-sf-proetale-open-pullback-preserves-kinjective: fully proved functor-level
  version of the existing complete open preservation proof; zero holes.
- lem-sf-upper-open-pullback-preserves-kinjective: fully proved specialization to
  the upper open base change; zero holes.
- def-sf-ringed-restriction-open-cube: owns the existing structure and four face
  definitions, extracted verbatim for per-file compilation; zero holes.

The first is notation; the last is relocation of existing data. The middle two
factor already proved preservation arguments, not any of the remaining holes.
Searches found generic single-complex, localized restriction and functor
preservation APIs, but no native versions of these interfaces. All new nodes are
strictly below the unchanged unit route and their source/ancestor chains are
recorded. The item node proof and dependency lists follow the implementation.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
