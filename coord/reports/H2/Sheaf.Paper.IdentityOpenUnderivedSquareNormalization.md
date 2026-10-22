## What changed

Proved `identity_open_underived_square_normalization` without changing its statement or
any published definition. The proof uses the existing identity-open restriction theorem
for its sectionwise restriction clauses, proves bijectivity of the module coprojections
through the canonical slice-restriction isomorphism and extension of scalars, and proves
the unit equation formally from mates and the identity compositor. Naturality gives the
adjunct equation and the tensor-unit section formula. The primed identity locus follows
from the universal properties of the two chosen pullback squares. Three applications of
the component form of `upperStarComp_assoc`, promoted to natural-isomorphism equations,
establish the square equality in the functor category. Evaluation and functoriality
preserve it on modules, complexes and ordinary unbounded derived categories.

All additional mathematical lemmas are private and proved. No other module is modified.
The private normalization code makes proof irrelevance explicit when structural instances
occur in the predicate through cached proof constants but in theorem types through their
expanded constructions. It matches the cached proofs at their individual positions, since
the coefficient construction and the predicate retain different proofs of `Precoherent`. It constructs ordinary `Subsingleton.elim`, `congrArg`, and
`Eq.mp` proof terms, which undergo the usual kernel check. The private import
`Mathlib.Tactic` supplies the metaprogramming API. This changes no public construction
or statement. Private helper types use the source library’s `Ab` alias to keep their
inferred category data aligned; the published statements retain their original text.
The complete candidate compiled in 15.7 seconds with the standard compiler limits.
The unit-route import `Sheaf.Paper.CartesianCoefficients` and its DAG dependency are
retained. The proof-command change record is
`coord/changes/H2-identity-open-normalization-proof-commands.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.identity_open_underived_square_normalization`.
No holes added; no holes remain in the delivered module. The proof uses the existing
`identity_open_derived_restriction` declaration, whose independent proof remains assigned
in its own module. This is a proof from an existing dependency, not a new decomposition.

## No longer needed

The following original proof dependencies are no longer separate inputs to this proof.
The existing identity-open restriction theorem supplies the restriction and section
clauses; source-library coherence supplies the compositor laws. No upstream declaration
is removed or made sorried, and these nodes can still be required by other consumers.

- `lem-weil-proetale-weakly-etale-localization`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `def-sfb-finite-lower-star`
- `lem-weil-pbc-localize-ringed-site-morphism`
- `lem-sfb-eta-comp`
- `lem-pur-ringed-site-pullback-localization-universes`
- `def-sfb-module-lower-star-comp`
- `def-sfb-finite-lower-star-comp`
- `def-weil-pbc-composite-adjunction`
- `lem-weil-pbc-mate-pasting`
- `def-weil-pbc-adjunction-conjugate`
- `det-prop-sfb-module-pullback-exact-main`
- `sk-def-sfb-derived-categories`

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`

Added the explicit proof import of the existing abelian slice-restriction comparison
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier` for the inverse-image locus.

## Where the brief, the DAG or earlier work was wrong

The source library already proves the pullback compositor associativity and identity
laws. The DAG's sectionwise conjugation argument for those laws can therefore be replaced
by these existing proved declarations. The exactness theorem import is unnecessary:
the source functors already carry the instances required by the derived mapping API.
The existing identity-open restriction theorem also supplies the invertibility and
explicit section formula directly.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
