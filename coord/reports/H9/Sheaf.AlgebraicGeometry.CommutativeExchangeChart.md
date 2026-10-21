## What changed

Proved `AlgebraicGeometry.Etale.commutativeExchangeChart` without changing its
statement or any existing definition. The proof uses raw derived-Hom classes
instead of choosing further injective resolutions. Three new modules construct
the canonical raw transport and prove its compatibility with higher-image
classes and with geometric chart evaluation. Coefficient and test-object
naturality follow from actual adjunction and sheaf-map naturality.

The item node now records this route. No source-library declaration is changed.
All four delivery modules compile without errors or warnings through
`lcompile.py --all`; the original statement and six definitions were checked
verbatim against the shared source.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.commutativeExchangeChart`.

New proved theorems:
`AlgebraicGeometry.Etale.commutativeExchangeClassCompatibility` and
`AlgebraicGeometry.Etale.commutativeExchangeEvaluationCompatibility`.
The raw source isomorphism and pullback are explicit constructions.
`commutativeExchangeTransport` constructs the single and shift transport for an
arbitrary exact additive functor; `commutativeExchangeTransport_def` gives its
explicit formula. The construction is irreducible so geometric applications
use this interface. `commutativeExchangeEvaluation` and its formula theorem
cache the explicit point evaluation by the same single and shift comparisons.
Transport and evaluation are also bundled as additive group morphisms, with
proved application formulae.
`commutativeExchangeEvaluationHom_rawComparison` identifies the native raw
comparison with this bundled evaluation, caching its definitional presentation
in the evaluation API. The evaluation compatibility theorem equates these
morphisms; the chart theorem applies the equality to its raw class. Explicit
source and target types on the cohomology and coefficient maps keep their
canonical group presentations consistent.
Its generic argument obtains degree-zero naturality from the derived single-unit
identity before specializing to the chart schemes.

Holes closed: 1. Holes added: 0. Holes left in the delivery: 0.
The proof uses the existing library interfaces; this does not assert that all
transitive dependencies have already been proved without sorry.

## No longer needed

The explicit-resolution proof route is replaced. In particular the item does
not separately invoke enough injectives, bounded-below injective representatives,
K-injective Hom lifting, or preservation of injectives by etale restriction.
Their source-library declarations and existing consumers remain in the library.
No module is withdrawn, and no claim is made that these modules are globally
unreachable.

The item's old proof-dependency edges are replaced by the raw inverse-evaluation,
raw transport, mate/class compatibility, chart-evaluation compatibility, and
higher-direct-image comparison dependencies recorded in its updated node.
All old `tool_uses` approvals except
`sbc-lem-higher-direct-image-presheaf` are removed from this node: the lower
comparisons now carry the exact-functor, composition and restriction arguments.
The coefficient and test-object naturalities use naturality rather than the
resolution-level cohomology-pullback functoriality argument.

The removed direct dependency edges are listed explicitly below. Exact inverse
image, mates, fibre products and restriction comparisons still occur inside the
new proved comparison modules; those edges are recorded there. The resolution
existence and injective-representative steps are not used by this argument.

- `def-pc-fibre-product`: handled by the new raw-transport and compatibility interfaces.
- `def-weil-pbc-adjunction-mate`: handled by the new raw-transport and compatibility interfaces.
- `def-weil-pbc-cohomology-pullback`: handled by the new raw-transport and compatibility interfaces.
- `def-weil-pbc-derived-inverse-image`: handled by the new raw-transport and compatibility interfaces.
- `def-weil-pbc-direct-image`: handled by the new raw-transport and compatibility interfaces.
- `def-weil-pbc-etale-cohomology`: handled by the new raw-transport and compatibility interfaces.
- `def-weil-pbc-inverse-image`: handled by the new raw-transport and compatibility interfaces.
- `lem-weil-pbc-cohomology-pullback-functorial`: naturality is proved directly from adjunction and sheaf morphisms.
- `lem-weil-pbc-derived-inverse-image-composition`: handled by the new raw-transport and compatibility interfaces.
- `lem-weil-pbc-dplus-injective-representative`: the raw derived-Hom route avoids this resolution step.
- `lem-weil-pbc-etale-base-change-finite-limits`: handled by the new raw-transport and compatibility interfaces.
- `lem-weil-pbc-etale-inverse-image-restriction`: handled by the new raw-transport and compatibility interfaces.
- `lem-weil-pbc-etale-restriction-injectives`: the raw derived-Hom route avoids this resolution step.
- `lem-weil-pbc-exact-functor-complex-cohomology`: handled by the new raw-transport and compatibility interfaces.
- `lem-weil-pbc-inverse-image-composition`: handled by the new raw-transport and compatibility interfaces.
- `lem-weil-pbc-kinjective-hom-derived`: the raw derived-Hom route avoids this resolution step.
- `lem-weil-pbc-module-sheaves-enough-injectives`: the raw derived-Hom route avoids this resolution step.
- `prop-weil-pbc-derived-inverse-image-adjunction`: handled by the new raw-transport and compatibility interfaces.
- `prop-weil-pbc-inverse-image-exact`: handled by the new raw-transport and compatibility interfaces.

Removed proof imports are listed below; their declarations remain available in
the library and necessary dependencies are imported by the comparison modules.

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.CategoryTheory.Limits.MorphismProperty`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`

## Where the brief, the DAG or earlier work was wrong

The planned explicit-resolution route is valid but unnecessary given the
adopted raw derived-Hom evaluation interfaces. The statement, including its
lack of a cartesianness assumption, is preserved. The induced square of chart
schemes over g' is cartesian even when the original square is not; its inverse
is constructed by the fibre-product universal properties. The unit's route is
preserved. No statement or definition repair was necessary.

## New nodes

`def-kun-commutative-exchange-raw-pullback` records the explicitly constructed
source isomorphism and raw class transport, in
`Sheaf.AlgebraicGeometry.CommutativeExchangeRawPullback`.

`lem-kun-commutative-exchange-class-compatibility` records the raw-class
calculation of the derived exchange mate, in
`Sheaf.AlgebraicGeometry.CommutativeExchangeClassCompatibility`.

`lem-kun-commutative-exchange-evaluation-compatibility` records compatibility of
raw evaluation with the actual geometric chart cohomology pullback, in
`Sheaf.AlgebraicGeometry.CommutativeExchangeEvaluationCompatibility`.

All three are proved here. The change record
`coord/changes/commutative-exchange-chart-proof-context.md` documents the added
file-level proof elaboration commands flagged by the static interface check.
It records the unchanged theorem signature and six definition bodies, the
absence of current Lean importers, and the two planned DAG consumers. No
existing statement, definition, public import or other module's proof changes.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
