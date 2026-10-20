## What changed

Proved `AlgebraicGeometry.Etale.nonempty_geometricPointDerivedConstantsData` for the actual
constant-sheaf functor and the actual identity-point stalk, retaining every existing definition
and structure field. Constructed the adjunction with the prescribed constant-germ unit and
proved the counit formula and uniqueness by full faithfulness. Proved monoidality of that
canonical germ by the colimit-insertion formulas and sheafification comparison.

Added `Sheaf.CategoryTheory.ExactMonoidalEquivalenceDerived`: its proved `nonempty_data`
constructs strong derived monoidal structures, proves the prescribed localization-factor
normalizations, and proves monoidality of the termwise descended adjunction. The proof uses
the existing K-flat tensor comparison, the oplax square coherence theorem, transport along
the exact-derived comparison, and explicitly computed monoidal mates. Private structures
keep the constructed monoidal data abstract when assembling the equivalence.

Proved symmetry of the canonical Koszul derived braiding on integer complexes and transferred
it through the fully faithful derived stalk. The monoidal derived unit then proves the constant
functor's symmetry equation. Existing exact-functor cohomology lemmas preserve all lower bounds.
The new general lemma is an independent proved result, not an unfinished coherence obligation.

Change record: `coord/changes/M6-geometric-point-derived-descent.md` documents the added
helper commands flagged by preflight and both new public helper declarations; the three
existing consumers need no adaptation.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.nonempty_geometricPointDerivedConstantsData`.
Added zero holes. Both delivery modules contain zero `sorry`.
The new `CategoryTheory.ExactMonoidalEquivalenceDerived.nonempty_data` and all private helpers
are proved. No decomposition into unfinished statements remains.

Validation: sandbox import-order compilation passed without warnings: the general descent
module compiled in 39.8 seconds and the geometric-point module in 32.6 seconds.

## No longer needed

Removed the proof-only imports:

- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`

The adopted `Scheme.isEquivalence_constantSheaf_of_isSepClosed` gives the field-point
constant-sheaf equivalence directly. Thus this proof does not use
`lem-exc-abelian-sheaves-gmodules`, its Galois-group detour, or its module. The actual point's
existing fiber and constant-fiber isomorphism handle the stalk and germ directly, so no separate
pointed-stalk module or site-tensor universe construction is needed here. The existing source
library's functorial K-flat resolution and derived tensor comparisons supply the tensor descent;
this proof does not use the independent-coefficient ringed-site resolution theorem
`lem-pc-kflat-resolution` or its module. Both obsolete tool-use entries were removed from this
node. These are dependencies pruned from this proof; other consumers may still need them.
No adopted source declaration or module was removed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped with the derived tensor coherence unfinished. The existing
oplax-square and derived-comparison APIs supply the construction once its factor normalizations
are proved explicitly. The Galois-module route in the DAG is longer than the adopted direct
constant-sheaf equivalence. The unit's route and all target statements remain the same.

During development an unlanded provisional coherence statement omitted the requirement that
its adjunction unit was the canonical germ. An arbitrary sign-twisted unit need not be monoidal;
that provisional statement and its node were removed. The delivered proof constructs the
canonical adjunction first and proves its unit monoidal before deriving it. No such assumption
is left implicit. The abstract descent lemma assumes a monoidal counit and invertible unit and
counit, so it also handles this issue correctly.

Edge cases: the constructions require no boundedness or nonzero-complex assumptions; direct-sum
tensor formulas include zero summands and all integer bidegrees. The square of the Koszul sign
is one in every bidegree, and exact equivalences preserve every lower bound, not only degree zero.

## New nodes

`new-lem-kun-exact-monoidal-equivalence-derived` records the fully proved abstract monoidal
adjoint-equivalence descent theorem in its new module. The original item's node now records
the actual constant-germ construction, this descent theorem, and the transferred Koszul symmetry.
Blueprint search for monoidal equivalence found only restriction/change-of-scalars and trace
formula nodes; none states this localization-factor and adjunction coherence result.

The new-node search record includes LeanSearch, separately from the LeanFinder/Loogle
searches and the Mathlib source grep, as required by the three-kind search rule.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
