## What changed

Proved `AlgebraicGeometry.Etale.scalarPullback_composition` with its original statement
and public import. The proof reuses the proved private `scalarPullback_eq` identification
from `EtaleProEtaleScalarMate`, accessed by a private `import all`. That identification
expresses the normalized comparison as the inverse scalar-adjunction mate.

The existing derived restriction-square composition theorem supplies the square to transpose.
Private proved helpers transport the unit equation to exact derived inverse image and paste
the three scalar-adjunction transposes. Injectivity of the Hom bijection proves composition
of the inverse comparisons; cancellation gives the stated forward equation. Explicit types
for the restriction comparison prevent its localization constructions from unfolding during
this calculation. All added helpers are private and proved; no other module is changed.
The complete module compiled through `lcompile.py` in 16.0 seconds with zero holes;
the delivery tool performs the final compile and preflight.
The proof-local command changes and all consumers are documented in
`coord/changes/K5-scalar-pullback-composition-proof-scopes.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.scalarPullback_composition`
(node `lem-sf-scalar-pullback-composition`), the item's sole original hole.
Added holes: none. Remaining holes in the delivered module: none. Split statements: none.
The proof uses existing declared dependencies, including
`ProEtale.scalarPullbackReverse_isIso` through the imported normalized-mate identification.
Its module is already in the current `TargetsCheck` import closure.

## No longer needed

Removed these explicit proof imports:

- `WeilConjectures.CategoryTheory.AdjunctionSquareComposition`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`;
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit`;
- `WeilConjectures.CategoryTheory.Sites.ReductionFlat`;
- `WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic`;
- `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`;
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`;
- `Sheaf.Paper.EtaleUnboundedRestrictionComparison`;
- `Sheaf.Paper.KFlatRingedToposPullback`.

The scalar-mate identification already supplies normalization, so this proof does not
rebuild representatives, choose flat resolutions, prove general K-flat preservation,
or verify ordinary scalar-extension composition on tensor generators. Consequently
`lem-pc-kflat-resolution` and `lem-weil-pbc-ringed-pullback-preserves-kflat` leave this node's
direct proof dependencies. The exact geometric compositor uses the ordinary inverse-image
composition and the source-library derived-square API, so
`lem-weil-pbc-inverse-image-composition-module-linear` also leaves the proof dependencies;
its statement dependency is preserved. The two private proof imports provide the interfaces
that the final proof actually uses. No module is withdrawn and no upstream declaration is
removed; dependencies still used inside other modules remain there.

## Where the brief, the DAG or earlier work was wrong

The planned representative calculation can be replaced by the existing proved identification
with the inverse scalar mate, followed by the already proved composition of derived
restriction squares. That identification holds for arbitrary coefficient rings, so this
route adds no coefficient finiteness, flatness, or boundedness assumption. No false statement,
definition repair, or change to the unit's route was required. The node copy records the
final mate argument and its actual dependencies.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
