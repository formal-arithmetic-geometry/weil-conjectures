## What changed

Proved `AlgebraicGeometry.Etale.geometricStalk_torAmplitude_test` in
`Sheaf.AlgebraicGeometry.EtaleStalkTorTest` with its original signature.
A local criterion, proved uniformly for every scheme and derived object, combines
constant module tests, exact-stalk homology, the unbounded tensor/stalk comparison,
and conservative algebraic-closure points. Its pullback consequence follows by
localizing the module-valued `upperStarCompSheafFiberIso` and tensoring with M[0].
All four mathematical steps and the parent unit realization are preserved.

The node proof now describes these existing module-valued APIs directly. The theorem
and module docstrings, statement and statement dependencies remain unchanged. Removed the redundant
`prop-weil-pbc-inverse-image-modules-exact` proof edge: the proof uses the existing exact
ModuleCat-valued inverse image instead of constructing the SheafOfModules package. No new declaration or node was introduced.

Reduced the header to public `Coefficients` and `EtaleDerivedTensorStalk`, and private
`ExactFunctor` and `GeometricStalkTensorConstantSingle`. The public-import change is
recorded in `coord/changes/E1-etale-stalk-tor-test-imports.md`. There are zero current
Lean consumers, so none needs adaptation.

Validation: the original file compiled; the completed proof compiled; the reduced-import
version compiled with no errors or warnings. The proof uses no finiteness, boundedness,
nonemptiness or nonzero-ring assumption. Its conservative-family argument also applies
to the empty scheme. No new test declarations are delivered.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.geometricStalk_torAmplitude_test`
(node `lem-sf-etale-stalk-tor-test`).

Zero holes remain in the delivered module. Zero holes added; zero statements split off.
This is a proof from the existing dependencies, including
`AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso`, whose own proof remains an
existing separate item. This delivery does not claim to close that dependency.

## No longer needed

Removed direct imports:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: use the owning
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` for the bounded Tor predicate
  and the module-derived category; the torsion-cohomology extension is unused.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: the statement and proof use the existing
  `pointSmallEtale.sheafFiber`, not the separate explicit colimit presentation.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: only bounded intervals are used, defined
  already in `Coefficients`; the lower-bounded predicate is unused.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: the existing exact
  ModuleCat-valued `upperStar` and its stalk comparison suffice; the large existential
  package for the SheafOfModules encoding is unused.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`: no left/right-derived
  adjunction API is needed; use the generic exact-functor comparisons privately.
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`: unused.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: the exact-functor derived
  homology comparison supplies the required homology API.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`: their conservative-point and
  stalk-pullback APIs remain used, available through the retained public imports.

No node or whole module is withdrawn. The definition nodes remain statement dependencies;
the conservativity, stalk exactness, homology and tensor-comparison nodes remain
mathematical proof dependencies. The removed
`prop-weil-pbc-inverse-image-modules-exact` proof edge is retained as a statement dependency;
its explicit witness theorem is not invoked by the proof. No globally unreachable module count is asserted.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The stage-2 header over-imported APIs: exactness and
conservativity are already available directly for ModuleCat-valued sheaves, and the
source library already supplies the module-valued pullback/stalk natural isomorphism.
Thus the informal linearity and underlying-abelian-sheaf arguments need no new Lean
lemmas. The unit route and all hypotheses/conclusions are unchanged.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
