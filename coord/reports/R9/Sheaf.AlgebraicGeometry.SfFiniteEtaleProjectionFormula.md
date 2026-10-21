## What changed

Proved `AlgebraicGeometry.Etale.sf_finite_etale_projection_formula` with its signature unchanged.
The proof uses the existing unbounded torsion-ring proper projection formula for the proper
factor of the given compactification and the published component formula, so it proves
invertibility of the specified map. Bounded-below membership follows from exact open extension,
left t-exact derived pushforward, the finite Tor amplitude tensor estimate, and transport
across that map.
Updated the theorem proof explanation and its existing DAG node to describe this route.
The proof compiles as one module through lcompile.py (15.6 seconds, exit code 0).
The original theorem signature was compared verbatim and is unchanged. No local proof gap remains.
All public imports are preserved. No other module or public declaration was changed.
The added universe, open command, local instance priority and local irreducibility attributes
are recorded in `coord/changes/R9-finite-etale-projection-proof-context.md`.
The downstream source check reports zero consumers; the public theorem type is identical.

The source theorem follows the same proper geometric-fibre and conservative-stalk argument;
it is used as an existing tool. The unit statement and its compactification route remain intact.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.sf_finite_etale_projection_formula`
(node `sk-thm-sf-pf-finite`). No sorry remains in the item. Added 0 holes and split off 0.
The proof uses existing declarations; this count does not assert closure of their dependencies.

## No longer needed

Removed these private proof imports:

- `Sheaf.Paper.ProjectionCompactification`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.Paper.GeometricStalkPerfect`
- `WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `Sheaf.Paper.ProjectionMateExact`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`

The following original proof dependencies are no longer directly required by this item:

- `def-weil-pbc-projection-compactification`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-extension-by-zero-stalks`
- `prop-weil-pbc-geometric-stalks-exact`
- `lem-kun-stalk-as-pullback`
- `lem-kun-inverse-image-monoidal`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `fix-lem-finite-tor-perfect`
- `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`
- `lem-kun-proper-base-change-torsion-ring`
- `lem-kun-proj-formula-natural`
- `cor-cbc-derived-extension-zero-base-change`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-sf-triangle-morphism-iso`
- `lem-weil-pbc-degreewise-split-derived-triangle`

The source proper projection theorem already handles geometric base change, constant-complex
projection, and stalk conservativity, and the existing open projection comparison is already
an isomorphism. Hence this item need not repeat the perfect-stalk finite-free devissage,
open-stalk calculation, tensor descent, projection-mate triangle argument, or extension-zero
fibre comparison. Those nodes may remain needed by the retained source theorem or other
consumers; no global withdrawal or deletion is claimed. The removed imports above list the
corresponding unused modules completely. Existing public imports remain for interface stability.

Removed the obsolete direct `tool_uses` approvals from the node (all 19 old entries):

- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-extension-by-zero-stalks`
- `prop-weil-pbc-geometric-stalks-exact`
- `lem-kun-stalk-as-pullback`
- `lem-kun-inverse-image-monoidal`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `fix-lem-finite-tor-perfect`
- `lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`
- `lem-kun-proper-base-change-torsion-ring`
- `lem-kun-proj-formula-natural`
- `cor-cbc-derived-extension-zero-base-change`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-sf-triangle-morphism-iso`
- `lem-weil-pbc-degreewise-split-derived-triangle`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-cbc-extension-zero-base-change`

## Where the brief, the DAG or earlier work was wrong

The old six-step plan repeats the already available source proper projection theorem and
its canonical open-extension composition. Its last step asserts the D+ endpoint membership
without an explicit Lean estimate. The revised proof supplies that estimate using the
exact open extension, left t-exact derived pushforward, and the generic Tor-amplitude
lower tensor bound. The generic coefficient-category wrapper keeps the sheaf tensor
comparison cheap for the kernel; all helpers are private and fully proved.
No statement, definition, or hypothesis was repaired or weakened; constructibility and L's
boundedness hypotheses are retained even though this proof needs only K's lower bound and
L's Tor interval.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
