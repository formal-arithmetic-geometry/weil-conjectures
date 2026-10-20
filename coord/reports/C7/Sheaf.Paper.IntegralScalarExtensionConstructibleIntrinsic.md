## What changed

Proved `WeilConjectures.sfIntegralScalarExtension_constructible` by proving the canonical
intrinsic/legacy predicate comparison and applying the existing
`WeilConjectures.integralScalarExtension_constructible`. The auxiliary datum is constructed
explicitly using a prime larger than l; Y has no extra structure or hypothesis. The restricted
functor and its linearity theorem retain their exact signatures and bodies.

Added `Sheaf.Paper.SfDerivedCompleteLegacyComparison`, with the fully proved public theorem
`WeilConjectures.sfDerivedComplete_iff_legacy`. Its proof compares normalized units and
pure-tensor transitions on K-flat resolutions and transports the complete augmented Roos
triangle. Neither arbitrary cone-map uniqueness nor a chosen arbitrary completion is used.

Both delivered modules compile together through lcompile.py. No existing definition or
statement changes. The item's proof docstring and DAG route record the actual compatibility
argument and its dependency on the legacy declaration.

## Proved and sorry left

Closed the item's one hole: `WeilConjectures.sfIntegralScalarExtension_constructible`
(node `lem-weil-integral-scalar-extension-constructible`). Item holes: 1 before, 0 after.
Added holes: 0. Split-off holes: 0. The new comparison theorem is fully proved; every private
helper is fully proved. The delivered Lean files contain zero sorry occurrences.

The pre-existing `WeilConjectures.integralScalarExtension_constructible` in
`Sheaf.Paper.IntegralScalarExtensionConstructible` still contains sorry and is used by the new
proof. This delivery establishes the intrinsic interface from that existing preservation
statement; it does not claim an independent proof of its finite-filtration/effectivity
argument. The legacy declaration realizes the same preservation mathematics, and its
historical Lean attachment is archived under the item's node. The node's previous proof
plan is retained to document this remaining mathematical work. Existing tower transition
characterization theorems used by the comparison also retain their own recorded holes.

## No longer needed

Removed the following direct proof imports from the item:

- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `Mathlib.CategoryTheory.Sites.Abelian`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteFieldSheafScalarExtension`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Paper.NormalizedDVRTower`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`

The comparison module needs only its two public statement imports; redundant direct proof imports
were removed after compilation.

No mathematical dependency node is claimed pruned: the legacy preservation declaration
still needs its original finite-filtration/effectivity plan. The removed direct imports are
redundant for the compatibility proof; some remain in its transitive import closure through
the existing legacy theorem. The item's unit realized statement/step lists are empty. The finite-torsion
constructibility import is retained because preflight identifies it as a unit-route module;
no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The missing intrinsic interface can be obtained from the already published legacy
preservation declaration once the two canonical completeness predicates are compared.
The comparison was absent; equality of the underlying coefficient categories alone was
insufficient, because the units and transitions also had to be identified. This delivery
supplies that comparison without changing either definition. The legacy theorem remains
unproved, as explicitly noted above; no claim is made that its archived attachment is a
newly finished node.

The first dry run compiled and axiom-probed the packet but its delivery-worktree checkout
crashed after 600 seconds. The retry reached preflight and found a missing LeanSearch record;
that search was run and recorded. No push occurred in either attempt.

## New nodes

`lem-sf-derived-complete-legacy-comparison`: the equivalence of the intrinsic derived-unit
Roos condition and the legacy K-flat augmented-tower condition, over arbitrary schemes.
It is proved in full, with no boundedness or constructibility assumption. The statement
also applies to zero objects and empty schemes; the transport lemma uses only the supplied
product witnesses and imposes no existence hypothesis for all products. No change record
is needed because no existing signature or definition changed.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
