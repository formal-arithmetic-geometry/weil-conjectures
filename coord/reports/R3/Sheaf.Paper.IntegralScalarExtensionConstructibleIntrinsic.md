## What changed

Proved `WeilConjectures.sfIntegralScalarExtension_constructible` without changing its
signature, the restricted functor, its visibility, or the proved scalar-action equality.

The shortest route reuses the existing declaration
`WeilConjectures.integralScalarExtension_constructible` in
`Sheaf.Paper.IntegralScalarExtensionConstructible`, an existing legacy realization of
this same mathematical node. Its proof remains an existing `sorry`; this delivery
proves the interface transport, not that underlying preservation argument.
The canonical coefficient presentation theorem `purCoefficientModel_predicates`
identifies both completeness predicates on the image of `purCoefficientModel`.
Proved private isomorphism-invariance helpers transport the two augmented Roos
triangles through the equivalence counit, giving the equivalence on every ambient
object. The finite reduction functors are definitionally equal (checked by `rfl`).
The legacy membership, preservation, and reverse completeness transport then combine
in Lean. No geometric bounds are used. The new helpers all have complete proofs.

The earlier interrupted draft's two unproved helper statements were never delivered;
they are removed. No new module or new public declaration is introduced.
The node copy records the transport and reuse while retaining its existing
residue-field, finite-filtration, and normalized-tower route for the legacy theorem.

Validation: the integrated item compiled cleanly through `lcompile.py` in 13.1 seconds.
A separate scratch compilation checked the reduction equality and the whole transport.
Both directions of the completeness equivalence retain canonical augmentations;
this works for the empty scheme, zero complexes, identity extensions, and all
positive reduction exponents. No finite-field structure on the scheme is introduced.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.sfIntegralScalarExtension_constructible`
(node `lem-weil-integral-scalar-extension-constructible`).

Original item holes: 1. Remaining item holes: 0. Added holes: 0. Split off: 0.
`sfConstructibleIntegralScalarExtension_smul` was already proved and is unchanged.

This is reuse of an existing unresolved theorem, not an axiom-free proof of scalar
preservation. The imported legacy `integralScalarExtension_constructible` still has
its existing hole, and `purCoefficientModel_predicates` also has its existing hole.
Other pre-existing holes in those modules are unchanged. The sorry ledger, rather
than the local hole count, determines the net change in the targets' import closure.

## No longer needed

Removed these direct proof imports, whose individual declarations are not used by
the transport proof:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.NormalizedDVRTower`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `Mathlib.CategoryTheory.Sites.Abelian`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteFieldSheafScalarExtension`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`

The proof uses
`Sheaf.Paper.IntegralScalarExtensionConstructible` and
`Sheaf.Paper.CompletedCoefficientPresentationTransport`.
The unit-route import `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` is retained,
as required by the unit-route gate, as are both original public imports.
Helper opens are scoped to private declarations, and helper parameters are explicit;
no public scope command changes. No DAG dependency or whole module is
claimed globally pruned: the legacy realization retains the original finite-layer
and normalized-tower proof obligation and its dependencies. The unit has no realized
statement or steps bypassed by this reuse. No new node is required for proved private
isomorphism-invariance glue.

## Where the brief, the DAG or earlier work was wrong

The interrupted draft attempted a decomposition into completeness preservation and
finite-level preservation. That is unnecessary given the already stated legacy
preservation theorem and the existing unbounded coefficient-presentation predicates.
The legacy theorem is usable after an explicit completeness transport; the finite
reductions and ambient completed extension agree exactly. This delivery does not
assert that the legacy theorem is already proved, does not weaken a statement, and
does not claim the duplicate interface transport settles the remaining mathematical
preservation obligation.

The added DAG dependencies are the completeness definition
`def-weil-derived-complete` and
`def-pur-completed-coefficient-presentation-transport`, used as a tool for its
unbounded completeness comparisons only. Its bounded comparison requires geometric
hypotheses and is not used. A dependency traversal found no path back to this item.
The other original proof-dependency imports are indirect through the reused legacy theorem,
so they are not claimed unnecessary in the mathematical DAG.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
