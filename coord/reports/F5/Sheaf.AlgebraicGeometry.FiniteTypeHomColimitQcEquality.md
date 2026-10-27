## What changed

Proved `SheafOfModules.finite_type_hom_colimit_qc_equality` with its original signature.
Added two proved private helpers in the same module: `section_eventual_equality` identifies
the underlying sheaf colimit with a sheafified presheaf colimit, then uses the covering
equalizer sieve and filtered set-colimit equality; `generators_ext_on_object` cancels a
restricted generating epimorphism and checks the restricted free coproduct on its
rank-one summands. Finite intersections synchronize the generators near each point.
A finite subcover and one common upper stage synchronize these neighbourhoods over U;
sheaf separatedness gives equality of the morphisms.

The generator helper is stated over an arbitrary small site, keeping the ring sheaf
abstract to avoid repeated expansion of nested restrictions. The main proof similarly
generalizes the ring sheaf internally. The generator argument uses restriction
preserving epimorphisms and coproducts, avoiding
any claim that an epimorphism is surjective on sections. Empty generator families use
the empty coproduct. Empty U uses the empty subcover and a common upper bound of i and j.
The item node now records this categorical version of step 4. No definitions, public
signatures, attributes or public imports changed; no consumer adaptations are required.

## Proved and sorry left

Closed the sole original hole in `SheafOfModules.finite_type_hom_colimit_qc_equality`
(node `lem-weil-pbc-finite-type-hom-colimit-qc-equality`). Added zero holes; zero remain
in the delivered module. Both private helpers have complete proofs. No split-off theorem
or new axiom was introduced. The complete module compiled through `lcompile.py`
with no errors or warnings in 39.5 seconds; no profiling or increased-limit options remain.

## No longer needed

Removed the proof imports
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` and
`WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`.
For the former, Mathlib's local-injectivity instance supplies the precise local-equality
clause directly; the existing conceptual dependency
`lem-weil-pbc-site-sheafification-sections-local` is retained in the node, with the
Mathlib implementation identified in its proof step. The broader theorem is not imported.
The dependency `lem-weil-pbc-ringed-space-module-exactness-local-lifting` is removed from
the item node: preservation of epimorphisms and the free coproduct universal property
replace the local-lifting argument completely. All other declared dependencies are used.
No module is withdrawn; these are removed dependencies of this proof, not a claim that
other target branches cease to use their modules. Added the private proof import
`Mathlib.Data.Finset.Order` for finite upper bounds and
`Mathlib.CategoryTheory.Limits.Constructions.Over.Products` for the restriction
adjunction on the iterated over-site.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing hypothesis was found. The planned local-lifting argument
is valid, but a categorical restriction-and-cancellation argument is shorter with the
available Mathlib API. The proof does not require compact overlaps, transition
injectivity, or finite presentation. Search with LeanFinder, Loogle and Mathlib/source
ripgrep found no direct theorem proving the assigned finite-type assertion.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
