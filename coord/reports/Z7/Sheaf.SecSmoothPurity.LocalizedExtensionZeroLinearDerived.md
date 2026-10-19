## What changed

Proved `CategoryTheory.localizedExtensionZeroLinearDerived` without changing its signature.
Private helpers construct sectionwise scalar multiplication on module-sheaf morphisms,
prove its module laws, and prove bilinearity of composition. Restriction is linear by its
sectionwise definition. The already proved `Adjunction.left_adjoint_linear` transfers
linearity to extension using `SheafOfModules.localizedModuleAdjunctionIndependent`.
The existing exactness instances and Mathlib's derived-functor instances then give
additivity, derived linearity, shift compatibility and triangulatedness.

Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` and updated the item's
DAG proof, proof dependencies and proof origin to record this adjunction argument.
All scalar structures are constructed explicitly. The existing adjunction is fixed by
its normalized unit through a unique-existence theorem; no arbitrary existence witness
is introduced. Derived scalars are Mathlib's induced structures.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.localizedExtensionZeroLinearDerived`
(node `lem-cbc-localized-extension-zero-linear-derived`). Added 0 holes; split off 0
statements. No `sorry` remains in any delivered Lean declaration. Existing exactness
and adjunction theorems remain dependencies of the proof and retain their own nodes.

The resumed session compiled the retained proof against current sources using
`lcompile.py`: exit code 0, 4.1 seconds, no diagnostics (2026-10-19). The theorem
signature is identical to the repository's signature, and all delivered Lean lines
have at most 100 characters. The import-direction check accepts the added import.

## No longer needed

Removed the redundant proof-only imports
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.
The retained public imports provide the unchanged statement and exactness interface.

Removed `def-weil-extension-by-zero-presheaf` and
`def-weil-presheaf-modules-sheafification` from the item's `proof_deps`:
the proof does not need their direct-sum generator or sheafification factorization
calculations. Both remain statement dependencies defining the actual extension functor,
and their implementation modules remain transitively imported. No module is withdrawn.
All other proof dependencies remain used: scalar structures, restriction, exactness,
induced derived scalars, derived triangulatedness, and exact derived functor linearity.
The unit's `realized` table has no statement or step attachment to this node; the unit
route is preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's direct-sum and sheafification scalar computations can be replaced by the
existing adjunction lemma. Under the adjunction Hom bijection, the images of L(a f)
and a L(f) both equal a times the image of L(f), by unit naturality, restriction's
linearity and bilinearity of composition. This works for arbitrary sites, including
objects admitting no arrows to U. No statement or definition repair is needed.

The retained proof constructs the two prescribed scalar structures explicitly and
uses Mathlib's induced derived structures, respecting the earlier statement review.
The current dependency node records the more general system interface; the retained
`LocalizedModuleExactIndependent` interface supplies precisely the original theorem's
site and coefficient universes and its normalized adjunction.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
