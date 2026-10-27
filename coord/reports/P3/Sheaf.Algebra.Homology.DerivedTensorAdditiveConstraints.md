## What changed

Filled the four theorem proofs in the assigned module with private proved helpers.
Two transparent abbreviations name the existing native complex tensor dictionaries.
The published representative comparison is assembled as a natural isomorphism on
resolving chain models. Native associator, Koszul braiding and tensor-shift natural
isomorphisms give the prescribed normalized constraints. Morphisms in the homotopy
category lift to chain maps, so these comparisons descend to the resolving homotopy
subcategory; fully faithful precomposition with its binary and ternary localizations
extends them uniquely. Finite-variable restriction uses Mathlib product localization,
including an empty index type. Exactness for a resolving representative gives
additivity for arbitrary derived objects after transport by its representative iso.
Mathlib's preservation of biproducts supplies the actual image diagrams.

Model closure uses the existing tensor/shift closure, the independent-coefficient
bounded-flat criterion for single complexes, native single-factor tensor comparisons,
and categorical flatness under tensor and finite products. Finite-sum K-flatness follows
from tensor colimit preservation and additivity of homology. All existing public signatures and definition bodies, and all source-library modules,
are preserved. The dictionary abbreviations and local instance preferences are recorded
in `coord/changes/p3-derived-tensor-native-dictionaries.md`. The downstream script lists
zero consumers, so no adaptations are required. The existing DAG proof follows these routes.

## Proved and sorry left

Closed all four original holes. The complete four-proof module compiled in 59.9 seconds;
the delivery preflight checks the final formatting and equality-composition cleanup:

- `SheafOfModules.DerivedTensorConstraints.derived_tensor_model_closure`.
- `SheafOfModules.DerivedTensorConstraints.existsUnique_derived_tensor_constraints`.
- `SheafOfModules.DerivedTensorConstraints.derived_tensor_restriction_fully_faithful`.
- `SheafOfModules.DerivedTensorConstraints.derived_tensor_additive`.

All realize `lem-pur-derived-tensor-additive-constraints`. Four holes closed, zero holes
added or split off; zero explicit holes remain in the submitted module. Dependency theorems
remain their own items; this delivery introduces no new unproved dependency.

## No longer needed

Removed private import `Sheaf.Algebra.Homology.KFlatTelescopeClosure` and proof
dependency `lem-pc-kflat-closure`: finite sums follow directly from finite biproducts,
and flat degree-zero complexes from `lem-weil-pbc-independent-bounded-flat-kflat`.
The existing statement dependency remains because it documents the mathematical
context; this delivery does not withdraw any module or delete any declaration.
Removed that obsolete entry from the node's approved tool-use list.

Removed the redundant private imports `Mathlib.CategoryTheory.Localization.Predicate`
and `Mathlib.CategoryTheory.Triangulated.Pretriangulated`; both remain available
through the retained dependencies' public imports. No declaration from either is
withdrawn. The original public imports remain verbatim.

The planned dependency `lem-pur-total-tensor-signed-coherence`, module
`Sheaf.Algebra.Homology.TotalTensorSignedCoherence`, is not imported or needed.
The exact native chain isomorphisms in the statement are already natural, and their
whiskerings give the required natural isomorphisms directly. No additional signed
coherence identities are asserted by this item. The node's proof dependency is
removed accordingly. Other users may still need both modules; no global withdrawal
is claimed. The unit statement and its steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan used countable closure stated at
coincident universes for an independent-coefficient statement. The direct finite-sum
argument avoids that mismatch. The signed-coherence node also specializes its
coefficient universe; using the native chain constraints avoids requiring that
unnecessary specialization. Repeated compile-server busy responses (exit 124) were
retried as instructed; they were not treated as proof failures.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
