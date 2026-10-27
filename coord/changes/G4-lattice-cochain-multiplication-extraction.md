# Lattice algebra cochain multiplication extraction

## Reason

The two original holes have complete proofs, but the original combined module takes
74–92 seconds, above the 60-second file limit. The profiler identifies repeated kernel
checks of the concrete monoidal presentations and the inferred multiplication and cup
definitions. The multiplication proof was first generalized to a proved private lemma
in an abstract additive monoidal category, reducing the first version from 91 to 74
seconds. Canonical-instance preference and explicit result-type experiments did not
bring the combined module under the limit and are absent from this packet.

Following the assigned brief's step 3a, extract the self-contained cochain construction
into `Sheaf.CategoryTheory.LatticeAlgebraCochainMultiplication`. The assigned module
publicly reexports it. No existing declaration signature, instance priority, data body,
public import, or mathematical statement changes. All former declarations remain
available from the same import path. No adopted source-library file changes.

## Old

All declarations were in `Sheaf.CategoryTheory.LatticeAlgebraDerivedCup`.
The construction theorem had the signature below, with proof `by sorry`:

```lean
theorem singleMultiplicationExists (B : Algebra R r) :
    ∃! m : HomologicalComplex.tensorObj
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X)
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X) ⟶
        (HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X,
      (MonoidalCategoryStruct.tensorHom (C := Equivariant R r)
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).inv
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).inv) ≫
      HomologicalComplex.ιTensorObj
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X)
        ((HomologicalComplex.single (Equivariant R r) (.up ℤ) 0).obj B.X) 0 0 0 rfl ≫ m.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).hom =
        MonObj.mul (X := B.X)
```

The concrete cochain setup, `Algebra`, `cochainTensor_eq`, and
`singleMultiplicationExists` preceded `singleMultiplication` in that module.
`singleMultiplication` and all later data definitions had their current bodies.

## New

The assigned module adds this public import:

```lean
public import Sheaf.CategoryTheory.LatticeAlgebraCochainMultiplication
```

The new module contains the former cochain setup, `Algebra`, `cochainTensor_eq`,
and `singleMultiplicationExists` with their original signatures and instance priorities.
The two theorem proofs are complete. A fully proved private generic helper constructs
the map by coproduct descent and proves uniqueness by extensionality. The assigned
module retains `singleMultiplication` and every later definition verbatim, including
the original inferred signatures. Existing public imports are retained.

The owning node's Lean attachment lists the declarations retained in the assigned
module, and the new node attaches those extracted into the new module. The owning
node has the new cochain-construction node as a proof dependency. Its statement and
statement dependencies are unchanged. Target meanings and the blueprint unit route
are unchanged, so no target statement review is reopened.

## Users

`tools/downstream.py Sheaf.CategoryTheory.LatticeAlgebraDerivedCup --uses
Profinite.DiscreteLattice.DerivedCup.singleMultiplicationExists` reports nine transitive
consumers and no external direct reference to the existence theorem. The three direct
importers are `LatticeKoszulTriangulatedCupComparison`,
`LatticeRestrictionCupComparison`, and `LatticeFlatTwistedChainPairing`.
All original declarations are retained through the public reexport. No consumer
is changed or adapted in this packet. All three direct importers were copied
temporarily to the sandbox and compiled against the delivered files, in 29.1,
25.3 and 34.9 seconds respectively. The unchanged copies were then removed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.LatticeCharacterKoszulBoundary` | A2 | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeCubicalMultiplicationRoof` | H2 | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeFlatTwistedChainPairing` | H4 | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeKoszulInjectiveNormalization` | unclaimed | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeKoszulTotalTriangles` | J1 | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison` | unclaimed | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeOrderedKoszulProducts` | A3 | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeRestrictionCupComparison` | unclaimed | Same declarations, instances and definitions through the public reexport; no source adaptation. |
| `Sheaf.CategoryTheory.LatticeSectionwiseActionBridge` | unclaimed | Same declarations, instances and definitions through the public reexport; no source adaptation. |

## Status

landed 20261026T081908-L-2100276 2026-10-26 (merge of deliver/G4/Sheaf.CategoryTheory.LatticeAlgebraDerivedCup)
