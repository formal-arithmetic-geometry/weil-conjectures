# Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent retirement

## Reason

Apply the human's retirement instruction in
coord/changes/retire-sheaf-twins-20261020.md, Hand-off. The official twin gives actual
canonical equivalences instead of the Sheaf copy's two Nonempty theorems. Its
coefficient representation, cocycle space and coboundary quotient use the same
upstream definitions. No upstream file or target statement changes.

## Old

Retired module: lean/Sheaf/FieldTheory/GaloisUnitsHomogeneousCocycleDescent.lean.
Its public theorem signatures were:

```lean
theorem nonempty_equiv_galoisUnitsHomogeneousCocycles_twoCocycle
    (K : Type u) [Field K] :
    Nonempty (GaloisUnitsHomogeneousCocycles K ≃ GaloisUnitsTwoCocycle K)

theorem nonempty_equiv_galoisUnitsH2_twoCocycleClasses_of_cocycle_equiv
    (K : Type u) [Field K]
    (h : Nonempty (GaloisUnitsHomogeneousCocycles K ≃ GaloisUnitsTwoCocycle K)) :
    Nonempty (GaloisUnitsH2 K ≃ GaloisUnitsTwoCocycleClasses K)
```

The consumer imported the retired module and applied both theorems in succession.

## New

Withdraw the entire Sheaf module using deleted.txt. The consumer imports
WeilConjectures.FieldTheory.GaloisUnitsHomogeneousCocycleDescent and proves its
unchanged theorem by `exact ⟨galoisUnitsH2EquivTwoCocycleClasses K⟩`.
The upstream module already provides both canonical equivalences:

```lean
def galoisUnitsHomogeneousCocyclesEquivTwoCocycle :
    GaloisUnitsHomogeneousCocycles K ≃ GaloisUnitsTwoCocycle K

def galoisUnitsH2EquivTwoCocycleClasses :
    GaloisUnitsH2 K ≃ GaloisUnitsTwoCocycleClasses K
```

The two retired module's DAG attachments now name these explicit upstream
constructions; the comparison node records its direct application of descent.
No new declarations, assumptions, definitions or sorry proofs are introduced.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent | E1 | Retired copy withdrawn. |
| Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison | unclaimed | Private proof import and proof body adapted; statement and visibility identical. |

A complete source search found no other importer or caller of the removed API.
The unchanged public comparison statement still compares the same two types.

## Status

landed 20261020T144243-L-2258664 2026-10-20 (merge of deliver/E1/Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent)
The consumer import closure has no Sheaf/upstream twin collisions and no retired
module; all Lean references to the removed module and theorem names are gone.
The required dry run passed compilation and preflight at 80bc76259d (CODEX).
Awaiting independent review and the maintainer global build.
