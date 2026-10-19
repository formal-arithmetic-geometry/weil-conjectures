# AlgebraicGeometry.Scheme.ProEt.milnorTowerCokernel (and tower companions)

## Reason

The generic Roos cohomology calculation needs the tower constructions, while
ProEtaleMilnorSequence specializes that calculation. Move the four constructions
to MilnorTower to avoid an import cycle. Their names, universes, binders, bodies,
visibility and meaning are identical. ProEtaleMilnorSequence publicly imports
MilnorTower and retains all its original public imports. No target statement or
meaning changes and no consumer requires adaptation.

## Old

In Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence:

```lean
section Cokernel

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The sheaf cokernel of 1-T on a tower product, using the existing transition map.
Source: blueprint main-20261015, det-pe-milnor-sequence, clause 1
(blueprint: det-pe-milnor-sequence). -/
abbrev milnorTowerCokernel (M : ℕᵒᵖ ⥤ A) : A :=
  cokernel (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
    (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op))

/-- The canonical map of these cokernels induced by a tower morphism.
Source: blueprint main-20261015, det-pe-milnor-sequence, naturality in clause 1
(blueprint: det-pe-milnor-sequence). -/
def milnorTowerCokernelMap {M N : ℕᵒᵖ ⥤ A} (f : M ⟶ N) :
    milnorTowerCokernel M ⟶ milnorTowerCokernel N :=
  cokernel.map
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op))
    (towerTransitionEndomorphism (K := fun n : ℕ ↦ N.obj (op n))
      (fun n ↦ N.map (homOfLE (Nat.le_succ n)).op))
    (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)))
    (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)))
    (towerTransitionEndomorphism_natural_backward _ _ _
      (fun n ↦ (f.naturality (homOfLE (Nat.le_succ n)).op).symm)).symm

/-- The tower of q-th cohomology sheaves, with induced transition maps.
Source: blueprint main-20261015, det-pe-milnor-sequence, clause 1
(blueprint: det-pe-milnor-sequence). -/
abbrev milnorCohomologyTower (K : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : ℤ) : ℕᵒᵖ ⥤ A :=
  K ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q

/-- Regard a module tower as complexes concentrated in degree zero.
Source: blueprint main-20261015, det-pe-milnor-sequence, clause 2
(blueprint: det-pe-milnor-sequence). -/
abbrev milnorSingleTower (M : ℕᵒᵖ ⥤ A) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  M ⋙ HomologicalComplex.single A (ComplexShape.up ℤ) 0

end Cokernel
```

## New

Exactly the Old block, verbatim, in Sheaf.AlgebraicGeometry.MilnorTower;
ProEtaleMilnorSequence replaces that block with:

```lean
public import Sheaf.AlgebraicGeometry.MilnorTower
```

All original public imports of ProEtaleMilnorSequence remain.

## Users

Source search with tools/downstream.py --uses and rg found the following
existing declaration users. The import closure (843 downstream modules at the
resumed-session snapshot) continues to receive all four declarations and the original
public imports. It therefore needs no edits. The new modules are owned by V6.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence | V6 | Same statement, proved using the generic sequence; definitions re-exported. |
| Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic | V5 | Uses milnorSingleTower with identical name, type and body. |
| Sheaf.AlgebraicGeometry.ProEtaleLeftCompleteTruncationTower | unclaimed | Uses the identical tower definitions; no statement or proof edits. |
| Sheaf.AlgebraicGeometry.MilnorTower | V6 | New home of unchanged definitions. |
| Sheaf.AlgebraicGeometry.RoosCohomologyMaps | V6 | New generic calculation uses the tower definitions. |
| Sheaf.AlgebraicGeometry.RoosCohomologyNaturality | V6 | New proof of naturality for the explicit maps. |
| Sheaf.AlgebraicGeometry.RoosCohomologySequence | V6 | New proved package of the explicit natural short exact sequence. |

## Status

landed 20261019T034326-L-421589 2026-10-19 (merge of deliver/V6/Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence)
