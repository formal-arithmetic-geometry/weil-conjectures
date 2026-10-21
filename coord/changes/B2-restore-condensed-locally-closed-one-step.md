# AlgebraicGeometry.ProEtale.condensed_locallyClosed_one_step

## Reason

The assigned rework row preserves this module at
quarantine/Sheaf/Paper/CondensedLocallyClosedOneStep.lean after a reverted cluster restore.
Its live Lean path is absent. Restore its complete proof and repair an elaboration failure
against the published dependency build. The archive has zero sorry proofs.

The archived proof fails at the elimination of htri.the project server.the project server.the project server with
`Tactic generalize failed: result is not type correct`. Introducing the local fact
hconnect first lets obtain eliminate a local hypothesis without generalizing this
projection's dependent type. This retains the local exact-functor instance witnesses.

## Old

The live source path is absent. The authoritative archived theorem has this signature:

```lean
theorem condensed_locallyClosed_one_step
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))
    (hM : IsConstructibleModuleObject
      (condensedRingObj Λ T) M) :
    condensedLocallyClosedPiece Λ T ((DerivedCategory.singleFunctor _ 0).obj M) ∨
    ∃ (Z : Scheme.{u}) (i : Z ⟶ T),
      Exists fun [_hi : IsClosedImmersion i] ↦
      Exists fun [_hex : PreservesFiniteColimits
          (CondensedRing.lowerStar Λ i)] ↦
      ¬ Function.Surjective i ∧
      ∃ (MZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj Λ Z)),
        IsConstructibleModuleObject
          (condensedRingObj Λ Z) MZ ∧
        ∃ (A : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj Λ T)))
          (f : A ⟶ (DerivedCategory.singleFunctor _ 0).obj M)
          (g : (DerivedCategory.singleFunctor _ 0).obj M ⟶
            (CondensedRing.lowerStar
              Λ i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ))
          (h : (CondensedRing.lowerStar
              Λ i).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj MZ) ⟶
            A⟦(1 : ℤ)⟧),
          Pretriangulated.Triangle.mk f g h ∈ distTriang _ ∧
          condensedLocallyClosedPiece Λ T A
```

Its connecting-map extraction is:

```lean
    obtain ⟨δ, ε, hδ, hε, htriangle, hrest⟩ := htri.the project server.the project server.the project server
```

## New

Restore the archived module, keeping the signature above verbatim, all public and private
imports, its declaration docstring and options, and every mathematical proof step.
Replace only the extraction above by:

```lean
    have hconnect := htri.the project server.the project server.the project server
    obtain ⟨δ, ε, hδ, hε, htriangle, hrest⟩ := hconnect
```

The restored statement still gives a locally closed piece or a nonsurjective closed
immersion with constructible restriction and a distinguished triangle. It covers the empty
scheme through the first alternative. No definition or target statement changes meaning;
no target semantic review is reopened. The existing node attachment, proof and dependencies
are preserved; its proof-origin note records this restoration.

## Users

A direct import and declaration-use scan of both live roots and both quarantine roots
finds one consumer. The existing DAG parent is the same extension-tower node. The consumer
continues to apply exactly the archived theorem signature. No consumer adaptation is needed.
An import-order compile checked the final restored item in 16.4 seconds and the unchanged
archived consumer in 5.2 seconds, both without errors or warnings. The consumer test copy is
outside the delivery's lean/ tree.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | not queried; untouched | Archived direct importer and DAG parent; identical theorem signature and public imports. |

## Status

landed 20261021T021902-L-2788646 2026-10-21 (merge of deliver/B2/Sheaf.Paper.CondensedLocallyClosedOneStep)
