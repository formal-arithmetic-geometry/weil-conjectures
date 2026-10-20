# AlgebraicGeometry.Etale.nonempty_affineSpaceAmbientAdjunction

## Reason

The stage-3 preflight requests this record because the proof adds the command
`attribute [local instance] Sheaf.monoidalCategory`. This attribute is local to the
item module; it supplies the usual sheaf monoidal structure while elaborating
proved private comparison helpers. It changes no exported instance, definition,
theorem signature, public import, notation, or target meaning.

The proof replaces the original `sorry` by composition of the existing coordinate
tower and projective-line adjunctions and transport along proved natural
isomorphisms. The new imports are private. The DAG changes concern only the proof
route, proof dependencies, proof origin, and removal of obsolete tool approvals.

## Old

There was no local sheaf-monoidal instance command. The public signature was:

```lean
theorem nonempty_affineSpaceAmbientAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣
        ((upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin d)) S ↘ S)).mapDerivedCategory ⋙
          derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) S)
            ((DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) S) N A hA d))) ⋙
          shiftFunctor _ (2 * (d : ℤ)))
```

## New

The following module-local command supports the private helpers:

```lean
attribute [local instance] Sheaf.monoidalCategory
```

The public signature is verbatim unchanged:

```lean
theorem nonempty_affineSpaceAmbientAdjunction (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Nonempty
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣
        ((upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin d)) S ↘ S)).mapDerivedCategory ⋙
          derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) S)
            ((DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) S) N A hA d))) ⋙
          shiftFunctor _ (2 * (d : ℤ)))
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
--uses nonempty_affineSpaceAmbientAdjunction` reports one downstream module and
no textual use of this declaration outside the item. The downstream file imports
the item privately and mentions the affine-space argument in its proof docstring.
Its declarations and meanings are unchanged; no adaptation is needed. No existing
public definition changes, so no target-statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | M4 | Original hole proved; local instance and proved private helpers only. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Private importer; no signature, instance, or proof adaptation. |

The complete item compiles with zero warnings and zero holes in 18.1 seconds
through `lcompile.py`. There are no adapted modules and no source-library edits.

## Status

landed 20261020T211758-L-3500688 2026-10-20 (merge of deliver/M4/Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction)
