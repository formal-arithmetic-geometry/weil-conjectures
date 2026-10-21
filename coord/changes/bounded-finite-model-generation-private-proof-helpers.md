# AlgebraicGeometry.ProEtale.CondensedRing.bounded_finiteModel_generation

## Reason

The stage-3 preflight requires a change record because the proof adds a scoped
section and section variables for private finite-certificate helpers. These
commands only parameterize private declarations; the section closes before the
public theorem. No public signature, public import, definition, notation, or
attribute changes. The only new instance is a local hypothesis inside the theorem
proof. This record documents a syntactic interface-check trigger, with no
mathematical interface change.

## Old

```lean
theorem bounded_finiteModel_generation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (C : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [C.IsClosedUnderIsomorphisms] [C.IsTriangulated]
    (hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      HasFiniteConstantLocalModel Λ S L →
        C ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj L))))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K) :
    C K ∧ ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      Nonempty (F (Fin.last N) ≅ K) ∧ ∀ r : Fin (N + 1),
        IsZero (F r) ∨
        (∃ (V S : Scheme.{u}) (v : V ⟶ X), Exists fun [IsOpenImmersion v] ↦
          ∃ t : S ⟶ V, IsClosedImmersion t ∧ IsReduced S ∧
          ∃ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
            HasFiniteConstantLocalModel Λ S L ∧
            Nonempty (F r ≅ (DerivedCategory.singleFunctor _ 0).obj
              ((openImmersionLowerShriek Λ v).obj
                ((lowerStar Λ t).obj L)))) ∨
        (∃ (i : Fin (N + 1)) (n : ℤ), i < r ∧ Nonempty (F r ≅ (F i) ⟦n⟧)) ∨
        (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
          ∃ (f : F i ⟶ F r) (g : F r ⟶ F j) (h : F j ⟶ (F i) ⟦(1 : ℤ)⟧),
            Pretriangulated.Triangle.mk f g h ∈ distTriang _)
```

The body was `by sorry`. The private helper section did not exist.

## New

```lean
theorem bounded_finiteModel_generation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (C : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [C.IsClosedUnderIsomorphisms] [C.IsTriangulated]
    (hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      HasFiniteConstantLocalModel Λ S L →
        C ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek Λ v).obj ((lowerStar Λ t).obj L))))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K) :
    C K ∧ ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      Nonempty (F (Fin.last N) ≅ K) ∧ ∀ r : Fin (N + 1),
        IsZero (F r) ∨
        (∃ (V S : Scheme.{u}) (v : V ⟶ X), Exists fun [IsOpenImmersion v] ↦
          ∃ t : S ⟶ V, IsClosedImmersion t ∧ IsReduced S ∧
          ∃ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S),
            HasFiniteConstantLocalModel Λ S L ∧
            Nonempty (F r ≅ (DerivedCategory.singleFunctor _ 0).obj
              ((openImmersionLowerShriek Λ v).obj
                ((lowerStar Λ t).obj L)))) ∨
        (∃ (i : Fin (N + 1)) (n : ℤ), i < r ∧ Nonempty (F r ≅ (F i) ⟦n⟧)) ∨
        (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
          ∃ (f : F i ⟶ F r) (g : F r ⟶ F j) (h : F j ⟶ (F i) ⟦(1 : ℤ)⟧),
            Pretriangulated.Triangle.mk f g h ∈ distTriang _)
```

The body is proved using private finite-construction certificates, the existing
finite-model stratum filtration, and existing bounded degreewise devissage.
The added `section FiniteConstructions` and its `variable` command are closed by
`end FiniteConstructions`; every helper declaration is private and proved.
No definition has a postponed proof or arbitrary chosen data.

## Users

`tools/downstream.py Sheaf.Paper.BoundedFiniteModelGeneration --uses
AlgebraicGeometry.ProEtale.CondensedRing.bounded_finiteModel_generation` reports
zero downstream modules and only the defining module as a textual declaration user.
The assigned node remains needed by its DAG parents; none is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedFiniteModelGeneration | M5 | One proof completed; original public signature unchanged. |

## Status

landed 20261021T155757-L-3446718 2026-10-21 (merge of deliver/M5/Sheaf.Paper.BoundedFiniteModelGeneration)
