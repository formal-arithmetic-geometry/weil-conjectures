# CategoryTheory.RingedToposMorphism.existsUnique_derivedConstantTowerComparison

## Reason

Prove the constant-tower normalization theorem with its original signature and all public
constructions unchanged. The new helpers are private and fully proved. The only change to
elaboration outside their proofs is a local priority for Mathlib's existing
`hasSheafCompose_of_preservesLimitsOfSize` instance. The default higher-priority multicospan
route repeatedly expanded covering multicospans while elaborating the concrete sheaf
categories: the original statement alone took about 50 seconds, and the completed proof
exceeded the 60-second file limit. The local priority reduces the unchanged statement to
about 9 seconds. It chooses a proof of the same Prop-valued `HasSheafCompose` class and
changes no functor, category, comparison, or target meaning.

The resolving-class, counit transport, fraction extension, localization lift and uniqueness
arguments are proved abstractly, then specialized to the ordinary and tower K-flat classes.
All work stays in this module. No consumer adaptation is necessary.

## Old

There was no local instance-priority command. The existing theorem was:

```lean
theorem existsUnique_derivedConstantTowerComparison
    (f : RingedToposMorphism
      ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
    (E : ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))
    [E.Additive] (adj : E ⊣ f.modules)
    (L : DerivedCategory (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [Lt.IsLeftDerivedFunctor τ (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Functor.HasUniqueConstantTowerNormalizedComparison.{u + 1, u, u + 1, u,
        wA, wB, wTA, wTB}
      (A := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
      (B := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)) E L ε Lt τ
      (fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) := by
  sorry
```

## New

The following command is local to this module:

```lean
attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize
```

Every existing public definition, signature and public import stays verbatim. The theorem
is now proved using fully proved private helpers:

```lean
theorem existsUnique_derivedConstantTowerComparison
    (f : RingedToposMorphism
      ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
    (E : ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S))
    [E.Additive] (adj : E ⊣ f.modules)
    (L : DerivedCategory (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (ε : DerivedCategory.Q ⋙ L ⟶
      E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))]
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [Lt.IsLeftDerivedFunctor τ (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))] :
    Functor.HasUniqueConstantTowerNormalizedComparison.{u + 1, u, u + 1, u,
        wA, wB, wTA, wTB}
      (A := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R))
      (B := ringedSiteModules.{u, u, u, u}
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj S)) E L ε Lt τ
      (fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) := by
  exact Functor.constantTowerComparison_of_resolving E (ringedResolvingClass R)
    (ringed_resolution T R) (ringed_pullback_inverts T T' R S f E adj)
    (fun P ↦ ∀ j : ℕᵒᵖ, ringedResolvingClass R (P.asFunctor.obj j))
    (ringed_tower_resolution T R) (ringed_tower_pullback_inverts T T' R S f E adj)
    (fun P hP _ ↦ hP) L ε Lt τ
```

Three proof-only imports provide complexes of functors, initial restriction of limit cones,
and the universe lift of the tower indexing category. No public helper or instance is added.

## Users

Ran the source-only query:
`python3 tools/downstream.py Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization
--uses existsUnique_derivedConstantTowerComparison ConstantTowerDerivedComparison
IsConstantTowerRepresentativeNormalized HasUniqueConstantTowerNormalizedComparison`.
It found zero downstream modules and only this module mentioning these declarations.
DAG parents with unfinished proofs retain their dependencies; none is withdrawn.
The public interface is unchanged, so future consumers require no adaptation either.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization | T8 | Theorem proved; local elaboration priority; public interface unchanged. |

## Status

landed 20261021T120647-L-3930039 2026-10-21 (merge of deliver/T8/Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization)
