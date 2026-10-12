# CategoryTheory.exists_horseshoe_rightDerived_deltaFunctor

## Reason

DAG-only correction: the final comparison remark in the horseshoe node names the universal
delta-functor node as a forward pointer. Its reviewer explicitly identified this as a
pointer, not a dependency. Using the existing horseshoe construction to prove the
existential universal theorem would make that pointer an artificial cycle. Replace the
bracketed pointer by prose and remove only that entry from stmt_deps. The Lean module,
its signature, and all mathematical content are unchanged.

## Old

```lean
theorem exists_horseshoe_rightDerived_deltaFunctor {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A] [EnoughInjectives A] [Category.{v₂} B] [Abelian B] (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] : ∃ (G : CohomologicalDeltaFunctor A B) (hF : G.F = (fun n : ℕ ↦ v.rightDerived n)), ∀ (S : ShortComplex A) (hS : S.ShortExact) (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃) (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex) (hαβ : α ≫ β = 0) (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι) (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι) (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact), ∃ hvH : ((ShortComplex.mk α β hαβ).map (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact, ∀ n : ℕ, G.delta S hS n ≫ eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hF) = eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hF) ≫ (IC.isoRightDerivedObj v n).hom ≫ hvH.δ n (n + 1) rfl ≫ (IA.isoRightDerivedObj v (n + 1)).inv
```

DAG comparison reference: `[lem-weil-pbc-right-derived-universal-delta-functor]`.

## New

```lean
theorem exists_horseshoe_rightDerived_deltaFunctor {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A] [EnoughInjectives A] [Category.{v₂} B] [Abelian B] (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] : ∃ (G : CohomologicalDeltaFunctor A B) (hF : G.F = (fun n : ℕ ↦ v.rightDerived n)), ∀ (S : ShortComplex A) (hS : S.ShortExact) (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂) (IC : InjectiveResolution S.X₃) (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex) (hαβ : α ≫ β = 0) (_hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι) (_hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι) (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact), ∃ hvH : ((ShortComplex.mk α β hαβ).map (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact, ∀ n : ℕ, G.delta S hS n ≫ eqToHom (congrArg (fun F ↦ (F (n + 1)).obj S.X₁) hF) = eqToHom (congrArg (fun F ↦ (F n).obj S.X₃) hF) ≫ (IC.isoRightDerivedObj v n).hom ≫ hvH.δ n (n + 1) rfl ≫ (IA.isoRightDerivedObj v (n + 1)).inv
```

DAG comparison reference: `the universal right-derived delta-functor construction`.

## Users

The downstream search found 526 transitive importers; none requires adaptation because
no Lean file or mathematical statement of the horseshoe construction changes. Its
direct declaration users and the new use in this delivery are listed below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor | unchanged | DAG comparison pointer only |
| Sheaf.CategoryTheory.Abelian.RightDerived.FilteredColimitSuccessor | unchanged | none |
| Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor | P1 | now uses the existing construction |

Every DAG citer is recorded holds:true in statement_change: lem-pc-derived-limit-roos-abelian-groups, lem-sc-p1-right-derived-triangle-connecting, lem-pc-tower-surjective-lim-acyclic, lem-weil-pbc-ml-cohomology-powers-ideal, lem-weil-pbc-site-cohomology-pullback, lem-sc-boundary-cech-injective-middle, lem-weil-pbc-right-derived-filtered-colimit-successor.

No target definition or target statement changes.

## Status

landed 20261012T053946-L-2642103 2026-10-12 (merge of deliver/P1/Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor)
