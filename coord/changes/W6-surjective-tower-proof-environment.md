# AlgebraicGeometry.ProEtale.proEtale_surjectiveTower_derivedLimit proof environment

## Reason

The proof needs two additional universe names for a generic private sheaf-lifting
lemma. Local backward transparency lets Lean match the definitionally identical
families `F n` and `(Functor.ofOpSequence t).obj (op n)` without unfolding the
canonical chosen limits. The main proof needs a larger heartbeat budget for its
large dependent conjunction; its measured single-file compile takes 25.2 seconds.
The original `hprod` binder in the statement is used only implicitly; a local
unused-variable linter option preserves that exact statement spelling.
All declaration signatures, existing binder names and public imports are unchanged.
The static preflight treats these command changes as an interface change.

## Old

```lean
universe t u w

theorem proEtale_surjectiveTower_derivedLimit
```

The unchanged full theorem declaration header is:

```lean
theorem proEtale_surjectiveTower_derivedLimit
    (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))]
    (F : ℕ → ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    (t : ∀ n : ℕ, F (n + 1) ⟶ F n) (ht : ∀ n : ℕ, Epi (t n)) :
    ∃ (hzero :
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) ≫
          towerTransitionEndomorphism t = 0)
      (hSES : (ShortComplex.mk
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n)))
        (towerTransitionEndomorphism t) hzero).ShortExact),
      Epi (towerTransitionEndomorphism t) ∧
      Nonempty (IsLimit (KernelFork.ofι
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) hzero)) ∧
      Nonempty (IsLimit (Fan.mk ((DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F))
        (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.π F n)))) ∧
      hSES.singleTriangle ∈ distTriang _ ∧
      (∀ [hprod : HasProduct (fun n : ℕ ↦
          (DerivedCategory.singleFunctor.{w} _ 0).obj (F n))],
        ∃ e : (DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F) ≅
            ∏ᶜ (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n)),
          (∀ n : ℕ, e.hom ≫
              Pi.π (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n)) n =
            (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.π F n)) ∧
          IsDerivedLimitTriangle
            (K := fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n))
            (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).map (t n))
            ((DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)))
            ((DerivedCategory.singleFunctor.{w} _ 0).map
              (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) ≫ e.hom)
            (e.inv ≫ hSES.singleδ)) ∧
      (∀ (G : ringedSiteModules.{max u (t + 1)}
          ((sheafCompose (Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
        (g : ∀ n : ℕ, G ⟶ F n), (∀ n : ℕ, g (n + 1) ≫ t n = g n) →
        ∃ (h₀ : G ⟶ limit (Functor.ofOpSequence t)),
          (∀ n : ℕ, h₀ ≫ limit.π (Functor.ofOpSequence t) (op n) = g n) ∧
          (∃! h : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
              (DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)),
            h ≫ (DerivedCategory.singleFunctor.{w} _ 0).map
                (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) =
              (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.lift g)) ∧
          (∀ h : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
              (DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)),
            h ≫ (DerivedCategory.singleFunctor.{w} _ 0).map
                (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) =
              (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.lift g) →
            h = (DerivedCategory.singleFunctor.{w} _ 0).map h₀) ∧
          (∀ k : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
            ((DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F))⟦(-1 : ℤ)⟧, k = 0))
```
There was no local elaboration option before this theorem.

## New

```lean
universe t u w v v'

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- The dependent conjunction transports several canonical limits through the degree-zero functor.
set_option backward.isDefEq.respectTransparency false in
theorem proEtale_surjectiveTower_derivedLimit
```

The New full declaration header is identical to the Old header above.
No statement or definition changes. The extra universes occur only in private
helpers; the two existing public instances and theorem have the same universes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
--uses AlgebraicGeometry.ProEtale.proEtale_surjectiveTower_derivedLimit` reports
831 transitive importers, with no explicit declaration consumer outside this module.
All keep the same statements, definitions and elaborated interfaces. No consumer
requires adaptation. The only textual hit is the declaration itself.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit | W6 | Proof completed; signature unchanged |

No target statement or target-used definition changes, so no target statement
review is reopened. No module held by another group is edited.

## Status

landed 20261019T034339-L-423911 2026-10-19 (merge of deliver/W6/Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit)
