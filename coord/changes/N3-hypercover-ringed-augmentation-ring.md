# ringedHypercover_injective_augmentation_exact

## Reason

The original augmentation theorem required a sheaf of commutative rings. Its entire
free-module, local-cone, sheafification and injective-duality proof already used
RingCat. Move this proved argument and its private helpers into the new module
Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing, and state its true
arbitrary-ring generality there. This follows the one-new-statement-per-new-module
rule. Retain the original theorem as the commutative specialization, with exactly
its previous public signature and public imports. No private helper was exported.
The existing module was unclaimed when inspected. This is an interface
extension and proof relocation, with no new hole and no performance-driven split.

## Old

```lean
theorem ringedHypercover_injective_augmentation_exact
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.toGrothendieck.Subcanonical]
    (R : Sheaf J.toGrothendieck CommRingCat.{max u r})
    (I : ringedSiteModules.{max u v r}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R)) [Injective I]
    (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (hcover : ∀ (n : ℕ) (T : C) (w : T ⟶ W)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.obj (op Δ))),
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ e.app (op Δ) = w) →
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)) →
      ∃ S : Sieve T, S ∈ J.toGrothendieck T ∧
        ∀ (V : C) (f : V ⟶ T), S f →
          ∃ t : V ⟶ U _⦋n⦌,
            t ≫ e.app (op (SimplexCategory.mk n)) = f ≫ w ∧
            ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
              t ≫ U.map θ.op = f ≫ p Δ h θ) :
    Function.Injective (I.val.map (e.app (op (SimplexCategory.mk 0))).op) ∧
    Function.Exact
      (I.val.map (e.app (op (SimplexCategory.mk 0))).op)
      (fun s : I.val.obj (op (U _⦋0⦌)) ↦
        ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s) ∧
    ∀ n : ℕ, Function.Exact
      (fun s : I.val.obj (op (U _⦋n⦌)) ↦
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s)
      (fun s : I.val.obj (op (U _⦋n + 1⦌)) ↦
        ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s)
```

## New

The original signature above is identical. Its proof applies the following new
proved declaration to the underlying ring sheaf:

```lean
theorem ringedHypercover_injective_augmentation_exact_ring
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.toGrothendieck.Subcanonical]
    (R : Sheaf J.toGrothendieck RingCat.{max u r})
    (I : ringedSiteModules.{max u v r} R) [Injective I]
    (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (hcover : ∀ (n : ℕ) (T : C) (w : T ⟶ W)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.obj (op Δ))),
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ e.app (op Δ) = w) →
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)) →
      ∃ S : Sieve T, S ∈ J.toGrothendieck T ∧
        ∀ (V : C) (f : V ⟶ T), S f →
          ∃ t : V ⟶ U _⦋n⦌,
            t ≫ e.app (op (SimplexCategory.mk n)) = f ≫ w ∧
            ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
              t ≫ U.map θ.op = f ≫ p Δ h θ) :
    Function.Injective (I.val.map (e.app (op (SimplexCategory.mk 0))).op) ∧
    Function.Exact
      (I.val.map (e.app (op (SimplexCategory.mk 0))).op)
      (fun s : I.val.obj (op (U _⦋0⦌)) ↦
        ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s) ∧
    ∀ n : ℕ, Function.Exact
      (fun s : I.val.obj (op (U _⦋n⦌)) ↦
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s)
      (fun s : I.val.obj (op (U _⦋n + 1⦌)) ↦
        ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s)
```

The new theorem's proof is the original proof with the let-bound underlying ring
sheaf replaced by the supplied RingCat-valued sheaf. Every other construction and
local exactness proof is retained. Zero rings and empty bases are included.

## Users

The downstream.py --uses search finds these existing users. The original public
signature and public imports are identical, so no caller adaptation is forced.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation | unclaimed | Original theorem retained as a specialization; private proof machinery moves. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverInjectiveRow | unclaimed | Same commutative-ring theorem and statement; no edits. |
| Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing | N3, new | Proves arbitrary-ring exactness with the original explicit constructions. |
| Sheaf.Paper.HypercoverInjectiveModuleRow | N3, new | Uses arbitrary-ring exactness after constant-ring realization. |

No existing definition appearing in a target statement changes meaning. No forced
adaptation to a module held by another group is included.

## Status

landed 20261015T233749-L-3369289 2026-10-15 (merge of deliver/N3/Sheaf.Paper.HypercoverCohomologyModule)
