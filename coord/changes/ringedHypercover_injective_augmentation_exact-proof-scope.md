# CategoryTheory.ringedHypercover_injective_augmentation_exact

## Reason

The conservative interface check flags added namespace and variable commands used to scope
private proof helpers. This record documents those commands. No existing public signature,
public definition, or public import changes; no global instance is added. The sole original
proof hole is closed. No downstream module is adapted.

## Old

The module had its original `universe u v r`, `open CategoryTheory Opposite`,
`open scoped Simplicial`, and `namespace CategoryTheory` commands. The original signature is:

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

The original signature remains verbatim:

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

Before the original namespace, three closed `namespace CategoryTheory.RingedHypercover`
blocks scope private helpers. Their local variable declarations are:

```lean
variable {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{r})
variable (J : GrothendieckTopology C) (S : Sheaf J RingCat.{r})
```

in the first block, and

```lean
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (R : Cᵒᵖ ⥤ RingCat.{r})
```

in each of the other two blocks. All helpers in these scopes are private. Each block ends
before the original `namespace CategoryTheory` and target declaration. Instance arguments
needed by private proofs are supplied inside those proofs. Consequently the existing theorem
has the identical elaborated signature and no existing target meaning changes.

The new, separate `Sheaf.CategoryTheory.RingedHypercoverFiniteCones` module exposes its
proved finite-cone statement and local-edge specialization. It is a private proof import of
the original module. Its node records the geometric finite-support argument.

## Users

The downstream list was obtained with
`tools/downstream.py Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation --uses
ringedHypercover_injective_augmentation_exact`. All original downstream modules retain their
source unchanged. None needs an adaptation because every existing public signature and
public import is unchanged. Group holders below are the repository claim snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation | D2 | Private proof helpers added; original public signature unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | No adaptation: existing public signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | No adaptation: existing public signature and public imports unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No adaptation: existing public signature and public imports unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | No adaptation: existing public signature and public imports unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | No adaptation: existing public signature and public imports unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No adaptation: existing public signature and public imports unchanged. |
| TargetsCheck | unclaimed | No adaptation: existing public signature and public imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No adaptation: existing public signature and public imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | No adaptation: existing public signature and public imports unchanged. |

## Status

landed 20261015T154159-L-160685 2026-10-15 (merge of deliver/D2/Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation)
