# CategoryTheory.ringedHypercover_injective_augmentation_exact_ring

## Reason

The pro-etale site's objects live in universe t+1 while a ring sheaf may live
in an independent smaller universe u. After transporting the hom universe
with ULiftHom, the existing RingCat.{max u r} binder still forces the ring
universe to contain the site universe. The module's explicit free-module and
sheafification constructions already support independent ring universe r.
Generalize only the public theorem's ring binder and the two corresponding
proof annotations. The module is unclaimed. The mathematical statement,
local matching condition, module universe and conclusion are unchanged.
No data is chosen from an unproved existence theorem.

## Old

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

Proof annotations: `let S : Sheaf K RingCat.{max u r} := R` and
`RingedHypercover.freeSheafFunctor.{u, v, max u r} K S`.

## New

```lean
theorem ringedHypercover_injective_augmentation_exact_ring
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.toGrothendieck.Subcanonical]
    (R : Sheaf J.toGrothendieck RingCat.{r})
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

Proof annotations: `let S : Sheaf K RingCat.{r} := R` and
`RingedHypercover.freeSheafFunctor.{u, v, r} K S`.

## Users

The downstream scan found two pre-existing external callers. Their signatures
and proofs are retained. For the commutative specialization, inference now
sets the theorem's r to max u r; max u v (max u r) is the same module universe.
The explicitly instantiated paper caller uses equal universes, hence is
unchanged. The item is the new caller requiring independent universes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing | unclaimed | Generalized theorem; existing private constructions unchanged. |
| Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation | unclaimed | Same mathematical statement and proof; inferred ring universe specializes to max u r. |
| Sheaf.Paper.HypercoverInjectiveModuleRow | unclaimed | Equal-universe explicit call remains identical. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex | C8 | New arbitrary-ring caller at site universe t+1, ring universe u. |

No target signature or definition used in a target changes. This is a theorem
universe generalization, with no modification of objects or restriction maps.
The node's Lean attachment is synchronized; its natural-language statement
already allowed arbitrary ring sheaves.

## Status

landed 20261019T002519-L-2145648 2026-10-19 (merge of deliver/C8/Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex)
