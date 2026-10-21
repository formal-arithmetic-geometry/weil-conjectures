# CategoryTheory.Mod.exists_cokernel_action

## Reason

Repair of the returned delivery based on `185674722`. The current repository
already contains the assigned module, created by `45eba2ae8c4`; it has the
following signature with proof `by sorry`. This delivery fills that proof and
preserves the complete current interface. This record corrects the obsolete
absent-module description retained from the first packet.

## Old

```lean
theorem exists_cokernel_action
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {R : C} [MonObj R]
    [PreservesFiniteColimits (tensorLeft R)]
    {M N : Mod C R} (f : M ⟶ N) {Q : C} (π : N.X ⟶ Q)
    (w : f.hom ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π w)) :
    ∃ (a : ModObj R Q),
      R ◁ π ≫ a.smul = ModObj.smul (M := R) (X := N.X) ≫ π ∧
      (∀ (γ : R ⊗ Q ⟶ Q),
        R ◁ π ≫ γ = ModObj.smul (M := R) (X := N.X) ≫ π → γ = a.smul) ∧
      ∃ (p : N ⟶ ({ X := Q, mod := a } : Mod C R)), p.hom = π ∧
        ∃ (wp : f ≫ p = 0), Nonempty (IsColimit (CokernelCofork.ofπ p wp))
```

## New

```lean
theorem exists_cokernel_action
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {R : C} [MonObj R]
    [PreservesFiniteColimits (tensorLeft R)]
    {M N : Mod C R} (f : M ⟶ N) {Q : C} (π : N.X ⟶ Q)
    (w : f.hom ≫ π = 0) (hπ : IsColimit (CokernelCofork.ofπ π w)) :
    ∃ (a : ModObj R Q),
      R ◁ π ≫ a.smul = ModObj.smul (M := R) (X := N.X) ≫ π ∧
      (∀ (γ : R ⊗ Q ⟶ Q),
        R ◁ π ≫ γ = ModObj.smul (M := R) (X := N.X) ≫ π → γ = a.smul) ∧
      ∃ (p : N ⟶ ({ X := Q, mod := a } : Mod C R)), p.hom = π ∧
        ∃ (wp : f ≫ p = 0), Nonempty (IsColimit (CokernelCofork.ofπ p wp))
```

The proof is complete, using cokernel preservation twice and the existing
module-object axioms. There are no new definitions, assumptions, or axioms.
The existing node attachment and the unit route are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ModuleObjectCokernelAction | G1 | Assigned theorem now fully proved. |

There is no interface change and no consumer adaptation. Existing DAG parents
still cite the cokernel node; their statements and dependency records remain
valid. All existing public imports, declarations and docstrings are preserved.

## Status

landed 20261021T111120-L-4146770 2026-10-21 (merge of deliver/G1/Sheaf.CategoryTheory.ModuleObjectCokernelAction)
