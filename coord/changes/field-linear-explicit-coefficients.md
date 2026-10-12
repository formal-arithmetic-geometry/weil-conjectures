# scalarUnitLinear and scalarTensorCoefficient

## Reason

The human ruling of 2026-10-12 forbids data chosen from unproved existence.
These two coefficient maps have direct constructions.

## Old

```lean
def scalarUnitLinear : ModuleCat.of k k ⟶
    (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op ⊤) :=
  Classical.choose (exists_scalarUnitLinear f)
```

```lean
theorem exists_scalarUnitLinear :
    ∃ η : ModuleCat.of k k ⟶
        (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op ⊤),
      ∀ r : k, η r = scalarMap f ⊤ r := by
  sorry
```

```lean
def scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    scalarSheaf f F ⊗ scalarSheaf f G ⟶ scalarSheaf f (F ⊗ G) :=
  Classical.choose (exists_scalarTensorCoefficient f F G)
```

```lean
theorem exists_scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    ∃ τ : scalarSheaf f F ⊗ scalarSheaf f G ⟶ scalarSheaf f (F ⊗ G),
      ∀ (U : X.Opens) (s : scalarObj f F (op U)) (t : scalarObj f G (op U)),
        τ.hom.app (op U)
          (((Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
            (ModuleCat.{u} k)) (scalarSheaf f F) (scalarSheaf f G)).app (op U))
              (s ⊗ₜ[k] t)) = tmulSection s t := by
  sorry
```

## New

```lean
def scalarUnitLinear : ModuleCat.of k k ⟶
    (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op ⊤) :=
  letI : Module k ((SheafOfModules.unit X.ringCatSheaf).val.obj (op ⊤)) :=
    Module.compHom _ (scalarMap f ⊤)
  ModuleCat.ofHom
    { toFun := fun r : k ↦ scalarMap f ⊤ r
      map_add' := fun r s ↦ (scalarMap f ⊤).map_add r s
      map_smul' := by
        intro r s
        change scalarMap f ⊤ (r * s) = scalarMap f ⊤ r * scalarMap f ⊤ s
        exact (scalarMap f ⊤).map_mul r s }
```

```lean
theorem exists_scalarUnitLinear (r : k) : scalarUnitLinear f r = scalarMap f ⊤ r := by
  rfl
```

```lean
def scalarTensorCoefficientApp (F G : SheafOfModules.{u} X.ringCatSheaf)
    (U : (Opens X)ᵒᵖ) :
    scalarObj f F U ⊗ scalarObj f G U ⟶ scalarObj f (F ⊗ G) U :=
  letI : Module k (F.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k (G.val.obj U) := Module.compHom _ (scalarMap f U.unop)
  letI : Module k ((F ⊗ G).val.obj U) := Module.compHom _ (scalarMap f U.unop)
  ModuleCat.MonoidalCategory.tensorLift (fun s t ↦ tmulSection s t)
    (fun s s' t ↦ add_tmulSection s s' t)
    (fun r s t ↦ smul_tmulSection (scalarMap f U.unop r) s t)
    (fun s t t' ↦ tmulSection_add s t t')
    (fun r s t ↦ tmulSection_smul (scalarMap f U.unop r) s t)
```

```lean
theorem scalarTensorCoefficientApp_naturality (F G : SheafOfModules.{u} X.ringCatSheaf)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (scalarPresheaf f F ⊗ scalarPresheaf f G).map i ≫
        scalarTensorCoefficientApp f F G V =
      scalarTensorCoefficientApp f F G U ≫ (scalarPresheaf f (F ⊗ G)).map i := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change tmulSection ((F.val.map i).hom s) ((G.val.map i).hom t) =
    ((F ⊗ G).val.map i).hom (tmulSection s t)
  exact (tmulSection_map (leOfHom i.unop) s t).symm
```

```lean
def scalarTensorPresheafCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    scalarPresheaf f F ⊗ scalarPresheaf f G ⟶ scalarPresheaf f (F ⊗ G) where
  app := scalarTensorCoefficientApp f F G
  naturality := fun _ _ i ↦ scalarTensorCoefficientApp_naturality f F G i
```

```lean
def scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    scalarSheaf f F ⊗ scalarSheaf f G ⟶ scalarSheaf f (F ⊗ G) :=
  (Sheaf.tensorLeftIso (scalarSheaf f F)).hom.app (scalarSheaf f G) ≫
    ((CategoryTheory.sheafificationAdjunction
      (Opens.grothendieckTopology X) (ModuleCat.{u} k)).homEquiv _ _).symm
        (scalarTensorPresheafCoefficient f F G)
```

```lean
theorem exists_scalarTensorCoefficient (F G : SheafOfModules.{u} X.ringCatSheaf) :
    ∀ (U : X.Opens) (s : scalarObj f F (op U)) (t : scalarObj f G (op U)),
      (scalarTensorCoefficient f F G).hom.app (op U)
        (((Functor.LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology X)
          (ModuleCat.{u} k)) (scalarSheaf f F) (scalarSheaf f G)).app (op U))
            (s ⊗ₜ[k] t)) = tmulSection s t := by
  sorry
```

The tensor existence theorem is now the characterization of the explicit map;
the old name is retained. The unit existence theorem is restated as the reflexive formula theorem,
retaining its legacy name. No target signature or TeX mathematical statement changes.
The node's Lean declaration list records the new construction and formula theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations | Z2 | Internal uses retain the same morphism types; existence choices removed. |

The four `downstream.py --uses` checks for scalarUnitLinear, scalarTensorCoefficient,
exists_scalarUnitLinear and exists_scalarTensorCoefficient list only this module.
No external user needs source adaptation. Downstream targets using these definitions
need the normal renewed semantic review; the intended coefficient formulas are unchanged.

## Status

landed 20261012T135340-L-1703279 2026-10-12 (merge of deliver/Z2/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
