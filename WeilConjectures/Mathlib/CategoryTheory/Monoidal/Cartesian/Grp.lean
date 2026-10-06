/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Kernels of morphisms of group objects

In a cartesian monoidal category with pullbacks, the kernel of a morphism `f : G ⟶ H` of
group objects is the fibre product of `f` and the unit `η[H] : 𝟙_ C ⟶ H`:

```
  ker f ──── kerι f ────▶ G
    │                     │
    │ toUnit              │ f
    ▼                     ▼
   𝟙_ C ──── η[H] ──────▶ H
```

## Main definitions

- `CategoryTheory.GrpObj.ker`: the kernel of a morphism of group objects.
- `CategoryTheory.GrpObj.kerι`: its canonical morphism to the source.
- `CategoryTheory.GrpObj.kerLift`: the universal property of the kernel.
- `CategoryTheory.GrpObj.kerPresheaf`: the presheaf of groups that `ker f` represents.
- `CategoryTheory.GrpObj.instGrpObjKer`: the group structure on `ker f`.

## Main statements

- `CategoryTheory.GrpObj.isPullback_kerι`: the square above is cartesian.
- `CategoryTheory.GrpObj.isMonHom_kerι`: `kerι f` is a morphism of group objects.
- `CategoryTheory.GrpObj.isPullback_ker_tensor`: translation by a `T`-point `x` of `G`
  identifies the fibre of `f` over `x ≫ f` with `ker f ⊗ T`.

For `f` a morphism of group objects, `ker f` is itself a group object: it represents the
presheaf of groups `Y ↦ ker ((· ≫ f) : (Y ⟶ G) →* (Y ⟶ H))`, and `kerι f` is a morphism of
group objects.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

namespace GrpObj

-- `GrpObj G` is deliberately not assumed: the kernel is the fibre product of `f` with the unit
-- of `H`, which needs only the group structure of the target.
variable {G H : C} [GrpObj H]

/-- The kernel of a morphism `f : G ⟶ H` of group objects: the fibre product of `f` with the
unit `η[H] : 𝟙_ C ⟶ H`. For group schemes over a field this is the kernel subgroup scheme.

```
  ker f ──── kerι f ────▶ G
    │                     │
    │ toUnit              │ f
    ▼                     ▼
   𝟙_ C ──── η[H] ──────▶ H
```
-/
noncomputable def ker (f : G ⟶ H) [HasPullback f η[H]] : C := pullback f η[H]

/-- The canonical morphism from the kernel of `f : G ⟶ H` to `G`, the left-hand edge of the
cartesian square defining `CategoryTheory.GrpObj.ker`. -/
noncomputable def kerι (f : G ⟶ H) [HasPullback f η[H]] : ker f ⟶ G := pullback.fst _ _

/-- The defining square of the kernel commutes: the composite `ker f ⟶ G ⟶ H` is the unit. -/
@[reassoc]
theorem kerι_comp (f : G ⟶ H) [HasPullback f η[H]] :
    kerι f ≫ f = toUnit (ker f) ≫ η[H] := by
  rw [kerι, pullback.condition]
  congr 1
  exact toUnit_unique _ _

/-- The defining square of the kernel is cartesian. -/
theorem isPullback_kerι (f : G ⟶ H) [HasPullback f η[H]] :
    IsPullback (kerι f) (toUnit (ker f)) f η[H] := by
  rw [toUnit_unique (toUnit (ker f)) (pullback.snd f η[H])]
  exact IsPullback.of_hasPullback f η[H]

/-- The universal property of the kernel: a morphism `g : X ⟶ G` whose composite with `f` is the
unit factors uniquely through `ker f`. -/
noncomputable def kerLift (f : G ⟶ H) [HasPullback f η[H]] {X : C} (g : X ⟶ G)
    (hg : g ≫ f = toUnit X ≫ η[H]) : X ⟶ ker f :=
  pullback.lift g (toUnit X) hg

@[reassoc (attr := simp)]
theorem kerLift_kerι (f : G ⟶ H) [HasPullback f η[H]] {X : C} (g : X ⟶ G)
    (hg : g ≫ f = toUnit X ≫ η[H]) : kerLift f g hg ≫ kerι f = g :=
  pullback.lift_fst _ _ _

theorem kerLift_unique (f : G ⟶ H) [HasPullback f η[H]] {X : C} (g : X ⟶ G)
    (hg : g ≫ f = toUnit X ≫ η[H]) (l : X ⟶ ker f) (hl : l ≫ kerι f = g) :
    l = kerLift f g hg := by
  refine pullback.hom_ext ?_ (toUnit_unique _ _)
  change l ≫ kerι f = kerLift f g hg ≫ kerι f
  rw [hl, kerLift_kerι]

section GroupStructure

variable [GrpObj G] (f : G ⟶ H) [IsMonHom f]

/-- The presheaf of groups represented by the kernel of `f : G ⟶ H`: it sends `Y` to the kernel
of the group homomorphism `(· ≫ f) : (Y ⟶ G) →* (Y ⟶ H)`. -/
def kerPresheaf : Cᵒᵖ ⥤ GrpCat.{v} where
  obj Y := GrpCat.of (MonoidHom.ker (IsMonHom.monoidHom f (unop Y)))
  map {Y Z} φ := GrpCat.ofHom
    { toFun g := ⟨φ.unop ≫ g.1, by
        rw [MonoidHom.mem_ker]
        change (φ.unop ≫ g.1) ≫ f = 1
        rw [Category.assoc, show g.1 ≫ f = 1 from MonoidHom.mem_ker.mp g.2, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one φ.unop)
      map_mul' a b := Subtype.ext (MonObj.comp_mul φ.unop a.1 b.1) }
  map_id Y := by ext g; exact Category.id_comp g.1
  map_comp {Y Z W} φ ψ := by ext g; exact Category.assoc ψ.unop φ.unop g.1

/-- The kernel of `f : G ⟶ H` represents `CategoryTheory.GrpObj.kerPresheaf f`. -/
noncomputable def kerRepresentableBy [HasPullback f η[H]] :
    (kerPresheaf f ⋙ forget _).RepresentableBy (ker f) where
  homEquiv {Y} :=
    { toFun l := ⟨l ≫ kerι f, by
        rw [MonoidHom.mem_ker]
        change (l ≫ kerι f) ≫ f = toUnit Y ≫ η[H]
        rw [Category.assoc, kerι_comp, ← Category.assoc,
          toUnit_unique (l ≫ toUnit (ker f)) (toUnit Y)]⟩
      invFun g := kerLift f g.1 (MonoidHom.mem_ker.mp g.2)
      left_inv l := (kerLift_unique f _ _ l rfl).symm
      right_inv g := Subtype.ext (kerLift_kerι _ _ _) }
  homEquiv_comp φ l := Subtype.ext (Category.assoc _ _ _)

/-- The kernel of a morphism of group objects is a group object. -/
noncomputable instance instGrpObjKer [HasPullback f η[H]] : GrpObj (ker f) :=
  GrpObj.ofRepresentableBy _ (kerPresheaf f) (kerRepresentableBy f)

/-- The `n`-th coordinate description of the group structure on `ker f`: the isomorphism of
`CategoryTheory.GrpObj.kerRepresentableBy` sends `l` to `l ≫ kerι f`. -/
theorem homEquiv'_kerRepresentableBy [HasPullback f η[H]] {Y : C} (l : Y ⟶ ker f) :
    ((kerRepresentableBy f).homEquiv' l).1 = l ≫ kerι f :=
  rfl

/-- The inclusion of the kernel into the source is a morphism of group objects. -/
instance isMonHom_kerι [HasPullback f η[H]] : IsMonHom (kerι f) where
  one_hom := by
    have h1 : (kerRepresentableBy f).homEquiv' (η[ker f]) = 1 :=
      (kerRepresentableBy f).homEquiv'.apply_symm_apply 1
    rw [← homEquiv'_kerRepresentableBy f (η[ker f]), h1]
    simpa using _root_.CategoryTheory.Hom.one_def (X := 𝟙_ C) (M := G)
  mul_hom := by
    have h1 : (kerRepresentableBy f).homEquiv' (μ[ker f]) =
        (kerRepresentableBy f).homEquiv' (fst (ker f) (ker f)) *
          (kerRepresentableBy f).homEquiv' (snd (ker f) (ker f)) :=
      (kerRepresentableBy f).homEquiv'.apply_symm_apply _
    rw [← homEquiv'_kerRepresentableBy f (μ[ker f]), h1, Subgroup.coe_mul,
      homEquiv'_kerRepresentableBy, homEquiv'_kerRepresentableBy, _root_.CategoryTheory.Hom.mul_def,
      lift_fst_comp_snd_comp]

/-- Translation identifies the fibres of a morphism of group objects with its kernel: for
`x : T ⟶ G`, the square
```
  ker f ⊗ T ──── (k, t) ↦ k * x t ────▶ G
      │                                 │
      │ snd                             │ f
      ▼                                 ▼
      T ─────────── x ≫ f ────────────▶ H
```
is cartesian, so the fibre of `f` over the `T`-point `x ≫ f` of `H` is `ker f ⊗ T`. -/
theorem isPullback_ker_tensor [HasPullback f η[H]] {T : C} (x : T ⟶ G) :
    IsPullback ((fst (ker f) T ≫ kerι f) * (snd (ker f) T ≫ x)) (snd (ker f) T) f (x ≫ f) := by
  have hk : kerι f ≫ f = 1 := by rw [kerι_comp, Hom.one_def]
  refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ lift (kerLift f (s.fst * (s.snd ≫ x)⁻¹) ?_) s.snd) ?_ ?_ ?_)
  · rw [MonObj.mul_comp, Category.assoc, hk, MonObj.comp_one, _root_.one_mul, Category.assoc]
  · rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, Category.assoc, mul_inv_cancel, Hom.one_def]
  · intro s
    simp [MonObj.comp_mul]
  · intro s
    simp
  · intro s m h₁ h₂
    refine hom_ext _ _ ?_ (by simpa using h₂)
    simp only [lift_fst]
    refine kerLift_unique _ _ _ _ ?_
    rw [← h₁, ← h₂, MonObj.comp_mul, Category.assoc, Category.assoc, mul_inv_cancel_right]

end GroupStructure

end GrpObj

end CategoryTheory
