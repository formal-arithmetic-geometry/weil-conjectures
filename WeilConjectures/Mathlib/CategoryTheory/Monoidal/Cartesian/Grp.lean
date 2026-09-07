/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Power endomorphisms and kernels of group objects

Let `G` be a group object in a cartesian monoidal category `C`. Since `X ⟶ G` is a group
for every `X` (`CategoryTheory.Hom.group`), the identity of `G` has powers, and the `n`-th
power of the identity is the endomorphism of `G` that is `x ↦ xⁿ` on points.

If moreover `C` has pullbacks, every homomorphism `f : G ⟶ H` of group objects has a kernel:
the fibre of `f` over the identity section of `H`, i.e. the pullback of `f` along the unit
`η[H] : 𝟙_ C ⟶ H`. Since `𝟙_ C` is terminal, its `T`-points are exactly the `T`-points of `G`
that are killed by `f`, and this is how it is given its group object structure.

## Main definitions

- `CategoryTheory.GrpObj.npow`: the endomorphism `x ↦ xⁿ` of `G`, for `n : ℕ`.
- `CategoryTheory.GrpObj.zpow`: the endomorphism `x ↦ xⁿ` of `G`, for `n : ℤ`.
- `CategoryTheory.GrpObj.ker`: the kernel of a homomorphism `f : G ⟶ H` of group objects,
  together with its group object structure and the inclusion
  `CategoryTheory.GrpObj.kerι : ker f ⟶ G`.

## Main results

- `CategoryTheory.GrpObj.comp_npow`: composing an `X`-point `f` of `G` with `npow G n` is
  the `n`-th power of `f` in the group `X ⟶ G`. All other properties of `npow` follow from
  this one and the group axioms in `X ⟶ G`.
- `CategoryTheory.GrpObj.instIsMonHomNpow`: `npow G n` is a morphism of monoid objects if
  `G` is commutative.
- `CategoryTheory.GrpObj.kerHomMulEquiv`: the universal property of the kernel on points, as
  an isomorphism of groups `(T ⟶ ker f) ≃* (IsMonHom.monoidHom f T).ker`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {G H X : C}
  [GrpObj G] [GrpObj H]

open scoped MonObj AddMonObj

namespace GrpObj

variable (G) in
/-- The `n`-th power endomorphism `x ↦ xⁿ` of a group object `G`. -/
@[to_additive /-- The endomorphism `x ↦ n • x` of an additive group object `G`. -/]
def npow (n : ℕ) : G ⟶ G := (𝟙 G) ^ n

variable (G) in
/-- The `n`-th power endomorphism `x ↦ xⁿ` of a group object `G`, for `n : ℤ`. -/
@[to_additive /-- The endomorphism `x ↦ n • x` of an additive group object `G`,
for `n : ℤ`. -/]
def zpow (n : ℤ) : G ⟶ G := (𝟙 G) ^ n

/-- On `X`-points, `npow G n` is the `n`-th power map: this is the defining property of
`npow G n`. -/
@[to_additive (attr := reassoc) /-- On `X`-points, `nsmul G n` is multiplication by `n`: this
is the defining property of `nsmul G n`. -/]
lemma comp_npow (f : X ⟶ G) (n : ℕ) : f ≫ npow G n = f ^ n := by
  rw [npow, MonObj.comp_pow, Category.comp_id]

/-- On `X`-points, `zpow G n` is the `n`-th power map. The name is primed to avoid a clash
with `CategoryTheory.GrpObj.comp_zpow`, which is about powers of a point rather than about
the endomorphism `zpow G n`. -/
@[to_additive (attr := reassoc) /-- On `X`-points, `zsmul G n` is multiplication by `n`. The name
is primed to avoid a clash with `CategoryTheory.AddGrpObj.comp_zsmul`, which is about multiples
of a point rather than about the endomorphism `zsmul G n`. -/]
lemma comp_zpow' (f : X ⟶ G) (n : ℤ) : f ≫ zpow G n = f ^ n := by
  rw [zpow, GrpObj.comp_zpow, Category.comp_id]

variable (G)

@[to_additive (attr := simp)]
lemma npow_zero : npow G 0 = toUnit G ≫ η := by
  rw [npow, pow_zero, Hom.one_def]

@[to_additive (attr := simp) nsmul_one]
lemma npow_one : npow G 1 = 𝟙 G :=
  pow_one _

@[to_additive]
lemma npow_add (m n : ℕ) : npow G (m + n) = lift (npow G m) (npow G n) ≫ μ := by
  rw [← Hom.mul_def, npow, npow, npow, pow_add]

@[to_additive (attr := reassoc)]
lemma npow_comp_npow (m n : ℕ) : npow G m ≫ npow G n = npow G (m * n) := by
  rw [comp_npow, npow, npow, pow_mul]

@[to_additive (attr := simp)]
lemma zpow_natCast (n : ℕ) : zpow G (n : ℤ) = npow G n :=
  _root_.zpow_natCast (𝟙 G) n

@[to_additive (attr := simp) zsmul_neg_one]
lemma zpow_neg_one : zpow G (-1) = ι :=
  (_root_.zpow_neg_one (𝟙 G)).trans inv_eq_inv.symm

variable {G}

/-- The power endomorphisms are natural in the group object. -/
@[to_additive (attr := reassoc) /-- The multiplication by `n` endomorphisms are natural in the
additive group object. -/]
lemma npow_comp (n : ℕ) (f : G ⟶ H) [IsMonHom f] : npow G n ≫ f = f ≫ npow H n := by
  rw [npow, MonObj.pow_comp, Category.id_comp, comp_npow]

/-- The power endomorphisms are natural in the group object. The name is primed to avoid a
clash with `CategoryTheory.GrpObj.zpow_comp`. -/
@[to_additive (attr := reassoc) /-- The multiplication by `n` endomorphisms are natural in the
additive group object. The name is primed to avoid a clash with
`CategoryTheory.AddGrpObj.zsmul_comp`. -/]
lemma zpow_comp' (n : ℤ) (f : G ⟶ H) [IsMonHom f] : zpow G n ≫ f = f ≫ zpow H n := by
  rw [zpow, GrpObj.zpow_comp, Category.id_comp, comp_zpow']

section Braided

variable [BraidedCategory C] [IsCommMonObj G]

/-- If `G` is a commutative group object, the `n`-th power endomorphism of `G` is a morphism
of monoid objects. -/
@[to_additive /-- If `G` is a commutative additive group object, multiplication by `n` on `G`
is a morphism of additive monoid objects. -/]
instance (n : ℕ) : IsMonHom (npow G n) where
  one_hom := by rw [comp_npow, MonObj.one_eq_one, one_pow]
  mul_hom := by
    have : (npow G n ⊗ₘ npow G n) ≫ μ = (fst G G ≫ npow G n) * (snd G G ≫ npow G n) := by
      rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
    rw [this]
    simp only [comp_npow]
    rw [← mul_pow, ← MonObj.mul_eq_mul]

/-- If `G` is a commutative group object, the `n`-th power endomorphism of `G` is a morphism
of monoid objects, for `n : ℤ`. -/
@[to_additive /-- If `G` is a commutative additive group object, multiplication by `n : ℤ` on
`G` is a morphism of additive monoid objects. -/]
instance (n : ℤ) : IsMonHom (zpow G n) where
  one_hom := by rw [comp_zpow', MonObj.one_eq_one, one_zpow]
  mul_hom := by
    have : (zpow G n ⊗ₘ zpow G n) ≫ μ = (fst G G ≫ zpow G n) * (snd G G ≫ zpow G n) := by
      rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
    rw [this]
    simp only [comp_zpow']
    rw [← mul_zpow, ← MonObj.mul_eq_mul]

end Braided

noncomputable section Ker

open Limits Opposite

variable [HasPullbacks C] (f : G ⟶ H)

/-- The kernel of a homomorphism `f : G ⟶ H` of group objects: the fibre of `f` over the
identity section of `H`, i.e. the pullback of `f` along the unit `η[H] : 𝟙_ C ⟶ H`. -/
@[to_additive /-- The kernel of a homomorphism `f : G ⟶ H` of additive group objects: the fibre
of `f` over the zero section of `H`, i.e. the pullback of `f` along the unit
`η[H] : 𝟙_ C ⟶ H`. -/]
def ker : C := pullback f η[H]

/-- The inclusion of the kernel of `f : G ⟶ H` into `G`. -/
@[to_additive /-- The inclusion of the kernel of `f : G ⟶ H` into `G`. -/]
def kerι : ker f ⟶ G := pullback.fst f η[H]

section

omit [GrpObj G]

/-- The kernel of `f` is the fibre of `f` over the identity section of `H`. -/
@[to_additive /-- The kernel of `f` is the fibre of `f` over the zero section of `H`. -/]
lemma isPullback_kerι : IsPullback (kerι f) (toUnit (ker f)) f η[H] := by
  have h := IsPullback.of_hasPullback f η[H]
  rwa [toUnit_unique (pullback.snd f η[H]) (toUnit (ker f))] at h

@[to_additive (attr := reassoc)]
lemma kerι_comp : kerι f ≫ f = toUnit (ker f) ≫ η[H] :=
  (isPullback_kerι f).w

@[to_additive (attr := simp)]
lemma kerι_comp_eq_one : kerι f ≫ f = 1 :=
  kerι_comp f

/-- The inclusion of the kernel into `G` is a monomorphism, since the identity section of `H`
is one. -/
@[to_additive /-- The inclusion of the kernel into `G` is a monomorphism, since the zero section
of `H` is one. -/]
instance : Mono (kerι f) :=
  inferInstanceAs (Mono (pullback.fst f η[H]))

end

variable [IsMonHom f]

/-- The presheaf of groups sending `T` to the kernel of the group homomorphism
`(T ⟶ G) →* (T ⟶ H)` induced by `f`, i.e. to the subgroup of `T`-points of `G` killed by `f`.
It is represented by `GrpObj.ker f`, see `GrpObj.kerFunctorRepresentableBy`. -/
@[to_additive /-- The presheaf of additive groups sending `T` to the kernel of the additive
group homomorphism `(T ⟶ G) →+ (T ⟶ H)` induced by `f`, i.e. to the subgroup of `T`-points
of `G` killed by `f`. It is represented by `AddGrpObj.ker f`, see
`AddGrpObj.kerFunctorRepresentableBy`. -/]
def kerFunctor : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (IsMonHom.monoidHom f (unop T)).ker
  map {T T'} φ := GrpCat.ofHom
    { toFun a := ⟨φ.unop ≫ a.1, by
        simp only [MonoidHom.mem_ker, IsMonHom.monoidHom_apply, Category.assoc]
        rw [show a.1 ≫ f = 1 from MonoidHom.mem_ker.mp a.2, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' a b := Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun a ↦ Subtype.ext (Category.id_comp a.1))
  map_comp φ ψ := GrpCat.hom_ext (MonoidHom.ext fun a ↦ Subtype.ext (Category.assoc _ _ _))

/-- The universal property of the kernel: `ker f` represents the presheaf `kerFunctor f`, i.e.
a `T`-point of `ker f` is the same thing as a `T`-point `a` of `G` with `a ≫ f = 1`. -/
@[to_additive /-- The universal property of the kernel: `ker f` represents the presheaf
`kerFunctor f`, i.e. a `T`-point of `ker f` is the same thing as a `T`-point `a` of `G` with
`a ≫ f = 0`. -/]
def kerFunctorRepresentableBy : (kerFunctor f ⋙ forget _).RepresentableBy (ker f) where
  homEquiv {T} :=
    { toFun a := ⟨a ≫ kerι f, by simp [MonoidHom.mem_ker]⟩
      invFun a := pullback.lift a.1 (toUnit T)
        (by rw [show a.1 ≫ f = 1 from MonoidHom.mem_ker.mp a.2, Hom.one_def])
      left_inv a := pullback.hom_ext (pullback.lift_fst _ _ _) (toUnit_unique _ _)
      right_inv a := Subtype.ext (pullback.lift_fst _ _ _) }
  homEquiv_comp g b := Subtype.ext (Category.assoc _ _ _)

/-- The kernel of a homomorphism of group objects is a group object. -/
@[to_additive /-- The kernel of a homomorphism of additive group objects is an additive
group object. -/]
instance : GrpObj (ker f) :=
  .ofRepresentableBy _ (kerFunctor f) (kerFunctorRepresentableBy f)

/-- The universal property of the kernel, as an isomorphism of groups: the `T`-points of
`ker f` are exactly the `T`-points of `G` killed by `f`. -/
@[to_additive /-- The universal property of the kernel, as an isomorphism of additive groups:
the `T`-points of `ker f` are exactly the `T`-points of `G` killed by `f`. -/]
def kerHomMulEquiv (T : C) : (T ⟶ ker f) ≃* (IsMonHom.monoidHom f T).ker where
  __ := (kerFunctorRepresentableBy f).homEquiv
  map_mul' a b := ((yonedaGrpObjIsoOfRepresentableBy (ker f) (kerFunctor f)
    (kerFunctorRepresentableBy f)).hom.app (op T)).hom.map_mul a b

@[to_additive (attr := simp)]
lemma coe_kerHomMulEquiv {T : C} (a : T ⟶ ker f) :
    ((kerHomMulEquiv f T a : (IsMonHom.monoidHom f T).ker) : T ⟶ G) = a ≫ kerι f :=
  rfl

@[to_additive (attr := reassoc)]
lemma mul_comp_kerι {T : C} (a b : T ⟶ ker f) :
    (a * b) ≫ kerι f = (a ≫ kerι f) * (b ≫ kerι f) :=
  congrArg Subtype.val ((kerHomMulEquiv f T).map_mul a b)

@[to_additive (attr := simp)]
lemma one_comp_kerι {T : C} : (1 : T ⟶ ker f) ≫ kerι f = 1 :=
  congrArg Subtype.val (kerHomMulEquiv f T).map_one

/-- The inclusion of the kernel into `G` is a homomorphism of group objects. -/
@[to_additive /-- The inclusion of the kernel into `G` is a homomorphism of additive group
objects. -/]
instance : IsMonHom (kerι f) where
  one_hom := by
    have h := one_comp_kerι (T := 𝟙_ C) f
    rwa [Hom.one_def, Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 (𝟙_ C)),
      Category.id_comp, Category.id_comp] at h
  mul_hom := by
    have h : (kerι f ⊗ₘ kerι f) ≫ μ =
        (fst (ker f) (ker f) ≫ kerι f) * (snd (ker f) (ker f) ≫ kerι f) := by
      rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
    rw [h, ← mul_comp_kerι, ← MonObj.mul_eq_mul]

end Ker

end GrpObj

end CategoryTheory
