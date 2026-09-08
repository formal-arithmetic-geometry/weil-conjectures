/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Mathlib.RingTheory.TensorProduct.Basic

/-!
# Fibre products of affine schemes over the terminal scheme

`Mathlib.AlgebraicGeometry.Pullbacks` computes the fibre product of `Spec A` and `Spec B` over
`Spec R` as `Spec (A ⊗[R] B)`. Since `Spec (ULift ℤ)` is a terminal scheme, this also computes
the fibre product over the terminal scheme `⊤_ Scheme`, which is the shape in which products of
schemes appear in practice.

## Main declarations

* `AlgebraicGeometry.isPullback_terminalFrom_spec`: the square with projections
  `Spec (A ⊗[ULift ℤ] B) ⟶ Spec A` and `Spec (A ⊗[ULift ℤ] B) ⟶ Spec B` over `⊤_ Scheme` is
  cartesian.
* `AlgebraicGeometry.pullbackTerminalSpecIso`: the induced isomorphism
  `pullback (terminal.from (Spec A)) (terminal.from (Spec B)) ≅ Spec (A ⊗[ULift ℤ] B)`.
* `AlgebraicGeometry.closure_range_mul_appTop_eq_top`: the global sections of a product of two
  affine schemes are generated as a ring by the products of pullbacks of generators of the two
  factors.
* `AlgebraicGeometry.Scheme.Pullback.opensRange_map`: the range of the map of fibre products
  induced by two open immersions is the intersection of the preimages of their ranges, and its
  variant `AlgebraicGeometry.Scheme.Pullback.opensRange_openCoverOfLeftRight_f` for the charts
  of the product of two open covers.

Note that `IsAffine (pullback (terminal.from X) (terminal.from Y))` for affine `X` and `Y` is
already an instance in Mathlib, since `⊤_ Scheme` is affine.

## Implementation notes

The `ULift ℤ`-algebra structure on a commutative ring `A : Type u` is `ULift.algebra'`, which is a
def rather than an instance; it is enabled as a local instance in this file.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct CommRingCat

namespace AlgebraicGeometry

attribute [local instance] ULift.algebra'

variable (A B : Type u) [CommRing A] [CommRing B]

/-- `Spec (A ⊗[ULift ℤ] B)`, with the two maps induced by `a ↦ a ⊗ₜ 1` and `b ↦ 1 ⊗ₜ b`, is the
fibre product of `Spec A` and `Spec B` over the terminal scheme:

```
  Spec (A ⊗[ULift ℤ] B) --b ↦ 1 ⊗ₜ b--> Spec B
            |                              |
      a ↦ a ⊗ₜ 1                           |
            ↓                              ↓
         Spec A --------------------> ⊤_ Scheme
```
-/
theorem isPullback_terminalFrom_spec :
    IsPullback (Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ULift.{u} ℤ) (A := A) (B := B))))
      (Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom))
      (terminal.from (Spec (.of A))) (terminal.from (Spec (.of B))) := by
  have h : IsPullback (Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ULift.{u} ℤ) (A := A) (B := B))))
      (Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom))
      (Spec.map (ofHom (algebraMap (ULift.{u} ℤ) A)))
      (Spec.map (ofHom (algebraMap (ULift.{u} ℤ) B))) := ?_
  · exact h.of_isTerminal specULiftZIsTerminal terminalIsTerminal
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso (ULift.{u} ℤ) A B).symm
    (pullbackSpecIso_inv_fst ..) (pullbackSpecIso_inv_snd ..)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp [Algebra.TensorProduct.algebraMap_def]

/-- The fibre product of `Spec A` and `Spec B` over the terminal scheme is
`Spec (A ⊗[ULift ℤ] B)`. -/
noncomputable def pullbackTerminalSpecIso :
    pullback (terminal.from (Spec (.of A))) (terminal.from (Spec (.of B))) ≅
      Spec (.of (A ⊗[ULift.{u} ℤ] B)) :=
  (isPullback_terminalFrom_spec A B).isoPullback.symm

/-- The composition of the inverse of `pullbackTerminalSpecIso A B` with the first projection is
`Spec.map` of the ring morphism `a ↦ a ⊗ₜ 1`. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_inv_fst :
    (pullbackTerminalSpecIso A B).inv ≫ pullback.fst _ _ =
      Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ULift.{u} ℤ))) :=
  (isPullback_terminalFrom_spec A B).isoPullback_hom_fst

/-- The composition of the inverse of `pullbackTerminalSpecIso A B` with the second projection is
`Spec.map` of the ring morphism `b ↦ 1 ⊗ₜ b`. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_inv_snd :
    (pullbackTerminalSpecIso A B).inv ≫ pullback.snd _ _ =
      Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom) :=
  (isPullback_terminalFrom_spec A B).isoPullback_hom_snd

/-- The composition of `pullbackTerminalSpecIso A B` with `Spec.map` of the ring morphism
`a ↦ a ⊗ₜ 1` is the first projection. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_hom_fst :
    (pullbackTerminalSpecIso A B).hom ≫
        Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ULift.{u} ℤ))) =
      pullback.fst _ _ := by
  rw [← pullbackTerminalSpecIso_inv_fst, Iso.hom_inv_id_assoc]

/-- The composition of `pullbackTerminalSpecIso A B` with `Spec.map` of the ring morphism
`b ↦ 1 ⊗ₜ b` is the second projection. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_hom_snd :
    (pullbackTerminalSpecIso A B).hom ≫
        Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
          (A := A) (B := B)).toRingHom) = pullback.snd _ _ := by
  rw [← pullbackTerminalSpecIso_inv_snd, Iso.hom_inv_id_assoc]

/-- **Global sections of a product of two affine schemes are generated by the products of the
pullbacks of generators of the two factors.** -/
theorem closure_range_mul_appTop_eq_top {A B : Type u} [CommRing A] [CommRing B]
    {W : Scheme.{u}} {pa : W ⟶ Spec (.of A)} {pb : W ⟶ Spec (.of B)}
    (hP : IsPullback pa pb (terminal.from _) (terminal.from _))
    {ιA ιB : Type*} {a : ιA → A} {b : ιB → B}
    (ha : Subring.closure (Set.range a) = ⊤) (hb : Subring.closure (Set.range b) = ⊤)
    {ra : ιA} (hra : a ra = 1) {rb : ιB} (hrb : b rb = 1) :
    Subring.closure (Set.range fun p : ιA × ιB ↦
        ((Scheme.ΓSpecIso _).inv ≫ pa.appTop).hom (a p.1) *
          ((Scheme.ΓSpecIso _).inv ≫ pb.appTop).hom (b p.2)) = ⊤ := by
  -- identify `W` with `Spec (A ⊗ B)` and read the two pullbacks of sections off the two
  -- inclusions of the tensor factors
  let e : W ≅ Spec (.of (A ⊗[ULift.{u} ℤ] B)) := hP.isoPullback ≪≫ pullbackTerminalSpecIso A B
  let φ : CommRingCat.of (A ⊗[ULift.{u} ℤ] B) ⟶ Γ(W, ⊤) :=
    (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop
  have hfst : e.hom ≫ Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ULift.{u} ℤ) (A := A) (B := B))) = pa := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackTerminalSpecIso_hom_fst,
      IsPullback.isoPullback_hom_fst]
  have hsnd : e.hom ≫ Spec.map (ofHom (Algebra.TensorProduct.includeRight
      (R := ULift.{u} ℤ) (A := A) (B := B)).toRingHom) = pb := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackTerminalSpecIso_hom_snd,
      IsPullback.isoPullback_hom_snd]
  have hA (x : A) : ((Scheme.ΓSpecIso _).inv ≫ pa.appTop).hom x =
      φ.hom (x ⊗ₜ[ULift.{u} ℤ] 1) := by
    rw [← hfst, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have hB (y : B) : ((Scheme.ΓSpecIso _).inv ≫ pb.appTop).hom y =
      φ.hom (1 ⊗ₜ[ULift.{u} ℤ] y) := by
    rw [← hsnd, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have hiso : IsIso φ := inferInstanceAs (IsIso ((Scheme.ΓSpecIso _).inv ≫ e.hom.appTop))
  have hsurj : Function.Surjective φ.hom :=
    ((ConcreteCategory.isIso_iff_bijective φ).mp hiso).2
  have hrange (p : ιA × ιB) :
      ((Scheme.ΓSpecIso _).inv ≫ pa.appTop).hom (a p.1) *
        ((Scheme.ΓSpecIso _).inv ≫ pb.appTop).hom (b p.2) =
      φ.hom (a p.1 ⊗ₜ[ULift.{u} ℤ] b p.2) := by
    rw [hA, hB, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have himage : (Set.range fun p : ιA × ιB ↦ φ.hom (a p.1 ⊗ₜ[ULift.{u} ℤ] b p.2)) =
      φ.hom '' (Set.range fun p : ιA × ιB ↦ a p.1 ⊗ₜ[ULift.{u} ℤ] b p.2) := by
    rw [← Set.range_comp]
    rfl
  simp only [hrange]
  rw [himage, ← RingHom.map_closure,
    Algebra.TensorProduct.closure_range_tmul_eq_top ha hb hra hrb]
  ext z
  simp only [Subring.mem_map, Subring.mem_top, iff_true, true_and]
  exact hsurj z

/-- The range of the morphism of fibre products induced by two open immersions `u` and `v` is
the intersection of the preimages of the ranges of `u` and `v`:

```
  X' <---fst--- X' ×[Z] Y' ---snd---> Y'
   |                 |                 |
   u           pullback.map            v
   ↓                 ↓                 ↓
   X  <---fst--- X ×[Z] Y ----snd----> Y
```
-/
lemma Scheme.Pullback.opensRange_map {X Y Z X' Y' : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (u : X' ⟶ X) (v : Y' ⟶ Y) [IsOpenImmersion u] [IsOpenImmersion v]
    (w₁ : (u ≫ f) ≫ 𝟙 Z = u ≫ f := Category.comp_id _)
    (w₂ : (v ≫ g) ≫ 𝟙 Z = v ≫ g := Category.comp_id _) :
    (pullback.map (u ≫ f) (v ≫ g) f g u v (𝟙 Z) w₁ w₂).opensRange =
      pullback.fst f g ⁻¹ᵁ u.opensRange ⊓ pullback.snd f g ⁻¹ᵁ v.opensRange := by
  let M := pullback.map (u ≫ f) (v ≫ g) f g u v (𝟙 Z) w₁ w₂
  have hMfst : M ≫ pullback.fst f g = pullback.fst (u ≫ f) (v ≫ g) ≫ u := by simp [M]
  have hMsnd : M ≫ pullback.snd f g = pullback.snd (u ≫ f) (v ≫ g) ≫ v := by simp [M]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.coe_preimage, Set.mem_preimage, ← Scheme.Hom.comp_apply, hMfst]
      exact ⟨_, rfl⟩
    · rw [Scheme.Hom.coe_preimage, Set.mem_preimage, ← Scheme.Hom.comp_apply, hMsnd]
      exact ⟨_, rfl⟩
  · let W : (pullback f g).Opens :=
      pullback.fst f g ⁻¹ᵁ u.opensRange ⊓ pullback.snd f g ⁻¹ᵁ v.opensRange
    have h1 : Set.range (W.ι ≫ pullback.fst f g).base ⊆ Set.range u.base := by
      rintro _ ⟨y, rfl⟩
      exact y.2.1
    have h2 : Set.range (W.ι ≫ pullback.snd f g).base ⊆ Set.range v.base := by
      rintro _ ⟨y, rfl⟩
      exact y.2.2
    have hab : IsOpenImmersion.lift u _ h1 ≫ (u ≫ f) =
        IsOpenImmersion.lift v _ h2 ≫ (v ≫ g) := by
      rw [← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, pullback.condition]
    have hc : pullback.lift _ _ hab ≫ M = W.ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, hMfst, ← Category.assoc, pullback.lift_fst,
          IsOpenImmersion.lift_fac]
      · rw [Category.assoc, hMsnd, ← Category.assoc, pullback.lift_snd,
          IsOpenImmersion.lift_fac]
    rintro y hy
    refine ⟨(pullback.lift _ _ hab).base ⟨y, hy⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hc]
    rfl

/-- The range of the `(i, j)`-th chart of the product cover of a fibre product is the
intersection of the preimages of the `i`-th and `j`-th chart of the two covers. -/
lemma Scheme.Pullback.opensRange_openCoverOfLeftRight_f {X Y Z : Scheme.{u}}
    (𝒰X : X.OpenCover) (𝒰Y : Y.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z) (ij : 𝒰X.I₀ × 𝒰Y.I₀) :
    ((Scheme.Pullback.openCoverOfLeftRight 𝒰X 𝒰Y f g).f ij).opensRange =
      pullback.fst f g ⁻¹ᵁ (𝒰X.f ij.1).opensRange ⊓
        pullback.snd f g ⁻¹ᵁ (𝒰Y.f ij.2).opensRange := by
  rw [← Scheme.Pullback.opensRange_map (f := f) (g := g) (𝒰X.f ij.1) (𝒰Y.f ij.2)]
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange,
    Scheme.Pullback.openCoverOfLeftRight_f]
  rfl

end AlgebraicGeometry
