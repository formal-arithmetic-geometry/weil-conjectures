/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Endomorphism
public import Submission.WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Composition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The relative Frobenius

Let `f : X ⟶ Y` be a morphism and `Φ_X`, `Φ_Y` endomorphisms of `X`, `Y` with
`Φ_X ≫ f = f ≫ Φ_Y`. Put `X' = Y ×_{Φ_Y, Y, f} X`, with projections `f' : X' ⟶ Y` and
`p : X' ⟶ X`. The *relative Frobenius* is `r = (f, Φ_X) : X ⟶ X'`; it satisfies `r ≫ p = Φ_X`
and `r ≫ f' = f`.

For a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite field `k₀ = 𝔽_q` with base change `f`,
and `Φ` the base changes of the `q`-power Frobenii, the `m`-th iterates `Φ^m` commute with `f`
and the relative Frobenius `r_m = (f, Φ_X ^ m)` is the base change of the relative
`q ^ m`-power Frobenius `F_{X₀/Y₀} = (f₀, F_{X₀} ^ m) : X₀ ⟶ Y₀ ×_{F_{Y₀} ^ m, Y₀, f₀} X₀`.

## Main definitions

- `AlgebraicGeometry.relativeFrobenius`: the relative Frobenius `r = (f, Φ_X)`.

## Main statements

- `AlgebraicGeometry.isPullback_relativeFrobenius`: the relative Frobenius commutes with base
  change.
- `AlgebraicGeometry.isPullback_relativeFrobenius_of_isFrobenius`: the relative Frobenius
  `r_m` of a base change of a morphism over a finite field is the base change of the relative
  `q ^ m`-power Frobenius.
- `AlgebraicGeometry.relativeFrobenius_specMap`: the affine formula `r' ⊗ s ↦ g r' * φ s`.
- `AlgebraicGeometry.isFinite_relativeFrobenius`,
  `AlgebraicGeometry.isUniversalHomeomorphism_relativeFrobenius`: the relative Frobenius of
  finite universal homeomorphisms is a finite universal homeomorphism.
- `AlgebraicGeometry.isFinite_and_isUniversalHomeomorphism_relativeFrobenius`: the same for the
  base changes of the Frobenii of schemes locally of finite type over a finite field.
- Instances in `Over S`: finiteness properties of `Y ×_{Φ_Y, Y, f} X` and of the relative
  Frobenius.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

section General

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- The *relative Frobenius* `r = (f, Φ_X) : X ⟶ X'` of a morphism `f : X ⟶ Y` compatible with
endomorphisms `Φ_X`, `Φ_Y` (`Φ_X ≫ f = f ≫ Φ_Y`), where `X' = Y ×_{Φ_Y, Y, f} X`:

```
     X' ──f'──→ Y           r ≫ p = Φ_X
     │          │           r ≫ f' = f
    p│          │Φ_Y
     ↓          ↓
     X ───f───→ Y
```

Here `X'` is `CategoryTheory.Limits.pullback Φ_Y f`, with `f' = pullback.fst` and
`p = pullback.snd` (blueprint: `sk-d-relative-frob`, `d-relative-frob`). -/
noncomputable def relativeFrobenius (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [HasPullback ΦY f] : X ⟶ pullback ΦY f :=
  pullback.lift f ΦX h.symm

/-- The identity `f' ∘ r = f` (blueprint: `sk-d-relative-frob`, `d-relative-frob`). -/
@[reassoc (attr := simp)]
lemma relativeFrobenius_fst (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (h : ΦX ≫ f = f ≫ ΦY)
    [HasPullback ΦY f] : relativeFrobenius f ΦX ΦY h ≫ pullback.fst ΦY f = f :=
  pullback.lift_fst _ _ _

/-- The identity `p ∘ r = Φ_X` (blueprint: `sk-d-relative-frob`, `d-relative-frob`). -/
@[reassoc (attr := simp)]
lemma relativeFrobenius_snd (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (h : ΦX ≫ f = f ≫ ΦY)
    [HasPullback ΦY f] : relativeFrobenius f ΦX ΦY h ≫ pullback.snd ΦY f = ΦX :=
  pullback.lift_snd _ _ _

end General

section BaseChange

variable {S s₀ X₀ Y₀ X Y : Scheme.{u}} {gX : X₀ ⟶ S} {gY : Y₀ ⟶ S} {σ : s₀ ⟶ S}
  {pX : X ⟶ X₀} {aX : X ⟶ s₀} {pY : Y ⟶ Y₀} {aY : Y ⟶ s₀} {f₀ : X₀ ⟶ Y₀} {f : X ⟶ Y}


/-- The fibre product `X' = Y ×_{Φ_Y, Y, f} X` commutes with base change: if `f`, `Φ_Y` are
the base changes of `f₀ : X₀ ⟶ Y₀` and of `F_Y : Y₀ ⟶ Y₀` along `σ : s₀ ⟶ S`, then
`X' = X₀' ×_S s₀` for `X₀' = Y₀ ×_{F_Y, Y₀, f₀} X₀` (blueprint: `d-relative-frob`). -/
lemma isPullback_pullbackMap (hX : IsPullback pX aX gX σ) (hfp : f ≫ pY = pX ≫ f₀)
    {ΦY : Y ⟶ Y} {FY : Y₀ ⟶ Y₀} (hΦY : IsPullback ΦY pY pY FY) :
    IsPullback (pullback.map ΦY f FY f₀ pY pX pY hΦY.w hfp) (pullback.snd ΦY f ≫ aX)
      (pullback.snd FY f₀ ≫ gX) σ := by
  refine IsPullback.paste_vert ?_ hX
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback FY f₀)
  rw [pullback.lift_fst, ← hfp]
  exact (IsPullback.of_hasPullback ΦY f).paste_horiz hΦY.flip

/-- The relative Frobenius commutes with base change: in the situation of
`AlgebraicGeometry.isPullback_pullbackMap`, if moreover `Φ_X = F_X ×_S 𝟙_{s₀}` with `F_X` an
`S`-morphism, then `r = (f, Φ_X)` is the base change `(f₀, F_X) ×_S 𝟙_{s₀}` of the relative
Frobenius of `X₀` over `Y₀` (blueprint: `d-relative-frob`). -/
lemma isPullback_relativeFrobenius (hX : IsPullback pX aX gX σ) (hfp : f ≫ pY = pX ≫ f₀)
    {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀} (h₀ : FX ≫ f₀ = f₀ ≫ FY) (hFX : FX ≫ gX = gX)
    {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} (h : ΦX ≫ f = f ≫ ΦY) (hΦXa : ΦX ≫ aX = aX)
    (hΦX : ΦX ≫ pX = pX ≫ FX) (hΦY : IsPullback ΦY pY pY FY) :
    IsPullback (relativeFrobenius f ΦX ΦY h) pX (pullback.map ΦY f FY f₀ pY pX pY hΦY.w hfp)
      (relativeFrobenius f₀ FX FY h₀) := by
  refine (IsPullback.of_bot ?_ ?_ (isPullback_pullbackMap hX hfp hΦY)).flip
  · simpa [hΦXa, hFX] using hX
  · apply pullback.hom_ext <;> simp [relativeFrobenius, hfp, hΦX]

end BaseChange

section Model

variable {k : Type u} [Field k] [Finite k] {s₀ X₀ Y₀ X Y : Scheme.{u}}
  {gX : X₀ ⟶ Spec (.of k)} {gY : Y₀ ⟶ Spec (.of k)} {σ : s₀ ⟶ Spec (.of k)} {pX : X ⟶ X₀}
  {aX : X ⟶ s₀} {pY : Y ⟶ Y₀} {aY : Y ⟶ s₀} {FX : X₀ ⟶ X₀} {FY : Y₀ ⟶ Y₀} {ΦX : X ⟶ X}
  {ΦY : Y ⟶ Y} {f₀ : X₀ ⟶ Y₀} {f : X ⟶ Y}



end Model


section Finite

variable {X Y : Scheme.{u}}

/-- The relative Frobenius of a morphism between schemes with finite endomorphisms is finite:
it is a section of the projection `p`, a base change of `Φ_Y`, and its composite with that
projection is the finite morphism `Φ_X` (blueprint: `sk-i-relative-frob`,
`i-relative-frob`). -/
instance isFinite_relativeFrobenius (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsFinite ΦX] [IsFinite ΦY] :
    IsFinite (relativeFrobenius f ΦX ΦY h) := by
  have : IsFinite (relativeFrobenius f ΦX ΦY h ≫ pullback.snd ΦY f) := by
    rw [relativeFrobenius_snd]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f)

/-- The relative Frobenius of a morphism between schemes whose endomorphisms are finite
universal homeomorphisms is a universal homeomorphism: its composite with the projection `p`, a
base change of `Φ_Y`, is `Φ_X` (blueprint: `sk-i-relative-frob`, `i-relative-frob`). -/
instance isUniversalHomeomorphism_relativeFrobenius (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsUniversalHomeomorphism ΦX] [IsUniversalHomeomorphism ΦY] :
    IsUniversalHomeomorphism (relativeFrobenius f ΦX ΦY h) := by
  have : IsUniversalHomeomorphism (relativeFrobenius f ΦX ΦY h ≫ pullback.snd ΦY f) := by
    rw [relativeFrobenius_snd]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f)


end Finite

/-! ### The relative Frobenius in `Over S` -/

section Over

variable {S : Scheme.{u}} {X Y : Over S}

/-- The cartesian square `X' = Y ×_{Φ_Y, Y, f} X` of `Over S` gives a cartesian square of
underlying schemes (blueprint: `sk-d-relative-frob`). -/
theorem isPullback_left_pullback (f : X ⟶ Y) (ΦY : Y ⟶ Y) :
    IsPullback (pullback.fst ΦY f).left (pullback.snd ΦY f).left ΦY.left f.left :=
  (IsPullback.of_hasPullback ΦY f).map (Over.forget S)

/-- The projection `p : X' ⟶ X` is finite if `Φ_Y` is, being a base change of it
(blueprint: `sk-i-relative-frob`). -/
instance isFinite_pullback_snd_left (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left] :
    IsFinite (pullback.snd ΦY f).left :=
  MorphismProperty.of_isPullback (isPullback_left_pullback f ΦY) inferInstance

/-- The structure morphism of `X' = Y ×_{Φ_Y, Y, f} X` is `p ≫ (X ↘ S)`. -/
lemma pullback_hom_eq (f : X ⟶ Y) (ΦY : Y ⟶ Y) :
    (pullback ΦY f).hom = (pullback.snd ΦY f).left ≫ X.hom :=
  (Over.w (pullback.snd ΦY f)).symm

/-- `X' = Y ×_{Φ_Y, Y, f} X` is locally of finite type over `S` if `X` is and `Φ_Y` is finite
(blueprint: `sk-i-relative-frob`). -/
instance locallyOfFiniteType_pullback_hom (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left]
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (pullback ΦY f).hom := by
  rw [pullback_hom_eq]
  infer_instance

/-- `X' = Y ×_{Φ_Y, Y, f} X` is quasi-compact over `S` if `X` is and `Φ_Y` is finite
(blueprint: `sk-i-relative-frob`). -/
instance quasiCompact_pullback_hom (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left]
    [QuasiCompact X.hom] : QuasiCompact (pullback ΦY f).hom := by
  rw [pullback_hom_eq]
  infer_instance

/-- `X' = Y ×_{Φ_Y, Y, f} X` is separated over `S` if `X` is and `Φ_Y` is finite
(blueprint: `sk-i-relative-frob`). -/
instance isSeparated_pullback_hom (f : X ⟶ Y) (ΦY : Y ⟶ Y) [IsFinite ΦY.left]
    [IsSeparated X.hom] : IsSeparated (pullback ΦY f).hom := by
  rw [pullback_hom_eq]
  infer_instance

/-- `r ∘ p = Φ_X` on underlying schemes (blueprint: `sk-d-relative-frob`). -/
@[reassoc (attr := simp)]
lemma relativeFrobenius_left_snd_left (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) :
    (relativeFrobenius f ΦX ΦY h).left ≫ (pullback.snd ΦY f).left = ΦX.left := by
  rw [← Over.comp_left, relativeFrobenius_snd]

/-- The relative Frobenius of finite endomorphisms is finite on underlying schemes
(blueprint: `sk-i-relative-frob`, `i-relative-frob`). -/
instance isFinite_relativeFrobenius_left (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsFinite ΦX.left] [IsFinite ΦY.left] :
    IsFinite (relativeFrobenius f ΦX ΦY h).left := by
  have : IsFinite ((relativeFrobenius f ΦX ΦY h).left ≫ (pullback.snd ΦY f).left) := by
    rw [relativeFrobenius_left_snd_left]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f).left

/-- The relative Frobenius of finite universal homeomorphisms is a universal homeomorphism on
underlying schemes (blueprint: `sk-i-relative-frob`, `i-relative-frob`). -/
instance isUniversalHomeomorphism_relativeFrobenius_left (f : X ⟶ Y) (ΦX : X ⟶ X)
    (ΦY : Y ⟶ Y) (h : ΦX ≫ f = f ≫ ΦY) [IsUniversalHomeomorphism ΦX.left]
    [IsUniversalHomeomorphism ΦY.left] :
    IsUniversalHomeomorphism (relativeFrobenius f ΦX ΦY h).left := by
  have : IsUniversalHomeomorphism (pullback.snd ΦY f).left :=
    MorphismProperty.of_isPullback (isPullback_left_pullback f ΦY) inferInstance
  have : IsUniversalHomeomorphism
      ((relativeFrobenius f ΦX ΦY h).left ≫ (pullback.snd ΦY f).left) := by
    rw [relativeFrobenius_left_snd_left]
    infer_instance
  exact .of_comp _ (pullback.snd ΦY f).left

/-- The relative Frobenius of finite endomorphisms is proper on underlying schemes
(blueprint: `sk-i-relative-frob`). -/
instance isProper_relativeFrobenius_left (f : X ⟶ Y) (ΦX : X ⟶ X) (ΦY : Y ⟶ Y)
    (h : ΦX ≫ f = f ≫ ΦY) [IsFinite ΦX.left] [IsFinite ΦY.left] :
    IsProper (relativeFrobenius f ΦX ΦY h).left :=
  inferInstance

end Over

end AlgebraicGeometry
