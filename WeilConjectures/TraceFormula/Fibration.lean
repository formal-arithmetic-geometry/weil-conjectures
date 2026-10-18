/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffinePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.TraceFormula.ModelDegreeOne

/-!

# The fibration step of the trace formula

Let `π₀ : X₀ ⟶ Y₀` be a morphism of `k₀`-schemes with `Y₀` affine. The degree one trace formula
over `Y₀` and over all the fibres of `π₀` above `k₀`-points gives the degree one trace formula over
`X₀` (`ProEtale.CondensedRing.ModelTraceFormulaOne.of_fibration`, blueprint
`sk-thm-trace-formula`, the induction on the number of variables, through `sk-d-weil-push`):

* the Weil `!`-pushforward `Rf_! K` along the base change `f : X ⟶ Y` of `π₀`, with the relative
  Frobenius `r : X ⟶ X ×_{Y, Φ_Y} Y`, a finite universal homeomorphism
  (`ProEtale.CondensedRing.relativeFrobenius`), has the compactly supported Frobenius of `K`
  (Leray isomorphism, `nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso`);
* by the degree one trace formula over `Y₀`, its trace is the sum over the points `y` fixed by
  `Φ_Y` of the traces of the stalk Frobenii of `Rf_! K`, which are the compactly supported
  Frobenii of the restrictions of `K` to the fibres `X_y` (proper base change,
  `nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`);
* the fibres `X_y` are base changes of the fibres of `π₀` above the `k₀`-points `y₀` of `Y₀`
  underlying `y` (`ProEtale.CondensedRing.IsModelFrobenius.fibre`), and the points of `X` fixed by
  `Φ` are the disjoint union of the points of the fibres fixed by their Frobenii
  (`ProEtale.CondensedRing.sum_fixedPoint_eq_sum_sum_fibre`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-! ### The standard model of a scheme over `k₀` -/

section StdModel

variable {k : Type u} [Field k] {k₀ : Type u} [Field k₀] [Algebra k₀ k] {Y₀ : Scheme.{u}}
  (g₀ : Y₀ ⟶ Spec (.of k₀))

variable (k) in
/-- The base change `Y₀ ×_{k₀} k` of a `k₀`-scheme, an object of `Over (Spec (.of k))`. -/
noncomputable abbrev stdModel : Over (Spec (.of k)) :=
  Over.mk (pullback.snd g₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))

instance [LocallyOfFiniteType g₀] : LocallyOfFiniteType (stdModel k g₀).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))

instance [QuasiCompact g₀] : QuasiCompact (stdModel k g₀).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))

instance [IsSeparated g₀] : IsSeparated (stdModel k g₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

/-- The endomorphism `F × 𝟙` of the base change `Y₀ ×_{k₀} k`, for a `k₀`-endomorphism `F` of
`Y₀`. -/
noncomputable def stdModelFrobenius {F : Y₀ ⟶ Y₀} (hF : F ≫ g₀ = g₀) :
    stdModel k g₀ ⟶ stdModel k g₀ :=
  Over.homMk (pullback.lift (pullback.fst _ _ ≫ F) (pullback.snd _ _)
    (by rw [Category.assoc, hF, pullback.condition])) (by simp)

/-- The base change of a `k₀`-scheme with the base change of its Frobenius is a model. -/
lemma isModelFrobenius_stdModel [Finite k₀] {F : Y₀ ⟶ Y₀} (hF : F.IsFrobenius (Nat.card k₀)) :
    IsModelFrobenius (stdModelFrobenius (k := k) g₀ (hF.comp_eq g₀)) g₀ (pullback.fst _ _) where
  isPullback := IsPullback.of_hasPullback _ _
  exists_isFrobenius := ⟨F, hF, pullback.lift_fst _ _ _⟩

end StdModel

/-! ### Fibres over rational points -/

section Fibre

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y) {Φ : X ⟶ X}
  {ΦY : Y ⟶ Y} (hf : Φ ≫ f = f ≫ ΦY) (y : RationalPoint Y) (hy : y ≫ ΦY = y)

/-- A rational point is a closed immersion. -/
lemma isClosedImmersion_rationalPoint (y : RationalPoint Y) : IsClosedImmersion y.left :=
  isClosedImmersion_of_comp_eq_id Y.hom y.left (Over.w y)

/-- The fibre `X_y = X ×_Y y` of `f : X ⟶ Y` over a rational point `y`. -/
noncomputable abbrev fibre : Over (Spec (.of k)) :=
  pullback f y

/-- The inclusion `X_y ⟶ X` of the fibre. -/
noncomputable abbrev fibreι : fibre f y ⟶ X :=
  pullback.fst f y

/-- The inclusion of the fibre is a closed immersion. -/
instance isClosedImmersion_fibreι : IsClosedImmersion (fibreι f y).left :=
  have := isClosedImmersion_rationalPoint y
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f y).map (Over.forget _)).flip
    (inferInstanceAs (IsClosedImmersion y.left))

lemma fibre_hom : (fibre f y).hom = (fibreι f y).left ≫ X.hom :=
  (Over.w (fibreι f y)).symm

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (fibre f y).hom := by
  rw [fibre_hom]
  infer_instance

instance [QuasiCompact X.hom] : QuasiCompact (fibre f y).hom := by
  rw [fibre_hom]
  infer_instance

instance [IsSeparated X.hom] : IsSeparated (fibre f y).hom := by
  rw [fibre_hom]
  infer_instance

/-- The fibre square `X_y ⟶ X`, `X_y ⟶ s` over `f` and `y` is cartesian. -/
lemma isPullback_fibre : IsPullback (fibreι f y) (toPoint (fibre f y)) f y := by
  have h := IsPullback.of_hasPullback f y
  rwa [toPoint_ext (pullback.snd f y) (toPoint _)] at h

/-- The Frobenius `Φ_y` of the fibre over a point `y` fixed by `Φ_Y`, the restriction of `Φ`. -/
noncomputable def fibreFrobenius : fibre f y ⟶ fibre f y :=
  pullback.lift (pullback.fst f y ≫ Φ) (pullback.snd f y)
    (by rw [Category.assoc, hf, pullback.condition_assoc, hy])

@[reassoc]
lemma fibreFrobenius_ι : fibreFrobenius f hf y hy ≫ fibreι f y = fibreι f y ≫ Φ :=
  pullback.lift_fst _ _ _

/-- The points of `X` fixed by `Φ` above `y` are the points of the fibre `X_y` fixed by
`Φ_y`. -/
noncomputable def fibreFixedPointEquiv :
    {x : {x : RationalPoint X // x ≫ Φ = x} // x.1 ≫ f = y} ≃
      {z : RationalPoint (fibre f y) // z ≫ fibreFrobenius f hf y hy = z} where
  toFun x := ⟨pullback.lift x.1.1 (𝟙 _) (by rw [x.2, Category.id_comp]), by
    apply pullback.hom_ext
    · rw [Category.assoc, fibreFrobenius_ι, pullback.lift_fst_assoc, pullback.lift_fst, x.1.2]
    · exact toPoint_ext _ _⟩
  invFun z := ⟨⟨z.1 ≫ fibreι f y, by
    rw [Category.assoc, ← fibreFrobenius_ι f hf y hy, ← Category.assoc, z.2]⟩, by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      toPoint_ext (z.1 ≫ pullback.snd f y) (𝟙 _), Category.id_comp]⟩
  left_inv x := Subtype.ext (Subtype.ext (pullback.lift_fst _ _ _))
  right_inv z := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) (toPoint_ext _ _))

end Fibre

/-! ### The relative Frobenius -/

section RelativeFrobenius

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y) {Φ : X ⟶ X}
  {ΦY : Y ⟶ Y} (hf : Φ ≫ f = f ≫ ΦY)

/-- The *relative Frobenius* `r = (Φ, f) : X ⟶ X ×_{Y, Φ_Y} Y` (blueprint `sk-d-relative-frob`). -/
noncomputable def relativeFrobenius : X ⟶ pullback f ΦY :=
  pullback.lift Φ f hf

@[reassoc (attr := simp)]
lemma relativeFrobenius_fst : relativeFrobenius f hf ≫ pullback.fst f ΦY = Φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeFrobenius_snd : relativeFrobenius f hf ≫ pullback.snd f ΦY = f :=
  pullback.lift_snd _ _ _

lemma pullback_frobenius_hom :
    (pullback f ΦY).hom = (pullback.fst f ΦY).left ≫ X.hom :=
  (Over.w (pullback.fst f ΦY)).symm

variable [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]

instance isFinite_pullback_fst_frobenius : IsFinite (pullback.fst f ΦY).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f ΦY).map (Over.forget _)).flip
    (inferInstanceAs (IsFinite ΦY.left))

instance isUniversalHomeomorphism_pullback_fst_frobenius :
    IsUniversalHomeomorphism (pullback.fst f ΦY).left :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f ΦY).map (Over.forget _)).flip
    (inferInstanceAs (IsUniversalHomeomorphism ΦY.left))

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (pullback f ΦY).hom := by
  rw [pullback_frobenius_hom]
  infer_instance

instance [QuasiCompact X.hom] : QuasiCompact (pullback f ΦY).hom := by
  rw [pullback_frobenius_hom]
  infer_instance

instance [IsSeparated X.hom] : IsSeparated (pullback f ΦY).hom := by
  rw [pullback_frobenius_hom]
  infer_instance

variable [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]

/-- The relative Frobenius is finite. -/
instance isFinite_relativeFrobenius : IsFinite (relativeFrobenius f hf).left := by
  have : IsFinite ((relativeFrobenius f hf).left ≫ (pullback.fst f ΦY).left) := by
    rw [← Over.comp_left, relativeFrobenius_fst]
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst f ΦY).left

/-- The relative Frobenius is a universal homeomorphism. -/
instance isUniversalHomeomorphism_relativeFrobenius :
    IsUniversalHomeomorphism (relativeFrobenius f hf).left := by
  have : IsUniversalHomeomorphism
      ((relativeFrobenius f hf).left ≫ (pullback.fst f ΦY).left) := by
    rw [← Over.comp_left, relativeFrobenius_fst]
    infer_instance
  exact IsUniversalHomeomorphism.of_comp _ (pullback.fst f ΦY).left

end RelativeFrobenius

end AlgebraicGeometry.ProEtale.CondensedRing
