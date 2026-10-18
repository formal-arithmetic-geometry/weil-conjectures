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

/-! ### Summing over the fibres -/

section Sum

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y) {Φ : X ⟶ X}
  {ΦY : Y ⟶ Y} (hf : Φ ≫ f = f ≫ ΦY)

/-- A sum over the points of `X` fixed by `Φ` is the sum over the points `y` of `Y` fixed by
`Φ_Y` of the sums over the points of the fibres `X_y` fixed by `Φ_y`. -/
lemma sum_fixedPoint_eq_sum_sum_fibre {M : Type*} [AddCommMonoid M]
    (F : {x : RationalPoint X // x ≫ Φ = x} → M)
    [Fintype {x : RationalPoint X // x ≫ Φ = x}] [Fintype {y : RationalPoint Y // y ≫ ΦY = y}]
    [∀ y : {y : RationalPoint Y // y ≫ ΦY = y},
      Fintype {z : RationalPoint (fibre f y.1) // z ≫ fibreFrobenius f hf y.1 y.2 = z}] :
    ∑ x : {x : RationalPoint X // x ≫ Φ = x}, F x =
      ∑ y : {y : RationalPoint Y // y ≫ ΦY = y},
        ∑ z : {z : RationalPoint (fibre f y.1) // z ≫ fibreFrobenius f hf y.1 y.2 = z},
          F ⟨z.1 ≫ fibreι f y.1, by
            rw [Category.assoc, ← fibreFrobenius_ι f hf y.1 y.2, ← Category.assoc, z.2]⟩ := by
  classical
  let g : {x : RationalPoint X // x ≫ Φ = x} → {y : RationalPoint Y // y ≫ ΦY = y} :=
    fun x ↦ ⟨x.1 ≫ f, by rw [Category.assoc, ← hf, ← Category.assoc, x.2]⟩
  rw [← Finset.sum_fiberwise Finset.univ g]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_subtype (Finset.univ.filter fun x ↦ g x = y) (p := fun x ↦ g x = y)
    (F := Subtype.fintype _) (fun x ↦ by simp)]
  let e : {x : {x : RationalPoint X // x ≫ Φ = x} // g x = y} ≃
      {x : {x : RationalPoint X // x ≫ Φ = x} // x.1 ≫ f = y.1} :=
    Equiv.subtypeEquivRight fun x ↦ Subtype.ext_iff
  refine Fintype.sum_equiv (e.trans (fibreFixedPointEquiv f hf y.1 y.2)) _ _ fun x ↦ ?_
  simp [e, fibreFixedPointEquiv]

end Sum

/-! ### The model of a fibre -/

section FibreModel

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Algebra k₀ k] {X₀ Y₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} (π₀ : X₀ ⟶ Y₀) {g₀ : Y₀ ⟶ Spec (.of k₀)}
  (hπ : π₀ ≫ g₀ = f₀)

/-- The base change `f : X ⟶ Y₀ ×_{k₀} k` of `π₀ : X₀ ⟶ Y₀`. -/
noncomputable def stdModelMap
    (w : p ≫ f₀ = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :
    X ⟶ stdModel k g₀ :=
  Over.homMk (pullback.lift (p ≫ π₀) X.hom (by rw [Category.assoc, hπ, w])) (by simp)

@[reassoc (attr := simp)]
lemma stdModelMap_left_fst (w : p ≫ f₀ = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :
    (stdModelMap π₀ hπ w).left ≫ pullback.fst _ _ = p ≫ π₀ :=
  pullback.lift_fst _ _ _

/-- The base change of `π₀` is compatible with the model Frobenii. -/
lemma stdModelMap_comp [Finite k₀] {F₀ : X₀ ⟶ X₀} (hF₀ : F₀.IsFrobenius (Nat.card k₀))
    (hp : Φ.left ≫ p = p ≫ F₀) {FY : Y₀ ⟶ Y₀} (hFY : FY.IsFrobenius (Nat.card k₀))
    (w : p ≫ f₀ = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :
    Φ ≫ stdModelMap π₀ hπ w = stdModelMap π₀ hπ w ≫ stdModelFrobenius g₀ (hFY.comp_eq g₀) := by
  have hc : π₀ ≫ FY = F₀ ≫ π₀ := hF₀.comp_eq_comp f₀ hFY π₀
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simp [stdModelMap, stdModelFrobenius, reassoc_of% hp, hc]
  · simp [stdModelMap, stdModelFrobenius]

variable [Finite k₀] (hΦ : IsModelFrobenius Φ f₀ p)

omit [Finite k₀] in
/-- The square `X ⟶ X₀`, `X ⟶ Y₀ ×_{k₀} k` over `π₀` is cartesian. -/
lemma isPullback_stdModelMap :
    IsPullback p (stdModelMap π₀ hπ hΦ.isPullback.w).left π₀
      (pullback.fst g₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))) := by
  refine IsPullback.of_bot ?_ (stdModelMap_left_fst π₀ hπ _).symm (IsPullback.of_hasPullback _ _)
  have h := hΦ.isPullback
  rwa [← hπ, ← Over.w (stdModelMap π₀ hπ hΦ.isPullback.w)] at h

variable (y : RationalPoint (stdModel k g₀)) (y₀ : Spec (.of k₀) ⟶ Y₀)
  (hy₀ : Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ≫ y₀ =
    y.left ≫ pullback.fst g₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))))

/-- The map from the fibre `X_y` to the fibre `X₀ ×_{Y₀} y₀` of `π₀`. -/
noncomputable def fibreModelMap :
    (fibre (stdModelMap π₀ hπ hΦ.isPullback.w) y).left ⟶ pullback π₀ y₀ :=
  pullback.lift ((fibreι (stdModelMap π₀ hπ hΦ.isPullback.w) y).left ≫ p)
    ((fibre (stdModelMap π₀ hπ hΦ.isPullback.w) y).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) (by
    have h := congrArg CommaMorphism.left
      (isPullback_fibre (stdModelMap π₀ hπ hΦ.isPullback.w) y).w
    simp only [Over.comp_left, toPoint_left] at h
    rw [Category.assoc, Category.assoc, hy₀, ← stdModelMap_left_fst π₀ hπ hΦ.isPullback.w,
      ← Category.assoc, h, Category.assoc])

variable {F₀ : X₀ ⟶ X₀} (hF₀ : F₀.IsFrobenius (Nat.card k₀)) (hp : Φ.left ≫ p = p ≫ F₀)
  {FY : Y₀ ⟶ Y₀} (hFY : FY.IsFrobenius (Nat.card k₀))
  (hy : y ≫ stdModelFrobenius g₀ (hFY.comp_eq g₀) = y)

/-- **The fibres are models** (blueprint `sk-thm-trace-formula`): the fibre `X_y` of the base
change of `π₀` over a point `y` fixed by `Φ_Y`, with its Frobenius `Φ_y`, is the base change of
the fibre `X₀ ×_{Y₀} y₀` of `π₀` over the `k₀`-point `y₀` underlying `y`. -/
theorem isModelFrobenius_fibre :
    IsModelFrobenius (fibreFrobenius (stdModelMap π₀ hπ hΦ.isPullback.w)
        (stdModelMap_comp π₀ hπ hF₀ hp hFY hΦ.isPullback.w) y hy)
      (pullback.snd π₀ y₀) (fibreModelMap π₀ hπ hΦ y y₀ hy₀) where
  isPullback := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π₀ y₀)
    have h₁ := (isPullback_fibre (stdModelMap π₀ hπ hΦ.isPullback.w) y).map (Over.forget _)
    simp only [Over.forget_map, toPoint_left] at h₁
    have h := h₁.paste_horiz (isPullback_stdModelMap π₀ hπ hΦ)
    rw [← hy₀] at h
    have heq : fibreModelMap π₀ hπ hΦ y y₀ hy₀ ≫ pullback.fst π₀ y₀ =
        (fibreι (stdModelMap π₀ hπ hΦ.isPullback.w) y).left ≫ p :=
      pullback.lift_fst _ _ _
    rw [heq]
    exact h
  exists_isFrobenius := by
    obtain ⟨FZ, hFZ⟩ := Scheme.Hom.exists_isFrobenius (pullback.snd π₀ y₀)
    refine ⟨FZ, hFZ, pullback.hom_ext ?_ ?_⟩
    · have hc : pullback.fst π₀ y₀ ≫ F₀ = FZ ≫ pullback.fst π₀ y₀ :=
        hFZ.comp_eq_comp (pullback.snd π₀ y₀) hF₀ _
      have hι := congrArg CommaMorphism.left (fibreFrobenius_ι
        (stdModelMap π₀ hπ hΦ.isPullback.w) (stdModelMap_comp π₀ hπ hF₀ hp hFY
          hΦ.isPullback.w) y hy)
      simp only [Over.comp_left] at hι
      simp only [fibreModelMap, Category.assoc, pullback.lift_fst, ← hc,
        pullback.lift_fst_assoc]
      rw [← Category.assoc, hι, Category.assoc, hp]
    · simp only [fibreModelMap, Category.assoc, pullback.lift_snd, hFZ.comp_eq]
      rw [← Category.assoc, Over.w]

end FibreModel

/-! ### The Weil `!`-pushforward along the base change -/

section Pushforward

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- Isomorphic Weil objects for the identity of the base point have Frobenii of the same
trace. -/
lemma trace_frobenius_eq_of_iso {S T : WeilBoundedConstructible ℓ (𝟙 (point k))} (e : S ≅ T)
    [hS : HasRightDual S.carrier] [hT : HasRightDual T.carrier] :
    trace S.frobenius.hom = trace T.frobenius.hom :=
  trace_eq_of_iso (X := S.carrier) (X' := T.carrier) ((IsoAlgebra.forget _).mapIso e) _ _
    (WeilBoundedConstructible.frobenius_hom_naturality e.hom)

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) {Φ : X ⟶ X} {ΦY : Y ⟶ Y} (hf : Φ ≫ f = f ≫ ΦY)
  [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite ΦY.left]
  [IsUniversalHomeomorphism ΦY.left]

/-- The Weil `!`-pushforward `Rf_! K` along `f`, with the relative Frobenius
(blueprint `sk-d-weil-push`), has the compactly supported Frobenius of `K`, by the Leray
isomorphism. -/
lemma trace_compactFrobenius_weilPushforward (K : WeilBoundedConstructible ℓ Φ)
    [hL : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).obj
        ((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
          (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
          (relativeFrobenius_snd f hf)).obj K).carrier)]
    [hK : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)] :
    trace ((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
      (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
      (relativeFrobenius_snd f hf)).obj K).compactFrobenius = trace K.compactFrobenius := by
  obtain ⟨e⟩ := nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso ℓ
    (IsPullback.of_hasPullback f ΦY) (relativeFrobenius_fst f hf) (relativeFrobenius_snd f hf) K
  exact trace_frobenius_eq_of_iso e (hS := hL) (hT := hK)

variable (y : RationalPoint Y) (hy : y ≫ ΦY = y)
  [IsFinite (fibreFrobenius f hf y hy).left]
  [IsUniversalHomeomorphism (fibreFrobenius f hf y hy).left]

/-- The stalk Frobenius of the Weil `!`-pushforward at a point `y` fixed by `Φ_Y` is the
compactly supported Frobenius of the restriction of `K` to the fibre `X_y`, by proper base
change; by the degree one trace formula on the fibre, its trace is the sum of the traces of the
stalk Frobenii of `K` at the points of `X_y` fixed by `Φ_y`. -/
lemma trace_weilStalkFrobenius_weilPushforward [IsSepClosed k] (K : WeilBoundedConstructible ℓ Φ)
    [Fintype {z : RationalPoint (fibre f y) // z ≫ fibreFrobenius f hf y hy = z}]
    (h : ((weilUpperStar ℓ (fibreFrobenius f hf y hy) Φ (fibreι f y)
      (fibreFrobenius_ι f hf y hy)).obj K).TraceFormulaOne)
    [hL : HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
      ((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
        (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
        (relativeFrobenius_snd f hf)).obj K).carrier)]
    [∀ x : RationalPoint X, HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K.carrier)] :
    trace (((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
        (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
        (relativeFrobenius_snd f hf)).obj K).weilStalkFrobenius y hy) =
      ∑ z : {z : RationalPoint (fibre f y) // z ≫ fibreFrobenius f hf y hy = z},
        trace (K.weilStalkFrobenius (z.1 ≫ fibreι f y) (by
          rw [Category.assoc, ← fibreFrobenius_ι f hf y hy, ← Category.assoc, z.2])) := by
  obtain ⟨e⟩ := nonempty_weilStalk_weilLowerShriekOfFrobenius_iso ℓ
    (IsPullback.of_hasPullback f ΦY) (relativeFrobenius_fst f hf) (relativeFrobenius_snd f hf)
    (fibreFrobenius_ι f hf y hy) hy (isPullback_fibre f y) K
  let hKZ : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (toPoint (fibre f y))).obj ((weilUpperStar ℓ (fibreFrobenius f hf y hy) Φ (fibreι f y)
          (fibreFrobenius_ι f hf y hy)).obj K).carrier) :=
    (WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology _).some
  let _ : ∀ z : RationalPoint (fibre f y), HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ z).obj
        ((weilUpperStar ℓ (fibreFrobenius f hf y hy) Φ (fibreι f y)
          (fibreFrobenius_ι f hf y hy)).obj K).carrier) :=
    fun z ↦ (WeilBoundedConstructible.nonempty_hasRightDual_stalk _ z).some
  have hZ : trace ((weilUpperStar ℓ (fibreFrobenius f hf y hy) Φ (fibreι f y)
      (fibreFrobenius_ι f hf y hy)).obj K).compactFrobenius =
      ∑ z : {z : RationalPoint (fibre f y) // z ≫ fibreFrobenius f hf y hy = z},
        trace (((weilUpperStar ℓ (fibreFrobenius f hf y hy) Φ (fibreι f y)
          (fibreFrobenius_ι f hf y hy)).obj K).weilStalkFrobenius z.1 z.2) := h
  rw [WeilBoundedConstructible.weilStalkFrobenius,
    trace_frobenius_eq_of_iso e (hS := hL) (hT := hKZ)]
  refine hZ.trans (Finset.sum_congr rfl fun z _ ↦ ?_)
  have hz1 : z.1 ≫ frobeniusIterate (fibreFrobenius f hf y hy) 1 = z.1 := by
    rw [frobeniusIterate_one]
    exact z.2
  rw [← WeilBoundedConstructible.trace_stalkFrobenius_one _ z.1 hz1 z.2,
    WeilBoundedConstructible.trace_stalkFrobenius_weilUpperStar,
    WeilBoundedConstructible.trace_stalkFrobenius_one]

/-- The fibration step for Weil objects: if the degree one trace formula holds for the Weil
`!`-pushforward of `K` along `f` and for the restrictions of `K` to the fibres of `f` over the
points fixed by `Φ_Y`, it holds for `K`. -/
theorem traceFormulaOne_of_weilPushforward [IsSepClosed k] (K : WeilBoundedConstructible ℓ Φ)
    [Finite {y : RationalPoint Y // y ≫ ΦY = y}]
    (hY : ((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
      (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
      (relativeFrobenius_snd f hf)).obj K).TraceFormulaOne)
    (hfin : ∀ (y : RationalPoint Y) (hy : y ≫ ΦY = y),
      IsFinite (fibreFrobenius f hf y hy).left ∧
        IsUniversalHomeomorphism (fibreFrobenius f hf y hy).left)
    (hfib : ∀ (y : RationalPoint Y) (hy : y ≫ ΦY = y),
      haveI := (hfin y hy).1
      haveI := (hfin y hy).2
      ((weilUpperStar ℓ (fibreFrobenius f hf y hy) Φ (fibreι f y)
        (fibreFrobenius_ι f hf y hy)).obj K).TraceFormulaOne) :
    K.TraceFormulaOne := by
  classical
  intro _ iX _
  let _ := Fintype.ofFinite {y : RationalPoint Y // y ≫ ΦY = y}
  let _ (y : {y : RationalPoint Y // y ≫ ΦY = y}) :
      Fintype {z : RationalPoint (fibre f y.1) // z ≫ fibreFrobenius f hf y.1 y.2 = z} :=
    Fintype.ofEquiv _ (fibreFixedPointEquiv f hf y.1 y.2)
  let hLc : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint Y)).obj
        ((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
          (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
          (relativeFrobenius_snd f hf)).obj K).carrier) :=
    (WeilBoundedConstructible.nonempty_hasRightDual_compactCohomology _).some
  let hLs (y : RationalPoint Y) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).obj
        ((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
          (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
          (relativeFrobenius_snd f hf)).obj K).carrier) :=
    (WeilBoundedConstructible.nonempty_hasRightDual_stalk _ y).some
  have hYeq : trace ((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
      (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
      (relativeFrobenius_snd f hf)).obj K).compactFrobenius =
      ∑ y : {y : RationalPoint Y // y ≫ ΦY = y},
        trace (((weilLowerShriekOfFrobenius ℓ Φ ΦY f (IsPullback.of_hasPullback f ΦY)
          (relativeFrobenius f hf) (relativeFrobenius_fst f hf)
          (relativeFrobenius_snd f hf)).obj K).weilStalkFrobenius y.1 y.2) := hY
  rw [← trace_compactFrobenius_weilPushforward f hf K (hL := hLc) (hK := iX), hYeq,
    sum_fixedPoint_eq_sum_sum_fibre f hf (fun x ↦ trace (K.weilStalkFrobenius x.1 x.2))]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have := (hfin y.1 y.2).1
  have := (hfin y.1 y.2).2
  exact trace_weilStalkFrobenius_weilPushforward f hf y.1 y.2 K (hfib y.1 y.2) (hL := hLs y.1)

end Pushforward

/-! ### The fibration step over a model -/

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

/-- **The fibration step** (blueprint `sk-thm-trace-formula`): let `π₀ : X₀ ⟶ Spec A` be a
morphism to an affine `k₀`-scheme. If the degree one trace formula holds over `Spec A` and over
the fibres of `π₀` above all the `k₀`-points of `Spec A`, it holds over `X₀`. -/
theorem ModelTraceFormulaOne.of_fibration [IsAlgClosed k] {A : Type u} [CommRing A]
    [Algebra k₀ A] {X₀ : Scheme.{u}} (π₀ : X₀ ⟶ Spec (.of A)) {f₀ : X₀ ⟶ Spec (.of k₀)}
    (hπ : π₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = f₀) [LocallyOfFiniteType f₀]
    [LocallyOfFiniteType π₀]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))]
    (hY : ModelTraceFormulaOne ℓ (k := k) (Spec.map (CommRingCat.ofHom (algebraMap k₀ A))))
    (hfib : ∀ y₀ : Spec (.of k₀) ⟶ Spec (.of A),
      y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 _ →
        ModelTraceFormulaOne ℓ (k := k) (pullback.snd π₀ y₀)) :
    ModelTraceFormulaOne ℓ (k := k) f₀ := by
  intro X _ _ _ Φ p hΦ K
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  obtain ⟨FY, hFY⟩ := Scheme.Hom.exists_isFrobenius
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))
  have hΦY := isModelFrobenius_stdModel (k := k)
    (Spec.map (CommRingCat.ofHom (algebraMap k₀ A))) hFY
  have := hΦ.isFinite_self
  have := hΦ.isUniversalHomeomorphism_self
  have := hΦY.isFinite_self
  have := hΦY.isUniversalHomeomorphism_self
  have := hΦY.finite_fixedPoint (m := 1) one_ne_zero
  have : Finite {y : RationalPoint (stdModel k (Spec.map (CommRingCat.ofHom
      (algebraMap k₀ A)))) // y ≫ stdModelFrobenius _ (hFY.comp_eq _) = y} :=
    Finite.of_equiv (FixedPoint (stdModelFrobenius (k := k)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ A))) (hFY.comp_eq _)) 1)
      (Equiv.subtypeEquivRight fun y ↦ by rw [frobeniusIterate_one])
  have hdesc (y : RationalPoint (stdModel k (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))))
      (hy : y ≫ stdModelFrobenius _ (hFY.comp_eq _) = y) :
      ∃ y₀ : Spec (.of k₀) ⟶ Spec (.of A),
        Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ≫ y₀ = y.left ≫ pullback.fst _ _ ∧
          y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 _ := by
    have hfr := (hΦY.comp_frobeniusIterate_left_eq_iff 1 y.left).1 (by
      rw [frobeniusIterate_one, ← Over.comp_left, hy])
    rw [pow_one] at hfr
    exact exists_spec_point_of_frobenius_comp_eq _ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      erw [Over.w y]
      exact Category.id_comp _) hfr
  choose y₀ hy₀ hy₀' using hdesc
  intro _ _ _
  exact traceFormulaOne_of_weilPushforward (stdModelMap π₀ hπ hΦ.isPullback.w)
    (stdModelMap_comp π₀ hπ hF₀ hp hFY hΦ.isPullback.w) K
    (hY _ _ _ hΦY _)
    (fun y hy ↦ ⟨(isModelFrobenius_fibre π₀ hπ hΦ y (y₀ y hy) (hy₀ y hy) hF₀ hp hFY
      hy).isFinite_self, (isModelFrobenius_fibre π₀ hπ hΦ y (y₀ y hy) (hy₀ y hy) hF₀ hp hFY
      hy).isUniversalHomeomorphism_self⟩)
    (fun y hy ↦ hfib (y₀ y hy) (hy₀' y hy) _ _ _
      (isModelFrobenius_fibre π₀ hπ hΦ y (y₀ y hy) (hy₀ y hy) hF₀ hp hFY hy) _)

end Main

end AlgebraicGeometry.ProEtale.CondensedRing
