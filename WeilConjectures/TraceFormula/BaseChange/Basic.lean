/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusExistence
public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite
public import WeilConjectures.TraceFormula.ModelExtension

/-!

# The base change from a finite field to its algebraic closure

Let `k = 𝔽_q` be a finite field with algebraic closure `k̄`, `s : Spec k̄ ⟶ Spec k` the geometric
point (`specAlgebraicClosure k`) and `X` a scheme over `Spec k`. This file sets up the geometry
of the base change `X̄ = X ×_k k̄`, an object of `Over (Spec k̄)`, which connects the Weil objects
of `WeilConjectures.TraceFormula.Statement`, living over `k` with an automorphism `e`, and the
model-Frobenius setting of the Lefschetz–Verdier formula, living over `k̄` with an endomorphism
`Φ` over `Spec k̄`.

* The `q`-power Frobenius `F_X : X ⟶ X` (`ProEtale.CondensedRing.overFrobenius`) is a morphism
  over `Spec k`, since `k = 𝔽_q`, and commutes with every morphism of schemes over `Spec k`.
* For an endomorphism `g` of `X` over `Spec k` and `N : ℕ`, the *model Frobenius*
  `Φ = (F_X^N ≫ g) ×_k k̄` of `X̄` (`ProEtale.CondensedRing.modelFrobenius N g`) is an
  endomorphism over `Spec k̄`. For `g = 𝟙` it is the base change of the `q^N`-power Frobenius,
  the model Frobenius of `IsModelFrobenius` for a model of `X̄` over `𝔽_{q^N}`
  (`ProEtale.CondensedRing.exists_isModelFrobenius_modelFrobenius_id`). For an automorphism `e`,
  `Φ = (F_X^{n+1} ≫ e^{n+1}) ×_k k̄` is the Frobenius `σ^{n+1}` twisted by `e^{n+1}`.
* A geometric point `x̄ : Spec k̄ ⟶ X` over `s` is the same as a `k̄`-rational point
  `x̄' = (x̄, 𝟙)` of `X̄` (`ProEtale.CondensedRing.geometricBaseChangePoint`), and
  `x̄ ≫ g = σ^{n+1} ≫ x̄` if and only if `x̄'` is fixed by `Φ = (F_X^{n+1} ≫ g) ×_k k̄`
  (`ProEtale.CondensedRing.geometricBaseChangePoint_comp_modelFrobenius_eq_iff`): the Galois
  Frobenius `σ` of `Spec k̄` is the inverse of the `q`-power Frobenius of `Spec k̄`, and
  `F_X ∘ x̄ = x̄ ∘ F_{k̄}`. In particular the points of degree `n + 1` for `e`
  (`ProEtale.CondensedRing.frobeniusFixedPoints e n`) are the rational points of `X̄` fixed by
  `Φ = (F_X^{n+1} ≫ e^{n+1}) ×_k k̄` (`ProEtale.CondensedRing.frobeniusFixedPointsEquiv`).

## Main definitions

- `ProEtale.CondensedRing.overFrobenius`: the `q`-power Frobenius of a scheme over `Spec k`.
- `ProEtale.CondensedRing.geometricBaseChange`: the base change functor
  `Over (Spec k) ⥤ Over (Spec k̄)`, with projection
  `ProEtale.CondensedRing.geometricBaseChangeProj : X̄ ⟶ X`.
- `ProEtale.CondensedRing.modelFrobenius`: the model Frobenius `(F_X^N ≫ g) ×_k k̄` of `X̄`.
- `ProEtale.CondensedRing.geometricBaseChangePoint`: the rational point of `X̄` attached to a
  geometric point of `X` over `s`.
- `ProEtale.CondensedRing.frobeniusFixedPointsEquiv`: the points of degree `n + 1` for `e` are
  the rational points of `X̄` fixed by the model Frobenius.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] [Finite k]

/-! ### The Frobenius of a scheme over a finite field -/

section Frobenius

variable (X : Over (Spec (.of k)))

/-- The `#k`-power Frobenius `F_X` of a scheme `X` over the finite field `k`, as a morphism over
`Spec k` (`Scheme.Hom.IsFrobenius.comp_eq`). It is unique: two `#k`-power Frobenii agree by
`Scheme.Hom.IsFrobenius.comp_eq_comp` applied to the identity. -/
noncomputable def overFrobenius : X ⟶ X :=
  Over.homMk X.hom.exists_isFrobenius.choose
    (X.hom.exists_isFrobenius.choose_spec.comp_eq X.hom)

lemma isFrobenius_overFrobenius_left : (overFrobenius X).left.IsFrobenius (Nat.card k) :=
  X.hom.exists_isFrobenius.choose_spec

variable {X} in
/-- The Frobenius commutes with every morphism over `Spec k`. -/
lemma comp_overFrobenius {Y : Over (Spec (.of k))} (f : X ⟶ Y) :
    f ≫ overFrobenius Y = overFrobenius X ≫ f := by
  ext1
  exact (isFrobenius_overFrobenius_left X).comp_eq_comp X.hom
    (isFrobenius_overFrobenius_left Y) f.left

/-- The `N`-th iterate of the Frobenius is the `#k ^ N`-power Frobenius. -/
lemma isFrobenius_frobeniusIterate_overFrobenius_left (N : ℕ) :
    (frobeniusIterate (overFrobenius X) N).left.IsFrobenius (Nat.card k ^ N) := by
  rw [frobeniusIterate_left]
  exact (isFrobenius_overFrobenius_left X).pow X.hom N

end Frobenius

/-! ### The Galois Frobenius of `Spec k̄` -/

section Galois

variable (k) in
/-- The ring endomorphism `y ↦ y ^ (#k ^ N)` of `k̄`. -/
noncomputable def powCardPowRingHom (N : ℕ) :
    CommRingCat.of (AlgebraicClosure k) ⟶ CommRingCat.of (AlgebraicClosure k) :=
  letI := Fintype.ofFinite k
  CommRingCat.ofHom ((FiniteField.frobeniusAlgHom k (AlgebraicClosure k)).toRingHom ^ N)

lemma powCardPowRingHom_apply (N : ℕ) (y : AlgebraicClosure k) :
    (powCardPowRingHom k N).hom y = y ^ (Nat.card k ^ N) := by
  let := Fintype.ofFinite k
  simp only [powCardPowRingHom, CommRingCat.hom_ofHom, RingHom.coe_pow]
  induction N generalizing y with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, ih, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card, ← pow_mul, pow_succ']

/-- The `N`-th power of the geometric Frobenius of `k̄` is a left inverse of the
`#k ^ N`-power map. -/
lemma geometricFrobenius_pow_apply_pow (N : ℕ) (y : AlgebraicClosure k) :
    ((FiniteField.geometricFrobenius k (AlgebraicClosure k)) ^ N) (y ^ (Nat.card k ^ N)) = y := by
  induction N generalizing y with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, AlgEquiv.mul_apply, pow_succ, pow_mul,
      (FiniteField.geometricFrobenius_eq_iff k (AlgebraicClosure k)).2 rfl, ih]


/-- The `N`-th power of the geometric Frobenius `σ` of `Spec k̄` is inverse to `Spec` of the
`#k ^ N`-power map of `k̄`: `σ^N ≫ Spec(y ↦ y ^ (#k ^ N)) = 𝟙`. -/
lemma geometricFrobeniusField_powSucc_hom_comp_specMap (n : ℕ) :
    ((geometricFrobeniusField k).powSucc n).hom ≫ Spec.map (powCardPowRingHom k (n + 1)) =
      𝟙 _ := by
  rw [Iso.powSucc_hom_eq_pow, geometricFrobeniusField_hom_pow, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext y
  change ((FiniteField.geometricFrobenius k (AlgebraicClosure k)) ^ (n + 1))
    ((powCardPowRingHom k (n + 1)).hom y) = y
  rw [powCardPowRingHom_apply]
  exact geometricFrobenius_pow_apply_pow (n + 1) y

/-- `Spec(y ↦ y ^ (#k ^ N)) ≫ σ^N = 𝟙`. -/
lemma specMap_comp_geometricFrobeniusField_powSucc_hom (n : ℕ) :
    Spec.map (powCardPowRingHom k (n + 1)) ≫ ((geometricFrobeniusField k).powSucc n).hom =
      𝟙 _ := by
  rw [← cancel_epi ((geometricFrobeniusField k).powSucc n).hom, ← Category.assoc,
    geometricFrobeniusField_powSucc_hom_comp_specMap, Category.id_comp, Category.comp_id]

end Galois

/-! ### The base change -/

section BaseChange

variable (k) in
/-- The base change functor `X ↦ X̄ = X ×_k k̄` from schemes over `Spec k` to schemes over
`Spec k̄`, along the geometric point `s : Spec k̄ ⟶ Spec k`. -/
noncomputable abbrev geometricBaseChange :
    Over (Spec (.of k)) ⥤ Over (Spec (.of (AlgebraicClosure k))) :=
  Over.pullback (specAlgebraicClosure k)

variable (X : Over (Spec (.of k)))

instance [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((geometricBaseChange k).obj X).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom (specAlgebraicClosure k)))

instance [QuasiCompact X.hom] : QuasiCompact ((geometricBaseChange k).obj X).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X.hom (specAlgebraicClosure k)))

instance [IsSeparated X.hom] : IsSeparated ((geometricBaseChange k).obj X).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X.hom (specAlgebraicClosure k)))

/-- The projection `π : X̄ ⟶ X` of the base change. -/
noncomputable def geometricBaseChangeProj : ((geometricBaseChange k).obj X).left ⟶ X.left :=
  pullback.fst X.hom (specAlgebraicClosure k)

omit [Finite k] in
lemma isPullback_geometricBaseChangeProj :
    IsPullback (geometricBaseChangeProj X) ((geometricBaseChange k).obj X).hom X.hom
      (specAlgebraicClosure k) :=
  IsPullback.of_hasPullback _ _

omit [Finite k] in
variable {X} in
/-- The base change of a morphism `f` lies over `f`: `f̄ ≫ π = π ≫ f`. -/
@[reassoc (attr := simp)]
lemma geometricBaseChange_map_left_comp_proj {Y : Over (Spec (.of k))} (f : X ⟶ Y) :
    ((geometricBaseChange k).map f).left ≫ geometricBaseChangeProj Y =
      geometricBaseChangeProj X ≫ f.left := by
  simp [geometricBaseChangeProj]

/-- The model Frobenius `Φ = (F_X^N ≫ g) ×_k k̄` of the base change `X̄`, for an endomorphism `g`
of `X` over `Spec k`: an endomorphism of `X̄` over `Spec k̄`. For an automorphism `e`, the model
Frobenius `(F_X^{n+1} ≫ e^{n+1}) ×_k k̄` is the Frobenius `σ^{n+1}` twisted by `e^{n+1}`. -/
noncomputable def modelFrobenius (N : ℕ) (g : X ⟶ X) :
    (geometricBaseChange k).obj X ⟶ (geometricBaseChange k).obj X :=
  (geometricBaseChange k).map (frobeniusIterate (overFrobenius X) N ≫ g)

/-- `Φ ≫ π = π ≫ F_X^N ≫ g`. -/
@[reassoc]
lemma modelFrobenius_left_comp_proj (N : ℕ) (g : X ⟶ X) :
    (modelFrobenius X N g).left ≫ geometricBaseChangeProj X =
      geometricBaseChangeProj X ≫ (frobeniusIterate (overFrobenius X) N ≫ g).left :=
  geometricBaseChange_map_left_comp_proj _

/-- For `g = 𝟙`, the model Frobenius `F_X^N ×_k k̄` is the `N`-th iterate of `F_X ×_k k̄`. -/
lemma modelFrobenius_id (N : ℕ) :
    modelFrobenius X N (𝟙 X) = frobeniusIterate (modelFrobenius X 1 (𝟙 X)) N := by
  simp only [modelFrobenius, Category.comp_id, frobeniusIterate_one]
  induction N with
  | zero => simp
  | succ N ih => rw [frobeniusIterate_succ, frobeniusIterate_succ, Functor.map_comp, ih]

/-- For `g = 𝟙`, the model Frobenius `F_X ×_k k̄` is the model Frobenius of the model `X` of
`X̄` over `k` (blueprint `sk-d-weil`). -/
theorem isModelFrobenius_modelFrobenius_one :
    IsModelFrobenius (modelFrobenius X 1 (𝟙 X)) X.hom (geometricBaseChangeProj X) where
  isPullback := isPullback_geometricBaseChangeProj X
  exists_isFrobenius := ⟨(overFrobenius X).left, isFrobenius_overFrobenius_left X, by
    rw [modelFrobenius_left_comp_proj, Category.comp_id, frobeniusIterate_one]⟩

/-- For `g = 𝟙` and `N ≠ 0`, the model Frobenius `F_X^N ×_k k̄` is the model Frobenius of a model
of `X̄` over the subfield `𝔽_{q^N}` of `k̄` (blueprint `sk-d-weil`). -/
theorem exists_isModelFrobenius_modelFrobenius_id [LocallyOfFiniteType X.hom] {N : ℕ}
    (hN : N ≠ 0) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₁ (AlgebraicClosure k))
      (X₁ : Scheme.{u}) (f₁ : X₁ ⟶ Spec (.of k₁)) (_ : LocallyOfFiniteType f₁)
      (p₁ : ((geometricBaseChange k).obj X).left ⟶ X₁),
      Nat.card k₁ = Nat.card k ^ N ∧ IsModelFrobenius (modelFrobenius X N (𝟙 X)) f₁ p₁ := by
  obtain ⟨k₁, _, _, _, _, _, hcard⟩ :=
    exists_finiteField_natCard_eq_pow k (AlgebraicClosure k) hN
  have h := (isModelFrobenius_modelFrobenius_one X).fieldChange (k₁ := k₁) hcard
  rw [← modelFrobenius_id] at h
  exact ⟨k₁, inferInstance, inferInstance, inferInstance, _, modelFieldChange X.hom k₁,
    inferInstance, _, hcard, h⟩

end BaseChange

/-! ### Rational points of the base change -/

section Points

variable {X : Over (Spec (.of k))}

/-- The `k̄`-rational point `x̄' = (x̄, 𝟙)` of `X̄ = X ×_k k̄` attached to a geometric point
`x̄ : Spec k̄ ⟶ X` over the geometric point `s` of the base. -/
noncomputable def geometricBaseChangePoint (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ X.hom = specAlgebraicClosure k) : RationalPoint ((geometricBaseChange k).obj X) :=
  Over.homMk (pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])) (by simp)

omit [Finite k] in
@[reassoc (attr := simp)]
lemma geometricBaseChangePoint_left_comp_proj (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ X.hom = specAlgebraicClosure k) :
    (geometricBaseChangePoint x hx).left ≫ geometricBaseChangeProj X = x :=
  pullback.lift_fst _ _ _

omit [Finite k] in
/-- A rational point of `X̄` is determined by its image in `X`. -/
lemma rationalPoint_ext {y y' : RationalPoint ((geometricBaseChange k).obj X)}
    (h : y.left ≫ geometricBaseChangeProj X = y'.left ≫ geometricBaseChangeProj X) : y = y' := by
  ext1
  refine pullback.hom_ext h ?_
  have hy := Over.w y
  have hy' := Over.w y'
  simp only [Over.pullback_obj_hom] at hy hy'
  exact hy.trans hy'.symm

omit [Finite k] in
/-- The rational point of `X̄` attached to the image `y ≫ π` of a rational point `y` is `y`. -/
lemma geometricBaseChangePoint_left_comp_proj_eq (y : RationalPoint ((geometricBaseChange k).obj X))
    (hy : (y.left ≫ geometricBaseChangeProj X) ≫ X.hom = specAlgebraicClosure k) :
    geometricBaseChangePoint (y.left ≫ geometricBaseChangeProj X) hy = y :=
  rationalPoint_ext (geometricBaseChangePoint_left_comp_proj _ _)

omit [Finite k] in
/-- The image `y ≫ π` of a rational point `y` of `X̄` lies over the geometric point `s`. -/
lemma rationalPoint_left_comp_proj_comp (y : RationalPoint ((geometricBaseChange k).obj X)) :
    (y.left ≫ geometricBaseChangeProj X) ≫ X.hom = specAlgebraicClosure k := by
  have hy := Over.w y
  simp only [Over.pullback_obj_hom] at hy
  rw [Category.assoc, geometricBaseChangeProj, pullback.condition, ← Category.assoc, hy]
  exact Category.id_comp _

/-- The geometric point `x̄` satisfies `x̄ ≫ g = σ^{n+1} ≫ x̄` if and only if the rational point
`x̄' = (x̄, 𝟙)` of `X̄` is fixed by the model Frobenius `Φ = (F_X^{n+1} ≫ g) ×_k k̄`: since
`x̄ ≫ F_X^{n+1} = Spec(y ↦ y ^ (#k ^ (n + 1))) ≫ x̄` and `Spec(y ↦ y ^ (#k ^ (n + 1)))` is the
inverse of `σ^{n+1}`. -/
theorem geometricBaseChangePoint_comp_modelFrobenius_eq_iff
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left) (hx : x ≫ X.hom = specAlgebraicClosure k)
    (n : ℕ) (g : X ⟶ X) :
    geometricBaseChangePoint x hx ≫ modelFrobenius X (n + 1) g = geometricBaseChangePoint x hx ↔
      x ≫ g.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x := by
  have hF : x ≫ (frobeniusIterate (overFrobenius X) (n + 1)).left =
      Spec.map (powCardPowRingHom k (n + 1)) ≫ x :=
    isFrobenius_frobeniusIterate_overFrobenius_left X (n + 1) x _
      (powCardPowRingHom_apply (n + 1))
  have key : geometricBaseChangePoint x hx ≫ modelFrobenius X (n + 1) g =
      geometricBaseChangePoint x hx ↔
      x ≫ (frobeniusIterate (overFrobenius X) (n + 1) ≫ g).left = x := by
    constructor
    · intro h
      have := congrArg (fun y ↦ y.left ≫ geometricBaseChangeProj X) h
      simpa [modelFrobenius_left_comp_proj] using this
    · intro h
      refine rationalPoint_ext ?_
      simpa [modelFrobenius_left_comp_proj] using h
  rw [Over.comp_left, ← Category.assoc, hF, Category.assoc] at key
  rw [key]
  constructor
  · intro h
    conv_rhs => rw [← h]
    rw [← Category.assoc, geometricFrobeniusField_powSucc_hom_comp_specMap, Category.id_comp]
  · intro h
    rw [h, ← Category.assoc, specMap_comp_geometricFrobeniusField_powSucc_hom, Category.id_comp]

/-- The points of degree `n + 1` of `X` for the Frobenius twisted by `e` are the rational points
of the base change `X̄ = X ×_k k̄` fixed by the model Frobenius
`Φ = (F_X^{n+1} ≫ e^{n+1}) ×_k k̄`: `x̄ ↦ (x̄, 𝟙)`. -/
noncomputable def frobeniusFixedPointsEquiv (e : X ≅ X) (n : ℕ) :
    frobeniusFixedPoints e n ≃
      {y : RationalPoint ((geometricBaseChange k).obj X) //
        y ≫ modelFrobenius X (n + 1) (e.powSucc n).hom = y} where
  toFun x := ⟨geometricBaseChangePoint x.1 x.2.1,
    (geometricBaseChangePoint_comp_modelFrobenius_eq_iff _ _ _ _).2 x.2.2⟩
  invFun y := ⟨y.1.left ≫ geometricBaseChangeProj X, rationalPoint_left_comp_proj_comp y.1, by
    rw [← geometricBaseChangePoint_comp_modelFrobenius_eq_iff _
      (rationalPoint_left_comp_proj_comp y.1), geometricBaseChangePoint_left_comp_proj_eq]
    exact y.2⟩
  left_inv x := Subtype.ext (geometricBaseChangePoint_left_comp_proj _ x.2.1)
  right_inv y := Subtype.ext
    (geometricBaseChangePoint_left_comp_proj_eq _ (rationalPoint_left_comp_proj_comp y.1))

end Points

end AlgebraicGeometry.ProEtale.CondensedRing
