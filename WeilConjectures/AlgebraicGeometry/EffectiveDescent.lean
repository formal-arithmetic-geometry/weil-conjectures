/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Effective descent for schemes

Let `p : X ⟶ Y` be a morphism of schemes. This file collects the descent statements for schemes
over `X` equipped with a descent datum relative to `p` (in the transport form
`CategoryTheory.Over.DescentDatum`) that are needed to descend the Jacobian of a curve from a
finite separable extension of the base field.

## Main statements

- `CategoryTheory.Over.DescentDatum.isEffective_of_isFinite`: along a surjective finite locally
  free morphism, descent data on schemes in which every finite set of points lies in an affine open
  (for instance projective schemes over a field) are effective (blueprint
  `thm-pd-effective-descent`).
- `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback`: compatible morphisms descend
  (blueprint `lem-pd-morphisms-descend`).
- `CategoryTheory.Over.DescentDatum.exists_commGrpObj_of_isPullback`: compatible group scheme
  structures descend (blueprint `lem-pd-group-scheme-descent`).
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback`:
  properness, smoothness of relative dimension `n` and geometric integrality descend along a field
  extension (blueprint `thm-pd-fpqc-local-properties`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y}

/-- **Effective descent for quasi-projective schemes.** Let `p : X ⟶ Y` be a surjective finite
locally free morphism and let `V` be a scheme over `X` in which every finite set of points lies in
an affine open, as is the case for a projective scheme over a field (Stacks 01ZY). Then every
descent datum on `V` relative to `p` is effective.

This is Stacks 0CCJ, via the criterion of Stacks 0CCI: the hypothesis on `V` is stronger than the
one needed there, which only asks it of the finite sets of points lying over one point of `Y`.

(blueprint: `thm-pd-effective-descent`) -/
theorem isEffective_of_isFinite [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    [Surjective p] {V : Over X}
    (hV : ∀ s : Set V.left, s.Finite → ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (D : Over.DescentDatum p V) : D.IsEffective :=
  sorry

section Points

variable {V : Over X} {V₀ : Over Y} {qV : V.left ⟶ V₀.left}

/-- Two points of `V` over the same `T`-point of `X` agree if their images in `V₀` agree, when `V`
is the base change of `V₀` along `p` through `qV`. -/
lemma hom_ext_of_isPullback (hqV : IsPullback qV V.hom V₀.hom p) {T : Scheme.{u}} {f : T ⟶ X}
    {a b : Over.mk f ⟶ V} (h : a.left ≫ qV = b.left ≫ qV) : a = b := by
  ext
  exact hqV.hom_ext h ((Over.w a).trans (Over.w b).symm)

/-- The point of `V` over `f : T ⟶ X` with image `g : T ⟶ V₀` in `V₀`, when `V` is the base
change of `V₀` along `p` through `qV`. -/
noncomputable def liftPoint (hqV : IsPullback qV V.hom V₀.hom p) {T : Scheme.{u}} (f : T ⟶ X)
    (g : T ⟶ V₀.left) (h : g ≫ V₀.hom = f ≫ p) : Over.mk f ⟶ V :=
  Over.homMk (hqV.lift g f h) (hqV.lift_snd g f h)

@[reassoc (attr := simp)]
lemma liftPoint_left_comp (hqV : IsPullback qV V.hom V₀.hom p) {T : Scheme.{u}} (f : T ⟶ X)
    (g : T ⟶ V₀.left) (h : g ≫ V₀.hom = f ≫ p) : (liftPoint hqV f g h).left ≫ qV = g :=
  hqV.lift_fst g f h

lemma liftPoint_eq (hqV : IsPullback qV V.hom V₀.hom p) {T : Scheme.{u}} {f : T ⟶ X}
    (a : Over.mk f ⟶ V) {g : T ⟶ V₀.left} (hg : a.left ≫ qV = g) (h : g ≫ V₀.hom = f ≫ p) :
    liftPoint hqV f g h = a :=
  hom_ext_of_isPullback hqV (by rw [liftPoint_left_comp, hg])

lemma liftPoint_congr (hqV : IsPullback qV V.hom V₀.hom p) {T : Scheme.{u}} (f : T ⟶ X)
    {g g' : T ⟶ V₀.left} (hg : g = g') (h : g ≫ V₀.hom = f ≫ p) (h' : g' ≫ V₀.hom = f ≫ p) :
    liftPoint hqV f g h = liftPoint hqV f g' h' := by
  subst hg
  rfl

lemma homMk_comp_liftPoint (hqV : IsPullback qV V.hom V₀.hom p) {T T' : Scheme.{u}}
    (t : T' ⟶ T) (f : T ⟶ X) (g : T ⟶ V₀.left) (h : g ≫ V₀.hom = f ≫ p) :
    (Over.homMk t : Over.mk (t ≫ f) ⟶ Over.mk f) ≫ liftPoint hqV f g h =
      liftPoint hqV (t ≫ f) (t ≫ g) (by rw [Category.assoc, h, Category.assoc]) :=
  hom_ext_of_isPullback hqV (by simp)

/-- If the transport of `D` is invariant under `qV`, the transport of a point `a` of `V` is the
unique point over the target with the same image in `V₀` as `a`. -/
lemma transport_eq_liftPoint (D : DescentDatum p V) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V) :
    D.transport f₁ f₂ h a = liftPoint hqV f₂ (a.left ≫ qV) (by
      rw [Category.assoc, hqV.w, ← Category.assoc, Over.w a]
      exact h) :=
  (liftPoint_eq hqV _ (hDV f₁ f₂ h a) _).symm

lemma transport_liftPoint (D : DescentDatum p V) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (g : T ⟶ V₀.left)
    (h₁ : g ≫ V₀.hom = f₁ ≫ p) (h₂ : g ≫ V₀.hom = f₂ ≫ p) :
    D.transport f₁ f₂ h (liftPoint hqV f₁ g h₁) = liftPoint hqV f₂ g h₂ := by
  rw [transport_eq_liftPoint D hqV hDV]
  exact liftPoint_congr hqV f₂ (liftPoint_left_comp hqV f₁ g h₁) _ _

/-- The point of `V` over `f'` with image `t ≫ c ≫ qV` in `V₀` is the transport of the
restriction of `c` along `t`. -/
lemma liftPoint_comp_eq_transport (D : DescentDatum p V) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    {T T' : Scheme.{u}} (t : T' ⟶ T) {f : T ⟶ X} (c : Over.mk f ⟶ V) (f' : T' ⟶ X)
    (h' : (t ≫ f) ≫ p = f' ≫ p) (h : (t ≫ c.left ≫ qV) ≫ V₀.hom = f' ≫ p) :
    liftPoint hqV f' (t ≫ c.left ≫ qV) h =
      D.transport (t ≫ f) f' h' ((Over.homMk t : Over.mk (t ≫ f) ⟶ Over.mk f) ≫ c) := by
  rw [transport_eq_liftPoint D hqV hDV]
  refine liftPoint_congr hqV f' ?_ _ _
  simp

end Points

variable {V : Over X}

/-- The points of the descended object with values in `U : Over Y`, expressed through `V` and
the descent datum `D`: for every `T`-point `g` of `U` and every lift `f : T ⟶ X` of `g ≫ U.hom`
along `p`, a point of `V` over `f`, natural in `T` and compatible with the transport of `D`.
When `D` is effective with descended object `V₀`, these are the morphisms `U ⟶ V₀` over `Y`
(`CategoryTheory.Over.DescentDatum.DescentPoints.homEquiv`). -/
structure DescentPoints (D : DescentDatum p V) (U : Over Y) : Type (u + 1) where
  /-- The point of `V` over `f` attached to the point `g` of `U`. -/
  point {T : Scheme.{u}} (f : T ⟶ X) (g : T ⟶ U.left) (h : g ≫ U.hom = f ≫ p) : Over.mk f ⟶ V
  point_comp {T T' : Scheme.{u}} (t : T' ⟶ T) (f : T ⟶ X) (g : T ⟶ U.left)
    (h : g ≫ U.hom = f ≫ p) :
    point (t ≫ f) (t ≫ g) (by rw [Category.assoc, h, Category.assoc]) =
      (Over.homMk t : Over.mk (t ≫ f) ⟶ Over.mk f) ≫ point f g h
  transport_point {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (g : T ⟶ U.left) (h₁ : g ≫ U.hom = f₁ ≫ p)
    (h₂ : g ≫ U.hom = f₂ ≫ p) :
    D.transport f₁ f₂ (h₁.symm.trans h₂) (point f₁ g h₁) = point f₂ g h₂

namespace DescentPoints

variable {D : DescentDatum p V} {U : Over Y}

@[ext]
lemma ext {x y : DescentPoints D U}
    (h : ∀ {T : Scheme.{u}} (f : T ⟶ X) (g : T ⟶ U.left) (hg : g ≫ U.hom = f ≫ p),
      x.point f g hg = y.point f g hg) : x = y := by
  obtain ⟨px, _, _⟩ := x
  obtain ⟨py, _, _⟩ := y
  obtain rfl : @px = @py := by
    funext T f g hg
    exact h f g hg
  rfl

lemma point_congr (x : DescentPoints D U) {T : Scheme.{u}} (f : T ⟶ X) {g g' : T ⟶ U.left}
    (hg : g = g') (h : g ≫ U.hom = f ≫ p) (h' : g' ≫ U.hom = f ≫ p) :
    x.point f g h = x.point f g' h' := by
  subst hg
  rfl

lemma comp_point_left (x : DescentPoints D U) {T T' : Scheme.{u}} (t : T' ⟶ T) (f : T ⟶ X)
    (g : T ⟶ U.left) (h : g ≫ U.hom = f ≫ p) :
    t ≫ (x.point f g h).left =
      (x.point (t ≫ f) (t ≫ g) (by rw [Category.assoc, h, Category.assoc])).left := by
  rw [x.point_comp]
  rfl

/-- The images in `V₀` of the points of a family only depend on the point of `U`. -/
lemma point_left_comp_eq {V₀ : Over Y} {qV : V.left ⟶ V₀.left}
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (x : DescentPoints D U) {T : Scheme.{u}} {f₁ f₂ : T ⟶ X} {g₁ g₂ : T ⟶ U.left}
    (hg : g₁ = g₂) (h₁ : g₁ ≫ U.hom = f₁ ≫ p) (h₂ : g₂ ≫ U.hom = f₂ ≫ p) :
    (x.point f₁ g₁ h₁).left ≫ qV = (x.point f₂ g₂ h₂).left ≫ qV := by
  subst hg
  rw [← x.transport_point f₁ f₂ g₁ h₁ h₂, hDV]

/-- The restriction of a family of points along `u : U' ⟶ U`. -/
def comap (x : DescentPoints D U) {U' : Over Y} (u : U' ⟶ U) : DescentPoints D U' where
  point f g h := x.point f (g ≫ u.left) (by rw [Category.assoc, Over.w u, h])
  point_comp t f g h := by
    rw [← x.point_comp]
    exact x.point_congr _ (Category.assoc _ _ _) _ _
  transport_point f₁ f₂ g h₁ h₂ := x.transport_point _ _ _ _ _

lemma comap_id (x : DescentPoints D U) : x.comap (𝟙 U) = x := by
  refine DescentPoints.ext fun f g h ↦ x.point_congr _ ?_ _ _
  simp

lemma comap_comp (x : DescentPoints D U) {U' U'' : Over Y} (u : U' ⟶ U) (u' : U'' ⟶ U') :
    x.comap (u' ≫ u) = (x.comap u).comap u' := by
  refine DescentPoints.ext fun f g h ↦ x.point_congr _ ?_ _ _
  simp

variable {V₀ : Over Y} {qV : V.left ⟶ V₀.left}

/-- The family of points of `V` defined by a morphism `u : U ⟶ V₀` over `Y`. -/
noncomputable def ofHom (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (u : U ⟶ V₀) : DescentPoints D U where
  point f g h := liftPoint hqV f (g ≫ u.left) (by rw [Category.assoc, Over.w u, h])
  point_comp t f g h := by
    rw [homMk_comp_liftPoint]
    exact liftPoint_congr hqV _ (Category.assoc _ _ _) _ _
  transport_point f₁ f₂ g h₁ h₂ := transport_liftPoint D hqV hDV _ _ _ _ _ _

variable [Flat p] [Surjective p] [QuasiCompact p]

/-- The morphism `U ⟶ V₀` over `Y` defined by a family of points of `V`: it is obtained by
descending along the base change `U ×_Y X ⟶ U` of `p`, which is an effective epimorphism. -/
noncomputable def desc (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (x : DescentPoints D U) : U ⟶ V₀ :=
  Over.homMk (EffectiveEpi.desc (pullback.fst U.hom p)
    ((x.point (pullback.snd U.hom p) (pullback.fst U.hom p) pullback.condition).left ≫ qV)
    (fun g₁ g₂ hg ↦ by
      rw [← Category.assoc, ← Category.assoc, x.comp_point_left, x.comp_point_left]
      exact x.point_left_comp_eq hDV hg _ _))
    (by
      rw [← cancel_epi (pullback.fst U.hom p), EffectiveEpi.fac_assoc, Category.assoc, hqV.w,
        ← Category.assoc, Over.w]
      exact pullback.condition.symm)

@[reassoc]
lemma fst_comp_desc_left (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (x : DescentPoints D U) :
    pullback.fst U.hom p ≫ (x.desc hqV hDV).left =
      (x.point (pullback.snd U.hom p) (pullback.fst U.hom p) pullback.condition).left ≫ qV := by
  simp [desc]

lemma point_left_comp (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (x : DescentPoints D U) {T : Scheme.{u}} (f : T ⟶ X) (g : T ⟶ U.left)
    (h : g ≫ U.hom = f ≫ p) :
    (x.point f g h).left ≫ qV = g ≫ (x.desc hqV hDV).left := by
  calc (x.point f g h).left ≫ qV =
      (x.point (pullback.lift g f h ≫ pullback.snd U.hom p)
        (pullback.lift g f h ≫ pullback.fst U.hom p) (by simp [h])).left ≫ qV :=
        x.point_left_comp_eq hDV (by simp) _ _
    _ = g ≫ (x.desc hqV hDV).left := by
      rw [← x.comp_point_left _ _ _ pullback.condition, Category.assoc,
        ← fst_comp_desc_left hqV hDV, ← Category.assoc, pullback.lift_fst]

/-- **Descent of points.** Morphisms `U ⟶ V₀` over `Y` correspond to families of points of `V`
compatible with the descent datum. -/
noncomputable def homEquiv (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV) :
    (U ⟶ V₀) ≃ DescentPoints D U where
  toFun := ofHom hqV hDV
  invFun x := x.desc hqV hDV
  left_inv u := by
    ext1
    rw [← cancel_epi (pullback.fst U.hom p),
      ← point_left_comp hqV hDV _ (pullback.snd U.hom p) _ pullback.condition]
    exact liftPoint_left_comp hqV _ _ _
  right_inv x := by
    exact DescentPoints.ext fun f g h ↦ liftPoint_eq hqV _ (point_left_comp hqV hDV x f g h) _

lemma homEquiv_apply_point (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (u : U ⟶ V₀) {T : Scheme.{u}} (f : T ⟶ X) (g : T ⟶ U.left) (h : g ≫ U.hom = f ≫ p) :
    (homEquiv hqV hDV u).point f g h =
      liftPoint hqV f (g ≫ u.left) (by rw [Category.assoc, Over.w u, h]) :=
  rfl

end DescentPoints

section Group

variable (D : DescentDatum p V)

lemma transport_mul [MonObj V]
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V) :
    D.transport f₁ f₂ h (a * b) = D.transport f₁ f₂ h a * D.transport f₁ f₂ h b :=
  hμ f₁ f₂ h a b

lemma transport_one [MonObj V]
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V])
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) :
    D.transport f₁ f₂ h 1 = 1 :=
  hη f₁ f₂ h

lemma transport_inv [GrpObj V]
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V])
    {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V) :
    D.transport f₁ f₂ h a⁻¹ = (D.transport f₁ f₂ h a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← transport_mul D hμ, inv_mul_cancel, transport_one D hη])

variable [CommGrpObj V]
  (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
    D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
      lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
  (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
    D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V])

/-- The pointwise commutative group structure on the families of points of a commutative group
object `V` with a descent datum compatible with the group law. -/
noncomputable abbrev DescentPoints.commGroup (U : Over Y) : CommGroup (DescentPoints D U) where
  mul x y :=
    { point f g h := x.point f g h * y.point f g h
      point_comp t f g h := by rw [x.point_comp, y.point_comp, MonObj.comp_mul]
      transport_point f₁ f₂ g h₁ h₂ := by
        rw [transport_mul D hμ, x.transport_point, y.transport_point] }
  mul_assoc x y z := DescentPoints.ext fun f g h ↦ mul_assoc _ _ _
  one :=
    { point _ _ _ := 1
      point_comp t f g h := (MonObj.comp_one _).symm
      transport_point f₁ f₂ g h₁ h₂ := transport_one D hη _ _ _ }
  one_mul x := DescentPoints.ext fun f g h ↦ one_mul _
  mul_one x := DescentPoints.ext fun f g h ↦ mul_one _
  inv x :=
    { point f g h := (x.point f g h)⁻¹
      point_comp t f g h := by rw [x.point_comp, GrpObj.comp_inv]
      transport_point f₁ f₂ g h₁ h₂ := by rw [transport_inv D hμ hη, x.transport_point] }
  inv_mul_cancel x := DescentPoints.ext fun f g h ↦ inv_mul_cancel _
  mul_comm x y := DescentPoints.ext fun f g h ↦ mul_comm _ _

/-- The presheaf of commutative groups `U ↦ DescentPoints D U` on `Over Y`. -/
noncomputable def DescentPoints.functor : (Over Y)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj U :=
    letI := DescentPoints.commGroup D hμ hη U.unop
    CommGrpCat.of (DescentPoints D U.unop)
  map {U U'} u :=
    letI := DescentPoints.commGroup D hμ hη U.unop
    letI := DescentPoints.commGroup D hμ hη U'.unop
    CommGrpCat.ofHom
      { toFun x := x.comap u.unop
        map_one' := rfl
        map_mul' _ _ := rfl }
  map_id U := by
    let := DescentPoints.commGroup D hμ hη U.unop
    ext x : 2
    exact x.comap_id
  map_comp {U U' U''} u u' := by
    let := DescentPoints.commGroup D hμ hη U.unop
    let := DescentPoints.commGroup D hμ hη U''.unop
    ext x : 2
    exact x.comap_comp _ _

variable [Flat p] [Surjective p] [QuasiCompact p] {V₀ : Over Y} {qV : V.left ⟶ V₀.left}

/-- The descended object `V₀` represents the presheaf of families of points of `V`. -/
noncomputable def DescentPoints.representableBy (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV) :
    (DescentPoints.functor D hμ hη ⋙ CategoryTheory.forget CommGrpCat).RepresentableBy V₀ where
  homEquiv := DescentPoints.homEquiv hqV hDV
  homEquiv_comp u u' := by
    apply DescentPoints.ext
    intro T f g h
    refine liftPoint_congr hqV f ?_ _ _
    simp

end Group

/-- **Morphisms descend.** Let `p : X ⟶ Y` be faithfully flat and quasi-compact, and let `V`, `W`
be schemes over `X` with descent data `D`, `E` that are effective, with descended schemes `V₀`,
`W₀` over `Y` and projections `qV`, `qW`. Then every morphism `ψ : V ⟶ W` over `X` compatible with
the two descent data is the base change of a unique morphism `ψ₀ : V₀ ⟶ W₀` over `Y`.

This is the full faithfulness of base change into descent data, Stacks 02W0.

(blueprint: `lem-pd-morphisms-descend`) -/
theorem existsUnique_hom_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V W : Over X}
    (D : Over.DescentDatum p V) (E : Over.DescentDatum p W) {V₀ W₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (qW : W.left ⟶ W₀.left) (hqW : IsPullback qW W.hom W₀.hom p)
    (hEW : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ W),
      (E.transport f₁ f₂ h a).left ≫ qW = a.left ≫ qW)
    (ψ : V ⟶ W)
    (hψ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      E.transport f₁ f₂ h (a ≫ ψ) = D.transport f₁ f₂ h a ≫ ψ) :
    ∃! ψ₀ : V₀ ⟶ W₀, ψ.left ≫ qW = qV ≫ ψ₀.left := by
  let Φ : DescentPoints E V₀ :=
    { point f g h := liftPoint hqV f g h ≫ ψ
      point_comp t f g h := by rw [← Category.assoc, homMk_comp_liftPoint]
      transport_point f₁ f₂ g h₁ h₂ := by rw [hψ, transport_liftPoint D hqV hDV] }
  refine ⟨(DescentPoints.homEquiv hqW hEW).symm Φ, ?_, fun ψ₀ hψ₀ ↦ ?_⟩
  · have hl : (liftPoint hqV V.hom qV hqV.w).left = 𝟙 _ := hqV.hom_ext (by simp) (by simp)
    refine Eq.trans ?_ (DescentPoints.point_left_comp hqW hEW Φ V.hom qV hqV.w)
    rw [Over.comp_left, hl, Category.id_comp]
  · rw [Equiv.eq_symm_apply]
    refine DescentPoints.ext fun f g h ↦ liftPoint_eq hqW _ ?_ _
    rw [Over.comp_left, Category.assoc, hψ₀, liftPoint_left_comp_assoc]

/-- The point `qV ∘ a` of `V₀` over `Y` induced by a point `a` of `V` over `f`, for a projection
`qV : V ⟶ V₀` exhibiting `V` as the base change of `V₀` along `p`. -/
abbrev descendPoint {V : Over X} {V₀ : Over Y} {qV : V.left ⟶ V₀.left}
    (hqV : IsPullback qV V.hom V₀.hom p) {T : Scheme.{u}} {f : T ⟶ X} (a : Over.mk f ⟶ V) :
    Over.mk (f ≫ p) ⟶ V₀ :=
  Over.homMk (a.left ≫ qV) (by
    simp only [Over.mk_hom, Category.assoc, hqV.w]
    rw [← Category.assoc, Over.w a]
    rfl)

/-- **The descended scheme is a group scheme.** Let `p : X ⟶ Y` be faithfully flat and
quasi-compact, let `V` be a scheme over `X` with an effective descent datum `D`, with descended
scheme `V₀` and projection `qV`, and let `V` carry a commutative group scheme structure whose
multiplication and unit are compatible with `D`. Then `V₀` carries a commutative group scheme
structure over `Y` whose base change is the given one: `qV` maps products of points of `V` to
products of points of `V₀`. Such a structure is unique, by the same token.

(blueprint: `lem-pd-group-scheme-descent`) -/
theorem exists_commGrpObj_of_isPullback [Flat p] [Surjective p] [QuasiCompact p] {V : Over X}
    [CommGrpObj V] (D : Over.DescentDatum p V) {V₀ : Over Y} (qV : V.left ⟶ V₀.left)
    (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
      D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    ∃ _ : CommGrpObj V₀, ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀] := by
  let α := DescentPoints.representableBy D hμ hη hqV hDV
  let : CommGrpObj V₀ := .ofRepresentableBy V₀ _ α
  refine ⟨this, fun {T} f a b ↦ ?_⟩
  apply α.homEquiv'.injective
  have hμ₀ : μ[V₀] = α.homEquiv'.symm (α.homEquiv' (fst V₀ V₀) * α.homEquiv' (snd V₀ V₀)) :=
    rfl
  rw [hμ₀]
  simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
  simp only [← α.homEquiv'_comp, lift_fst, lift_snd]
  refine DescentPoints.ext fun f' g h ↦ ?_
  have e (c : Over.mk f ⟶ V) (hc) :
      liftPoint hqV f' (g ≫ (descendPoint hqV c).left) hc =
        D.transport (g ≫ f) f' ((Category.assoc _ _ _).trans h)
          ((Over.homMk g : Over.mk (g ≫ f) ⟶ Over.mk f) ≫ c) :=
    liftPoint_comp_eq_transport D hqV hDV g c f' _ hc
  refine (e _ _).trans ((congrArg (D.transport _ _ _) (MonObj.comp_mul _ a b)).trans
    ((transport_mul D hμ _ _ _ _ _).trans ?_))
  exact congrArg₂ (· * ·) (e a _).symm (e b _).symm

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry

open MorphismProperty

open scoped TensorProduct

/-- **Separatedness satisfies fpqc descent.** The diagonal of the base change is the base change
of the diagonal, universal closedness descends, and an immersion with closed image is a closed
immersion. -/
instance isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong @IsSeparated (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : IsSeparated fst := hfst
    have hg : diagonal @UniversallyClosed g :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := diagonal @UniversallyClosed) h hf
        (diagonal_iff.mpr inferInstance)
    have : UniversallyClosed (pullback.diagonal g) := diagonal_iff.mp hg
    exact ⟨.of_isPreimmersion _ (pullback.diagonal g).isClosedMap.isClosed_range⟩

/-- **Properness satisfies fpqc descent.** -/
instance isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong @IsProper (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [isProper_eq]
  infer_instance

/-- Reducedness descends along flat surjective morphisms: the stalk maps of a flat morphism are
flat local homomorphisms, hence faithfully flat and injective. -/
lemma isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact isReduced_of_injective _ ‹RingHom.FaithfullyFlat _›.injective
  exact isReduced_of_isReduced_stalk Y

/-- Let `k ⊆ K` be a field extension and `Z'` the base change of a `k`-scheme `Z` to `K`. Every
base change `W` of `Z` to a field `Ω` over `k` receives a flat surjective morphism from a base
change `P` of `Z'` to a field `L`, namely `P = W ×_Ω L` for a field `L` containing `Ω` and `K`. -/
lemma exists_isPullback_flat_surjective_of_isPullback {k K Ω : Type u} [Field k] [Field K]
    [Field Ω] [Algebra k K] [Algebra k Ω] {Z Z' W : Scheme.{u}} {z : Z ⟶ Spec (.of k)}
    {z' : Z' ⟶ Spec (.of K)} {q : Z' ⟶ Z}
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K)))) {fst : W ⟶ Z}
    {snd : W ⟶ Spec (.of Ω)}
    (hW : IsPullback fst snd z (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) :
    ∃ (L : Type u) (_ : Field L) (ψ : K →+* L) (P : Scheme.{u}) (a : P ⟶ Z')
      (b : P ⟶ Spec (.of L)) (c : P ⟶ W),
      IsPullback a b z' (Spec.map (CommRingCat.ofHom ψ)) ∧ Flat c ∧ Surjective c := by
  have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k Ω K
    (algebraMap k Ω).injective (algebraMap k K).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω ⊗[k] K)
  let L := Ω ⊗[k] K ⧸ m
  let : Field L := Ideal.Quotient.field m
  let ψΩ : Ω →+* L := (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom
  let ψK : K →+* L := (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom
  have hψ : ψΩ.comp (algebraMap k Ω) = ψK.comp (algebraMap k K) := by
    ext x
    exact congrArg (Ideal.Quotient.mk m) (Algebra.TensorProduct.tmul_one_eq_one_tmul x)
  have hψ' : Spec.map (CommRingCat.ofHom ψΩ) ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      Spec.map (CommRingCat.ofHom ψK) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hψ]
  let : Algebra Ω L := ψΩ.toAlgebra
  have : Flat (Spec.map (CommRingCat.ofHom ψΩ)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Surjective (Spec.map (CommRingCat.ofHom ψΩ)) :=
    ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have hP := IsPullback.of_hasPullback snd (Spec.map (CommRingCat.ofHom ψΩ))
  have hPW := hP.paste_horiz hW
  rw [hψ'] at hPW
  refine ⟨L, inferInstance, ψK, _, h.lift (pullback.fst _ _ ≫ fst)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψK)) (by simpa using hPW.w),
    pullback.snd _ _, pullback.fst _ _, ?_, inferInstance, inferInstance⟩
  exact IsPullback.of_right (by rwa [h.lift_fst]) (by simp) h

/-- **Geometric irreducibility descends along field extensions.** -/
lemma geometricallyIrreducible_of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k)) (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [GeometricallyIrreducible z'] : GeometricallyIrreducible z := by
  refine ⟨geometrically_iff_of_commRing.mpr fun Ω _ _ W fst snd hW ↦ ?_⟩
  obtain ⟨L, _, ψ, P, a, b, c, hP, -, hc⟩ := exists_isPullback_flat_surjective_of_isPullback h hW
  have : IrreducibleSpace P :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ a b hP
  exact c.surjective.irreducibleSpace c.continuous

/-- **Geometric reducedness descends along field extensions.** -/
lemma geometricallyReduced_of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k)) (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [GeometricallyReduced z'] : GeometricallyReduced z := by
  refine ⟨geometrically_iff_of_commRing.mpr fun Ω _ _ W fst snd hW ↦ ?_⟩
  obtain ⟨L, _, ψ, P, a, b, c, hP, _, _⟩ := exists_isPullback_flat_surjective_of_isPullback h hW
  have : IsReduced P := GeometricallyReduced.geometrically_isReduced _ a b hP
  exact isReduced_of_flat_of_surjective c

open RingHom in
/-- The relative dimension of a locally standard smooth ring homomorphism with nontrivial target
is unique: both relative dimensions are the rank of the module of Kähler differentials on a
common basic open. -/
lemma _root_.RingHom.Locally.isStandardSmoothOfRelativeDimension_unique {A B : Type u}
    [CommRing A] [CommRing B] [Nontrivial B] {φ : A →+* B} {m n : ℕ}
    (hm : Locally (IsStandardSmoothOfRelativeDimension m) φ)
    (hn : Locally (IsStandardSmoothOfRelativeDimension n) φ) : m = n := by
  obtain ⟨s₁, hs₁, h₁⟩ := hm
  obtain ⟨s₂, hs₂, h₂⟩ := hn
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  have hmem (s : Set B) (hs : Ideal.span s = ⊤) : ∃ t ∈ s, t ∉ 𝔪 := by
    by_contra! H
    exact h𝔪.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr H))
  obtain ⟨t₁, ht₁, ht₁𝔪⟩ := hmem s₁ hs₁
  obtain ⟨t₂, ht₂, ht₂𝔪⟩ := hmem s₂ hs₂
  let C := Localization.Away (algebraMap B (Localization.Away t₁) t₂)
  let C' := Localization.Away (algebraMap B (Localization.Away t₂) t₁)
  have hC : IsStandardSmoothOfRelativeDimension m ((algebraMap B C).comp φ) := by
    have := (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      m).right C (algebraMap B (Localization.Away t₁) t₂) _ (h₁ t₁ ht₁)
    rwa [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at this
  have hC' : IsStandardSmoothOfRelativeDimension n ((algebraMap B C').comp φ) := by
    have := (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      n).right C' (algebraMap B (Localization.Away t₂) t₁) _ (h₂ t₂ ht₂)
    rwa [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] at this
  let e : C ≃ₐ[B] C' := IsLocalization.algEquiv (Submonoid.powers (t₁ * t₂)) C C'
  have hC'm : IsStandardSmoothOfRelativeDimension m ((algebraMap B C').comp φ) := by
    have he : e.toRingEquiv.toRingHom.comp (algebraMap B C) = algebraMap B C' :=
      RingHom.ext e.commutes
    have := isStandardSmoothOfRelativeDimension_respectsIso.1 _ e.toRingEquiv hC
    rwa [← RingHom.comp_assoc, he] at this
  have : Nontrivial C' := by
    have hu : IsUnit (algebraMap B (Localization.AtPrime 𝔪) (t₁ * t₂)) :=
      IsLocalization.map_units (Localization.AtPrime 𝔪)
        (⟨t₁ * t₂, h𝔪.isPrime.mul_notMem ht₁𝔪 ht₂𝔪⟩ : 𝔪.primeCompl)
    exact (IsLocalization.Away.lift (S := C') (t₁ * t₂) hu).domain_nontrivial
  let := ((algebraMap B C').comp φ).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension m A C' := hC'm
  have : Algebra.IsStandardSmoothOfRelativeDimension n A C' := hC'
  have hrm := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A)
    (S := C') m
  have hrn := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A)
    (S := C') n
  exact_mod_cast hrm.symm.trans hrn

/-- The relative dimension of a smooth morphism with nonempty source is unique. -/
lemma SmoothOfRelativeDimension.eq_of_nonempty {X Y : Scheme.{u}} (f : X ⟶ Y) [Nonempty X]
    {m n : ℕ} [hm : SmoothOfRelativeDimension m f] [SmoothOfRelativeDimension n f] : m = n := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  exact RingHom.Locally.isStandardSmoothOfRelativeDimension_unique
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h)
    (HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension n) f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ e)

/-- **Smoothness of relative dimension `n` descends along field extensions.** The morphism `z`
is smooth by fpqc descent, so it is locally standard smooth of some relative dimension `m`; the
base change of such a chart is a nonempty open of `Z'`, smooth of relative dimension both `m` and
`n` over `K`, so `m = n`. -/
lemma smoothOfRelativeDimension_of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k)) (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (n : ℕ)
    [SmoothOfRelativeDimension n z'] : SmoothOfRelativeDimension n z := by
  have hS : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := ⟨⟨‹_›, ‹_›⟩, inferInstance⟩
  have : Smooth z := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) h.flip hQ
    (SmoothOfRelativeDimension.smooth n z')
  have : Surjective q := MorphismProperty.of_isPullback h.flip hS
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hφ⟩ := Smooth.exists_isStandardSmooth z x
  obtain ⟨m, hm⟩ : ∃ m, (z.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    let := (z.appLE U V e).hom.toAlgebra
    obtain ⟨I, J, _, _, ⟨P⟩⟩ := hφ
    exact ⟨P.dimension, I, J, ‹_›, ‹_›, P, rfl⟩
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  obtain rfl : m = n := by
    have : IsAffine V := hV
    have : IsAffine U := hU
    have h1 : SmoothOfRelativeDimension m (z.resLE U V e) := by
      have : (RingHom.toMorphismProperty
          (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m))).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp
          (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
      rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension m)]
      exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
        (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m)))
        (arrowResLEAppIso z U V e)).mpr
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hm)
    have h2 : SmoothOfRelativeDimension (m + 0) (z.resLE U V e ≫ U.ι) := inferInstance
    rw [Scheme.Hom.resLE_comp_ι] at h2
    have h3 : SmoothOfRelativeDimension m ((q ⁻¹ᵁ V).ι ≫ z') :=
      have := smoothOfRelativeDimension_isStableUnderBaseChange (n := m)
      MorphismProperty.of_isPullback ((isPullback_morphismRestrict q V).paste_vert h) h2
    have : SmoothOfRelativeDimension (0 + n) ((q ⁻¹ᵁ V).ι ≫ z') := inferInstance
    obtain ⟨x', rfl⟩ := q.surjective x
    have : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x', hx⟩⟩
    have := SmoothOfRelativeDimension.eq_of_nonempty ((q ⁻¹ᵁ V).ι ≫ z') (m := m) (n := 0 + n)
    omega
  exact hm

/-- **Properties of morphisms are local in the fpqc topology on the target.** Let `k ⊆ K` be a
field extension and let `Z` be a scheme over `k` whose base change `Z_K` is proper, smooth of
relative dimension `n` and geometrically integral over `K`. Then so is `Z` over `k`.

For properness and smoothness this is Stacks 02YJ, 02VL, 02KL and 05B5, the morphism
`Spec K ⟶ Spec k` being faithfully flat and quasi-compact; the relative dimension is read off on
fibres. Geometric integrality descends because for every field `Ω` over `k` there is a field `L`
containing both `Ω` and `K`, and `Z_L ⟶ Z_Ω` is faithfully flat: reducedness descends along it
and irreducibility passes to the image.

The blueprint states this for finite extensions and lists finite type, smoothness, properness and
connectedness; the form here holds for any field extension and carries the properties used to
recognise an abelian variety of dimension `g`.

(blueprint: `thm-pd-fpqc-local-properties`) -/
theorem isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback {k K : Type u}
    [Field k] [Field K] [Algebra k K] {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k))
    (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (n : ℕ)
    [IsProper z'] [SmoothOfRelativeDimension n z'] [GeometricallyIntegral z'] :
    IsProper z ∧ SmoothOfRelativeDimension n z ∧ GeometricallyIntegral z := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have := geometricallyReduced_of_isPullback z z' q h
  have := geometricallyIrreducible_of_isPullback z z' q h
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := ⟨⟨‹_›, ‹_›⟩, inferInstance⟩
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper) h.flip hQ ‹_›,
    smoothOfRelativeDimension_of_isPullback z z' q h n,
    .of_geometricallyReduced_of_geometricallyIrreducible z⟩

end AlgebraicGeometry
