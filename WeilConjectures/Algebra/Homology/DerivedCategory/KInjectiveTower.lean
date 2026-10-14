/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedCategory.Products
public import WeilConjectures.Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The Roos resolution of a tower

Let `A` be an abelian category with countable products and `X : ℕᵒᵖ ⥤ A` a tower. Write
`R_b : A ⥤ (ℕᵒᵖ ⥤ A)` for the right adjoint of evaluation at `b`, so that `(R_b a)ₖ = a` if
`b ≤ k` and `0` otherwise. There is a short exact sequence of towers

```
  0 ⟶ X ⟶ ∏ₙ Rₙ(Xₙ) ──d──▶ ∏ₙ Rₙ₊₁(Xₙ) ⟶ 0
```

which is split at each level, and whose limit is `lim X ⟶ ∏ Xₙ ──1 - t──▶ ∏ Xₙ`. The two
right-hand terms are made of right adjoints of exact functors, so they preserve K-injectivity.

## Main definitions

- `CategoryTheory.Tower.roos`: the functors `∏ₙ R_{b n}(Xₙ)`.
- `CategoryTheory.Tower.roosShortComplex`: the short exact sequence above, and
  `CategoryTheory.Tower.roosComplexShortComplex` its version for complexes of towers.

## Main statements

- `CategoryTheory.Tower.roosShortComplex_shortExact`: the sequence is short exact.
- `CategoryTheory.Tower.isKInjective_roosComplex`: if `I` is a K-injective complex of towers,
  so are the complexes `∏ₙ R_{b n}(Iₙ)`.
- `CategoryTheory.Tower.isLimitLimRoosFan`: `lim ∏ₙ R_{b n}(Iₙ)` is the product `∏ₙ Iₙ`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Tower

variable {A : Type u} [Category.{v} A]

instance (a b : ℕᵒᵖ) : Subsingleton (a ⟶ b) :=
  ⟨fun _ _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩

instance (a b : ℕᵒᵖ) : Finite (a ⟶ b) := Finite.of_subsingleton

lemma hom_eq_homOfLE {k n : ℕ} (g : op k ⟶ op n) : g = (homOfLE (leOfHom g.unop)).op :=
  Subsingleton.elim _ _

section

variable [HasCountableProducts A]

/-- The right adjoint `R_b` of evaluation at `b`: `(R_b a)ₖ = ∏_{k ⟶ b} a`. -/
noncomputable abbrev R (b : ℕ) : A ⥤ (ℕᵒᵖ ⥤ A) := evaluationRightAdjoint A (op b)

/-- The tower `∏ₙ R_{b n}(Xₙ)`, with `k`-th term `∏ₙ ∏_{k ⟶ b n} Xₙ`. -/
@[simps obj]
noncomputable def roosObj (b : ℕ → ℕ) (X : ℕᵒᵖ ⥤ A) : ℕᵒᵖ ⥤ A where
  obj k := ∏ᶜ fun n : ℕ ↦ ∏ᶜ fun _ : k ⟶ op (b n) ↦ X.obj (op n)
  map f := Pi.lift fun n ↦ Pi.π _ n ≫ Pi.lift fun g ↦ Pi.π _ (f ≫ g)
  map_id k := Pi.hom_ext _ _ fun n ↦ Pi.hom_ext _ _ fun g ↦ by simp
  map_comp f f' := Pi.hom_ext _ _ fun n ↦ Pi.hom_ext _ _ fun g ↦ by simp

lemma roosObj_hom_ext {b : ℕ → ℕ} {X : ℕᵒᵖ ⥤ A} {k : ℕᵒᵖ} {Y : A}
    {f f' : Y ⟶ (roosObj b X).obj k}
    (h : ∀ (n : ℕ) (g : k ⟶ op (b n)), f ≫ Pi.π _ n ≫ Pi.π _ g = f' ≫ Pi.π _ n ≫ Pi.π _ g) :
    f = f' :=
  Pi.hom_ext _ _ fun n ↦ Pi.hom_ext _ _ fun g ↦ by simpa using h n g

@[reassoc (attr := simp)]
lemma roosObj_map_π (b : ℕ → ℕ) (X : ℕᵒᵖ ⥤ A) {k k' : ℕᵒᵖ} (f : k ⟶ k') (n : ℕ)
    (g : k' ⟶ op (b n)) :
    (roosObj b X).map f ≫ Pi.π _ n ≫ Pi.π _ g = Pi.π _ n ≫ Pi.π _ (f ≫ g) := by
  simp [roosObj]

/-- The functor `X ↦ ∏ₙ R_{b n}(Xₙ)`. -/
@[simps obj]
noncomputable def roos (b : ℕ → ℕ) : (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ A) where
  obj X := roosObj b X
  map φ :=
    { app k := Pi.lift fun n ↦ Pi.π _ n ≫ Pi.lift fun g ↦ Pi.π _ g ≫ φ.app (op n)
      naturality k k' f := roosObj_hom_ext fun n g ↦ by simp }
  map_id X := by ext k; exact roosObj_hom_ext fun n g ↦ by simp
  map_comp φ φ' := by ext k; exact roosObj_hom_ext fun n g ↦ by simp

@[reassoc (attr := simp)]
lemma roos_obj_map_π (b : ℕ → ℕ) (X : ℕᵒᵖ ⥤ A) {k k' : ℕᵒᵖ} (f : k ⟶ k') (n : ℕ)
    (g : k' ⟶ op (b n)) :
    ((roos b).obj X).map f ≫ Pi.π _ n ≫ Pi.π _ g = Pi.π _ n ≫ Pi.π _ (f ≫ g) :=
  roosObj_map_π b X f n g

@[reassoc (attr := simp)]
lemma roos_map_app_π (b : ℕ → ℕ) {X X' : ℕᵒᵖ ⥤ A} (φ : X ⟶ X') (k : ℕᵒᵖ) (n : ℕ)
    (g : k ⟶ op (b n)) :
    ((roos b).map φ).app k ≫ Pi.π _ n ≫ Pi.π _ g = Pi.π _ n ≫ Pi.π _ g ≫ φ.app (op n) := by
  simp [roos]

/-- The projection `∏ₙ R_{b n}(Xₙ) ⟶ R_{b n}(Xₙ)`. -/
@[simps]
noncomputable def roosπ (b : ℕ → ℕ) (n : ℕ) : roos (A := A) b ⟶
    (evaluation ℕᵒᵖ A).obj (op n) ⋙ R (b n) where
  app X :=
    { app k := Pi.π _ n
      naturality _ _ _ := Pi.hom_ext _ _ fun g ↦ by simp }
  naturality _ _ _ := by ext; exact Pi.hom_ext _ _ fun g ↦ by simp

/-- The inclusion `X ⟶ ∏ₙ Rₙ(Xₙ)`, whose components are the units of the adjunctions
`evₙ ⊣ Rₙ`. -/
@[simps]
noncomputable def roosι : 𝟭 (ℕᵒᵖ ⥤ A) ⟶ roos (fun n ↦ n) where
  app X :=
    { app k := Pi.lift fun n ↦ Pi.lift fun g ↦ X.map g
      naturality _ _ _ := roosObj_hom_ext fun n g ↦ by simp }
  naturality _ _ _ := by ext; exact roosObj_hom_ext fun n g ↦ by simp

/-- The map `d : ∏ₙ Rₙ(Xₙ) ⟶ ∏ₙ Rₙ₊₁(Xₙ)`, `(yₙ) ↦ (yₙ - fₙ(yₙ₊₁))ₙ`. -/
@[simps]
noncomputable def roosd [Preadditive A] : roos (A := A) (fun n ↦ n) ⟶ roos (· + 1) where
  app X :=
    { app k := Pi.lift fun n ↦ Pi.lift fun g ↦
        Pi.π _ n ≫ Pi.π _ (g ≫ (homOfLE n.le_succ).op) -
          Pi.π _ (n + 1) ≫ Pi.π (fun _ : k ⟶ op (n + 1) ↦ X.obj (op (n + 1))) g ≫
            X.map (homOfLE n.le_succ).op
      naturality k k' f := roosObj_hom_ext fun n g ↦ by
        simp [Preadditive.comp_sub] }
  naturality X X' φ := by
    ext; exact roosObj_hom_ext fun n g ↦ by simp [Preadditive.comp_sub]


@[reassoc (attr := simp)]
lemma roosι_roosd [Preadditive A] (X : ℕᵒᵖ ⥤ A) : roosι.app X ≫ roosd.app X = 0 := by
  ext k
  refine roosObj_hom_ext fun n g ↦ ?_
  simp only [NatTrans.comp_app, Functor.id_obj, roosι_app_app, roosd_app_app,
    Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Preadditive.comp_sub,
    limit.lift_π_assoc, Discrete.functor_obj_eq_as, NatTrans.app_zero, zero_comp, ← X.map_comp]
  exact sub_self _

/-- The short complex of towers `X ⟶ ∏ₙ Rₙ(Xₙ) ⟶ ∏ₙ Rₙ₊₁(Xₙ)`. -/
@[simps]
noncomputable def roosShortComplex [Preadditive A] (X : ℕᵒᵖ ⥤ A) : ShortComplex (ℕᵒᵖ ⥤ A) where
  f := roosι.app X
  g := roosd.app X
  zero := roosι_roosd X

section Splitting

variable [Preadditive A] (X : ℕᵒᵖ ⥤ A) (k : ℕ)

/-- The component `yₙ` of `y ∈ (∏ₙ Rₙ(Xₙ))ₖ`, for `n ≤ k`. -/
noncomputable abbrev yproj (n : ℕ) (h : n ≤ k) :
    (roosObj (fun n ↦ n) X).obj (op k) ⟶ X.obj (op n) :=
  Pi.π _ n ≫ Pi.π (fun _ : op k ⟶ op n ↦ X.obj (op n)) (homOfLE h).op

/-- The component `zₙ` of `z ∈ (∏ₙ Rₙ₊₁(Xₙ))ₖ`, for `n + 1 ≤ k`. -/
noncomputable abbrev zproj (n : ℕ) (h : n + 1 ≤ k) :
    (roosObj (· + 1) X).obj (op k) ⟶ X.obj (op n) :=
  Pi.π _ n ≫ Pi.π (fun _ : op k ⟶ op (n + 1) ↦ X.obj (op n)) (homOfLE h).op

omit [Preadditive A] in
lemma pi_π_eq {k n : ℕ} {Y : A} (g g' : op k ⟶ op n) :
    Pi.π (fun _ : op k ⟶ op n ↦ Y) g = Pi.π (fun _ : op k ⟶ op n ↦ Y) g' := by
  rw [Subsingleton.elim g g']

/-- The components `σₙ = Σ_{n ≤ j < n + m} f_{n,j}(z_j) : (∏ₙ Rₙ₊₁(Xₙ))ₖ ⟶ Xₙ` (where
`n + m = k`) of the section of `d` at level `k`. -/
noncomputable def sectionAux : (m n : ℕ) → n + m = k →
    ((roosObj (· + 1) X).obj (op k) ⟶ X.obj (op n))
  | 0, _, _ => 0
  | m + 1, n, h => zproj X k n (by omega) +
      sectionAux m (n + 1) (by omega) ≫ X.map (homOfLE n.le_succ).op

lemma sectionAux_congr {m m' n : ℕ} (h : n + m = k) (hm : m = m') :
    sectionAux X k m n h = sectionAux X k m' n (hm ▸ h) := by
  subst hm; rfl

lemma roosd_sectionAux (m n : ℕ) (h : n + m = k) :
    (roosd.app X).app (op k) ≫ sectionAux X k m n h =
      yproj X k n (by omega) - yproj X k k le_rfl ≫ X.map (homOfLE (show n ≤ k by omega)).op := by
  induction m generalizing n with
  | zero =>
    obtain rfl : n = k := by omega
    simp [sectionAux]
  | succ m ih =>
    simp only [sectionAux, Preadditive.comp_add, ← Category.assoc _ _ (X.map _),
      ih (n + 1) (by omega)]
    simp only [roosd_app_app, Category.assoc, limit.lift_π_assoc, Discrete.functor_obj_eq_as,
      Fan.mk_pt, Fan.mk_π_app, limit.lift_π, Preadditive.sub_comp, ← X.map_comp]
    rw [pi_π_eq _ (homOfLE (show n ≤ k by omega)).op]
    abel_nf
    rfl

/-- The levelwise splitting of the Roos short exact sequence. -/
noncomputable def roosSplitting :
    ((roosShortComplex X).map ((evaluation ℕᵒᵖ A).obj (op k))).Splitting where
  r := yproj X k k le_rfl
  s := Pi.lift fun n ↦ Pi.lift fun g ↦ sectionAux X k (k - n) n (by
    have := leOfHom g.unop; dsimp at this; omega)
  f_r := by
    simp only [ShortComplex.map_f, roosShortComplex_f, evaluation_obj_map, roosι_app_app,
      limit.lift_π_assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Discrete.functor_obj_eq_as]
    exact (X.map_id _).trans rfl
  s_g := by
    refine roosObj_hom_ext fun n g ↦ ?_
    have hn : n + 1 ≤ k := leOfHom g.unop
    obtain rfl : g = (homOfLE hn).op := Subsingleton.elim _ _
    simp only [ShortComplex.map_g, roosShortComplex_g, evaluation_obj_map,
      roosd_app_app, Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Category.id_comp,
      Preadditive.comp_sub, limit.lift_π_assoc, Discrete.functor_obj_eq_as]
    rw [sectionAux_congr X k _ (show k - n = (k - (n + 1)) + 1 by omega)]
    simp only [sectionAux, add_sub_cancel_right]
  id := by
    refine roosObj_hom_ext fun n g ↦ ?_
    have hn : n ≤ k := leOfHom g.unop
    obtain rfl : g = (homOfLE hn).op := Subsingleton.elim _ _
    simp only [Functor.id_obj, ShortComplex.map_f, roosShortComplex_f, evaluation_obj_map,
      roosι_app_app, ShortComplex.map_g, roosShortComplex_g, Preadditive.add_comp,
      Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Category.id_comp, limit.lift_π_assoc,
      Discrete.functor_obj_eq_as]
    rw [← Category.assoc, roosd_sectionAux]
    abel

end Splitting

end

section Abelian

variable [Abelian A] [HasCountableProducts A]

lemma roosShortComplex_shortExact (X : ℕᵒᵖ ⥤ A) : (roosShortComplex X).ShortExact :=
  ShortComplex.shortExact_of_evaluation fun k ↦ (roosSplitting X k.unop).shortExact

instance (b : ℕ → ℕ) : (roos (A := A) b).Additive where
  map_add := by
    intros
    ext k
    exact roosObj_hom_ext fun n g ↦ by simp

instance (a : ℕ) : (evaluationLeftAdjoint A (op a)).Additive where
  map_add := by
    intros
    ext t
    exact Sigma.hom_ext _ _ fun g ↦ by simp

instance (b : ℕ) : (evaluationRightAdjoint A (op b)).Additive where
  map_add := by
    intros
    ext t
    exact Pi.hom_ext _ _ fun g ↦ by simp

/-- The functor `X ↦ R_b(X_a)`, right adjoint to `W ↦ L_a(W_b)`. -/
noncomputable abbrev G (a b : ℕ) : (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ A) :=
  (evaluation ℕᵒᵖ A).obj (op a) ⋙ R b

/-- The adjunction `L_a ∘ ev_b ⊣ R_b ∘ ev_a`. -/
noncomputable def adjunctionG (a b : ℕ) :
    (evaluation ℕᵒᵖ A).obj (op b) ⋙ evaluationLeftAdjoint A (op a) ⊣ G a b :=
  (evaluationAdjunctionLeft A (op b)).comp (evaluationAdjunctionRight A (op a))

omit [HasCountableProducts A] in
/-- The left adjoint `L_a` of evaluation at `a` sends acyclic complexes to acyclic complexes:
`(L_a V)ₜ` is `V` if `t ≤ a` and `0` otherwise. -/
lemma acyclic_evaluationLeftAdjoint (a : ℕ) (V : CochainComplex A ℤ) (hV : V.Acyclic) :
    (((evaluationLeftAdjoint A (op a)).mapHomologicalComplex _).obj V).Acyclic := by
  rw [HomologicalComplex.acyclic_iff_evaluation]
  intro t
  by_cases ht : Nonempty (op a ⟶ t)
  · have : Unique (op a ⟶ t) := { default := ht.some, uniq := fun _ ↦ Subsingleton.elim _ _ }
    let e : (((evaluation ℕᵒᵖ A).obj t).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((evaluationLeftAdjoint A (op a)).mapHomologicalComplex _).obj V) ≅ V :=
      HomologicalComplex.Hom.isoOfComponents
        (fun p ↦ coproductUniqueIso (fun _ : op a ⟶ t ↦ V.X p)) fun p q _ ↦ by
          refine Sigma.hom_ext _ _ fun g ↦ ?_
          simp [coproductUniqueIso, Subsingleton.elim g default]
    exact fun p ↦ (hV p).of_iso e.symm
  · rw [not_nonempty_iff] at ht
    refine fun p ↦ HomologicalComplex.ExactAt.of_isZero ?_
    rw [IsZero.iff_id_eq_zero]
    exact Sigma.hom_ext _ _ fun g ↦ isEmptyElim g

/-- If `I` is a K-injective complex of towers, so is `R_b(I_a)`. -/
lemma isKInjective_G (a b : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((G a b).mapHomologicalComplex _).obj I) :=
  (adjunctionG a b).isKInjective_mapHomologicalComplex (fun W hW ↦ by
    have hW' := (HomologicalComplex.acyclic_iff_evaluation W).1 hW (op b)
    exact acyclic_evaluationLeftAdjoint a _ hW') I
/-- The complex of towers `∏ₙ R_{b n}(Iₙ)`. -/
noncomputable abbrev roosComplex (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ :=
  ((roos b).mapHomologicalComplex _).obj I

/-- The fan exhibiting `∏ₙ R_{b n}(Iₙ)` as the product of the complexes `R_{b n}(Iₙ)`. -/
noncomputable abbrev roosComplexFan (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Fan fun n : ℕ ↦ ((G n (b n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  Fan.mk (roosComplex b I) fun n ↦ (NatTrans.mapHomologicalComplex (roosπ b n) _).app I

@[reassoc (attr := simp)]
lemma roosComplex_X_map_π (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ)
    {k k' : ℕᵒᵖ} (g : k ⟶ k') (n : ℕ) (g' : k' ⟶ op (b n)) :
    ((roosComplex b I).X p).map g ≫ Pi.π _ n ≫ Pi.π _ g' = Pi.π _ n ≫ Pi.π _ (g ≫ g') :=
  roosObj_map_π b (I.X p) g n g'

@[reassoc (attr := simp)]
lemma roosComplex_d_app_π (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p q : ℤ)
    (k : ℕᵒᵖ) (n : ℕ) (g : k ⟶ op (b n)) :
    ((roosComplex b I).d p q).app k ≫ Pi.π _ n ≫ Pi.π _ g =
      Pi.π _ n ≫ Pi.π _ g ≫ (I.d p q).app (op n) :=
  roos_map_app_π b (I.d p q) k n g

@[reassoc (attr := simp)]
lemma GComplex_X_map_π (a b : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ)
    {k k' : ℕᵒᵖ} (g : k ⟶ k') (g' : k' ⟶ op b) :
    ((((G a b).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).X p).map g ≫ Pi.π _ g' =
      Pi.π (fun _ : k ⟶ op b ↦ (I.X p).obj (op a)) (g ≫ g') :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma GComplex_d_app_π (a b : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p q : ℤ)
    (k : ℕᵒᵖ) (g : k ⟶ op b) :
    ((((G a b).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).d p q).app k ≫ Pi.π _ g =
      Pi.π (fun _ : k ⟶ op b ↦ (I.X p).obj (op a)) g ≫ (I.d p q).app (op a) :=
  limit.lift_π _ _

/-- The morphism into `∏ₙ R_{b n}(Iₙ)` with given components. -/
noncomputable def roosComplexLift (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    {W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (φ : ∀ n, W ⟶ ((G n (b n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :
    W ⟶ roosComplex b I where
  f p :=
    { app k := Pi.lift fun n ↦ ((φ n).f p).app k
      naturality k k' g := roosObj_hom_ext fun n g' ↦ by
        have := ((φ n).f p).naturality g =≫ Pi.π _ g'
        simp only [Category.assoc, GComplex_X_map_π] at this
        simp only [Category.assoc, roosComplex_X_map_π, limit.lift_π_assoc, Fan.mk_pt,
          Fan.mk_π_app, Discrete.functor_obj_eq_as]
        exact this }
  comm' p q _ := by
    ext k
    refine roosObj_hom_ext fun n g ↦ ?_
    have := NatTrans.congr_app ((φ n).comm p q) k =≫ Pi.π _ g
    simp only [NatTrans.comp_app, Category.assoc, GComplex_d_app_π] at this
    simp only [NatTrans.comp_app, Category.assoc, roosComplex_d_app_π, limit.lift_π_assoc,
      Fan.mk_pt, Fan.mk_π_app, Discrete.functor_obj_eq_as]
    exact this

@[reassoc (attr := simp)]
lemma roosComplexLift_f_app_π (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    {W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (φ : ∀ n, W ⟶ ((G n (b n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (p : ℤ) (k : ℕᵒᵖ) (n : ℕ) (g : k ⟶ op (b n)) :
    ((roosComplexLift b I φ).f p).app k ≫ Pi.π _ n ≫ Pi.π _ g = ((φ n).f p).app k ≫ Pi.π _ g := by
  simp [roosComplexLift]

/-- `∏ₙ R_{b n}(Iₙ)` is the product of the complexes `R_{b n}(Iₙ)`. -/
noncomputable def isLimitRoosComplexFan (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (roosComplexFan b I) :=
  Fan.IsLimit.mk _ (fun s ↦ roosComplexLift b I s.proj)
    (fun s n ↦ by
      ext p k
      exact Pi.hom_ext _ _ fun g ↦ by simp)
    (fun s m hm ↦ by
      ext p k
      refine roosObj_hom_ext fun n g ↦ ?_
      have := NatTrans.congr_app (HomologicalComplex.congr_hom (hm n) p) k =≫ Pi.π _ g
      rw [roosComplexLift_f_app_π]
      simpa using this)

/-- If `I` is a K-injective complex of towers, so is `∏ₙ R_{b n}(Iₙ)`. -/
instance isKInjective_roosComplex (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [I.IsKInjective] : (roosComplex b I).IsKInjective := by
  have := fun n ↦ isKInjective_G n (b n) I
  exact CochainComplex.isKInjective_of_isLimitFan (isLimitRoosComplexFan b I)

/-- The degreewise short exact sequence of complexes of towers
`0 ⟶ I ⟶ ∏ₙ Rₙ(Iₙ) ⟶ ∏ₙ Rₙ₊₁(Iₙ) ⟶ 0`. -/
@[simps]
noncomputable def roosComplexShortComplex (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ShortComplex (CochainComplex (ℕᵒᵖ ⥤ A) ℤ) where
  X₁ := I
  X₂ := roosComplex (fun n ↦ n) I
  X₃ := roosComplex (· + 1) I
  f := { f p := roosι.app (I.X p), comm' p q _ := (roosι.naturality (I.d p q)).symm }
  g := { f p := roosd.app (I.X p), comm' p q _ := (roosd.naturality (I.d p q)).symm }
  zero := by ext p : 1; exact roosι_roosd (I.X p)

lemma roosComplexShortComplex_shortExact (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (roosComplexShortComplex I).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p ↦
    roosShortComplex_shortExact (I.X p)

end Abelian
section Limits

variable [Abelian A] [HasCountableProducts A]

instance : HasLimitsOfShape ℕᵒᵖ A := ⟨fun F ↦ hasLimit_of_equalizer_and_product F⟩

instance : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive where
  map_add := by
    intros
    exact limit.hom_ext fun _ ↦ by simp

/-- The cone `a ⟶ R_b(a)` with all components the diagonal. -/
@[simps]
noncomputable def diagonalCone (b : ℕ) (a : A) : Cone ((R b).obj a) where
  pt := a
  π :=
    { app t := (Pi.lift fun _ ↦ 𝟙 a : a ⟶ ∏ᶜ fun _ : t ⟶ op b ↦ a)
      naturality _ _ _ := Pi.hom_ext _ _ fun _ ↦ by simp }

/-- The isomorphism `lim R_b(a) ≅ a`, given by the projection to the `b`-th term. -/
@[simps]
noncomputable def limRIso (b : ℕ) (a : A) : lim.obj ((R b).obj a) ≅ a where
  hom := limit.π _ (op b) ≫ Pi.π _ (𝟙 (op b))
  inv := limit.lift _ (diagonalCone b a)
  hom_inv_id := by
    refine limit.hom_ext fun t ↦ Pi.hom_ext _ _ fun g ↦ ?_
    have := limit.w ((R b).obj a) g =≫ Pi.π _ (𝟙 (op b))
    simp only [evaluationRightAdjoint_obj_map, Category.assoc,
      limit.lift_π, Fan.mk_pt, Fan.mk_π_app, Category.comp_id] at this
    simp [← this]

@[reassoc (attr := simp)]
lemma limRIso_hom_naturality (b : ℕ) {a a' : A} (f : a ⟶ a') :
    lim.map ((R b).map f) ≫ (limRIso b a').hom = (limRIso b a).hom ≫ f := by
  simp

end Limits
section LimitComplexes

variable [Abelian A] [HasCountableProducts A]

/-- The termwise isomorphism `lim R_b(I_a) ≅ I_a` of complexes. -/
noncomputable def limGComplexIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a b : ℕ) :
    (lim.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((G a b).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅ I.asFunctor.obj (op a) :=
  HomologicalComplex.Hom.isoOfComponents (fun p ↦ limRIso b ((I.X p).obj (op a)))
    fun p q _ ↦ (limRIso_hom_naturality b ((I.d p q).app (op a))).symm

/-- The fan exhibiting `lim ∏ₙ R_{b n}(Iₙ)` as a product of the complexes `Iₙ`. -/
noncomputable abbrev limRoosFan (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Fan fun n : ℕ ↦ I.asFunctor.obj (op n) :=
  Fan.mk ((lim.mapHomologicalComplex (ComplexShape.up ℤ)).obj (roosComplex b I)) fun n ↦
    (lim.mapHomologicalComplex (ComplexShape.up ℤ)).map ((roosComplexFan b I).proj n) ≫
      (limGComplexIso I n (b n)).hom

/-- `lim ∏ₙ R_{b n}(Iₙ)` is the product of the complexes `Iₙ`. -/
noncomputable def isLimitLimRoosFan (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (limRoosFan b I) :=
  Fan.IsLimit.ofIsos ((isLimitMapConeFanMkEquiv _ _ _)
      (isLimitOfPreserves (lim.mapHomologicalComplex (ComplexShape.up ℤ))
        (isLimitRoosComplexFan b I)))
    (fun n ↦ (limGComplexIso I n (b n)).symm) (Iso.refl _) (fun n ↦ by simp)

/-- The limit cone of a tower of complexes, computed termwise. -/
@[simps]
noncomputable def limCone (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone I.asFunctor where
  pt := (lim.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  π :=
    { app j :=
        { f p := limit.π (I.X p) j
          comm' p q _ := (limMap_π _ _).symm }
      naturality j j' f := by
        ext p
        simp }

/-- The termwise limit cone is a limit cone. -/
noncomputable def isLimitLimCone (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsLimit (limCone I) :=
  HomologicalComplex.isLimitOfEval _ (limCone I) fun p ↦
    (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp))
      (limit.cone (I.X p)) ((HomologicalComplex.eval _ _ p).mapCone (limCone I))
      (Cone.ext (Iso.refl _) fun _ ↦ by simp)) (limit.isLimit _)

lemma limRoosFan_proj_f (b : ℕ → ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) (p : ℤ) :
    ((limRoosFan b I).proj n).f p =
      limit.π ((roos b).obj (I.X p)) (op (b n)) ≫ Pi.π _ n ≫ Pi.π _ (𝟙 (op (b n))) := by
  rw [fan_mk_proj, HomologicalComplex.comp_f]
  exact limMap_π_assoc _ _ _

lemma limCone_π_eq (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (lim.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosComplexShortComplex I).f ≫
      (limRoosFan (fun n ↦ n) I).proj n = (limCone I).π.app (op n) := by
  ext p
  rw [HomologicalComplex.comp_f, limRoosFan_proj_f]
  refine (limMap_π_assoc _ _ _).trans ?_
  simp only [roosComplexShortComplex_f_f, roosι_app_app, limit.lift_π_assoc, Fan.mk_pt,
    Fan.mk_π_app, Discrete.functor_obj_eq_as, limit.lift_π]
  exact (congrArg _ ((I.X p).map_id _)).trans (Category.comp_id _)

lemma limRoosFan_d_eq (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (lim.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosComplexShortComplex I).g ≫
      (limRoosFan (· + 1) I).proj n = (limRoosFan (fun n ↦ n) I).proj n -
        (limRoosFan (fun n ↦ n) I).proj (n + 1) ≫ I.asFunctor.map (homOfLE n.le_succ).op := by
  ext p
  rw [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    limRoosFan_proj_f, limRoosFan_proj_f, limRoosFan_proj_f]
  refine (limMap_π_assoc _ _ _).trans ?_
  simp only [Preadditive.comp_sub, roosComplexShortComplex_g_f, roosd_app_app, limit.lift_π_assoc,
    Fan.mk_pt, Fan.mk_π_app, Discrete.functor_obj_eq_as, limit.lift_π, Category.id_comp]
  congr 1
  · rw [← limit.w ((roos fun n ↦ n).obj (I.X p)) (homOfLE n.le_succ).op, Category.assoc]
    simp
    rfl
  · simp only [Category.assoc]
    rfl

end LimitComplexes

end CategoryTheory.Tower
