/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# Čech complexes of inverse images at a cofiltered limit

Let `X = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes over a
quasi-separated scheme `R`, with affine transition maps, and let `G` be an abelian étale sheaf
on `R`. By the continuity of sections
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`), the sections of the inverse
image of `G` to `X` over the base change of a quasi-compact quasi-separated étale `R`-scheme
are the filtered colimit of the sections of the inverse images of `G` to the stages. Hence the
Čech complex of the pushforward of the inverse image of `G` to `X`, on a finite family of étale
`R`-schemes whose Čech nerve is quasi-compact and quasi-separated, is the filtered colimit of
the corresponding Čech complexes for the stages. In particular it is exact in positive degrees
as soon as all the Čech complexes at the stages are, for instance when the inverse images of
`G` to the stages are injective.

## Main statements

- `AlgebraicGeometry.Etale.unitComparison_comp`: the comparison maps of
  `AlgebraicGeometry.Etale.unitComparison` compose.
- `AlgebraicGeometry.Etale.exactAt_cechComplex_lowerStar_upperStar_of_isLimit`: the exactness of
  Čech complexes at the limit.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Presheaf

namespace AlgebraicGeometry.Etale

section Composition

variable {R T T' T'' : Scheme.{u}} (t : T ⟶ R) (f : T' ⟶ T) (t' : T' ⟶ R) (ht' : t' = f ≫ t)
  (f' : T'' ⟶ T') (t'' : T'' ⟶ R) (ht'' : t'' = f' ≫ t')
  (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- `AlgebraicGeometry.Etale.unitComparison` only depends on the morphism `f` through its
value. -/
lemma unitComparison_congr {f₁ f₂ : T' ⟶ T} (h : f₁ = f₂) (ht' : t' = f₁ ≫ t) :
    unitComparison f₁ t t' ht' G = unitComparison f₂ t t' (h ▸ ht') G := by
  subst h
  rfl

/-- **The comparison maps compose**: for `T'' ⟶ T' ⟶ T ⟶ R`, the comparison map
`t_* t^* G ⟶ t'_* t'^* G` followed by `t'_* t'^* G ⟶ t''_* t''^* G` is the comparison map
`t_* t^* G ⟶ t''_* t''^* G`. -/
lemma unitComparison_comp :
    unitComparison f t t' ht' G ≫ unitComparison f' t' t'' ht'' G =
      unitComparison (f' ≫ f) t t'' (by rw [ht'', ht', Category.assoc]) G := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ AddCommGrpCat.ext fun s ↦ ?_))
  obtain ⟨W⟩ := W
  change (unitComparison f' t' t'' ht'' G).hom.app (op W)
    ((unitComparison f t t' ht' G).hom.app (op W) s) = _
  rw [unitComparison_hom_app_eq, unitComparison_hom_app_eq, unitComparison_hom_app_eq]
  refine (restrictAlong_restrictAlong t G f t' ht' f' t'' ht'' _ _ _ _ s).trans ?_
  exact congrArg (fun (φ : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ t).obj W)) ⟶
        ((t'')^*[AddCommGrpCat.{u + 1}].obj G).obj.obj
          (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ t'').obj W))) ↦ φ s)
    (restrictAlong_congr t G (f' ≫ f) t'' _ _ (by apply pullback.hom_ext <;> simp))

/-- `AlgebraicGeometry.Etale.unitComparison_comp`, applied to a section. -/
lemma unitComparison_comp_apply {W : R.Etale}
    (s : ((t)_*[AddCommGrpCat.{u + 1}].obj ((t)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj
      (op W)) :
    (unitComparison f' t' t'' ht'' G).hom.app (op W)
        ((unitComparison f t t' ht' G).hom.app (op W) s) =
      (unitComparison (f' ≫ f) t t'' (by rw [ht'', ht', Category.assoc]) G).hom.app (op W) s := by
  rw [← unitComparison_comp t f t' ht' f' t'' ht'' G]
  rfl

end Composition

section Limit

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u}) {R : Scheme.{u}}
  (π : D ⟶ (Functor.const J).obj R) (c : Cone D) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

omit [IsCofiltered J] in
/-- The structure morphisms of the stages to `R` are compatible with the transition maps. -/
lemma natTrans_app_eq_map_comp_app {D : J ⥤ Scheme.{u}} (π : D ⟶ (Functor.const J).obj R)
    {k k' : J} (g : k' ⟶ k) : π.app k' = D.map g ≫ π.app k := by
  simp

omit [IsCofiltered J] in
/-- In a cofiltered category, finitely many morphisms with common target are dominated by a
single one. -/
lemma exists_comp_eq_of_finite_aux {C : Type*} [Category* C] [IsCofiltered C]
    {ι : Type*} [Finite ι] {k : C} (k₁ : ι → C) (f₁ : ∀ i, k₁ i ⟶ k) :
    ∃ (K : C) (h : K ⟶ k) (g : ∀ i, K ⟶ k₁ i), ∀ i, g i ≫ f₁ i = h := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists
    (Finset.univ.image (fun i ↦ Over.mk (f₁ i)))
  have hg (i : ι) : Nonempty (S ⟶ Over.mk (f₁ i)) := hS (Finset.mem_image_of_mem _ (by simp))
  exact ⟨S.left, S.hom, fun i ↦ (hg i).some.left, fun i ↦ Over.w (hg i).some⟩

omit [IsCofiltered J] in
/-- The transition map from the stage `j` to the stage `k`, followed by the comparison map from
`k` to the limit, is the comparison map from `j` to the limit. -/
lemma unitComparison_map_comp_apply {j k : J} (g : k ⟶ j) {W : R.Etale}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)) :
    (unitComparison (c.π.app k) (π.app k) P (hP k) G).hom.app (op W)
        ((unitComparison (D.map g) (π.app j) (π.app k) (natTrans_app_eq_map_comp_app π g) G).hom.app
          (op W) s) =
      (unitComparison (c.π.app j) (π.app j) P (hP j) G).hom.app (op W) s := by
  rw [unitComparison_comp_apply, unitComparison_congr _ _ _ (c.w g)]

omit [IsCofiltered J] in
/-- The transition maps between the stages compose. -/
lemma unitComparison_map_map_apply {j k l : J} (g : k ⟶ j) (h : l ⟶ k) {W : R.Etale}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj.obj (op W)) :
    (unitComparison (D.map h) (π.app k) (π.app l) (natTrans_app_eq_map_comp_app π h) G).hom.app (op W)
        ((unitComparison (D.map g) (π.app j) (π.app k) (natTrans_app_eq_map_comp_app π g) G).hom.app
          (op W) s) =
      (unitComparison (D.map (h ≫ g)) (π.app j) (π.app l) (natTrans_app_eq_map_comp_app π _) G).hom.app
        (op W) s := by
  rw [unitComparison_comp_apply, unitComparison_congr _ _ _ (D.map_comp h g).symm]

set_option maxRecDepth 8000 in
include hP in
/-- **Čech complexes of inverse images at a cofiltered limit.** Let `X = lim Dⱼ` be a cofiltered
limit of quasi-compact quasi-separated schemes over a quasi-separated scheme `R`, with affine
transition maps, and let `G` be an abelian étale sheaf on `R` such that the Čech complexes of
the pushforwards of the inverse images of `G` to all the stages are exact in positive degrees.
Then the Čech complex of the pushforward of the inverse image of `G` to `X`, on a finite family
of étale `R`-schemes whose Čech nerve is quasi-compact and quasi-separated, is exact in positive
degrees: a Čech cocycle comes from a cochain at some stage, whose differential vanishes at a
later stage, where it is a coboundary. -/
theorem exactAt_cechComplex_lowerStar_upperStar_of_isLimit [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)] [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]
    [QuasiSeparatedSpace R] (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ (j : J) {V : R.Etale} {n : ℕ} (U : Fin n → Over V) (q : ℕ),
      ((cechComplex U).obj ((π.app j)_*[AddCommGrpCat.{u + 1}].obj
        ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)).obj).ExactAt (q + 1))
    {V : R.Etale} {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n), CompactSpace (cechNerveObj U y).left.left ∧
      QuasiSeparatedSpace (cechNerveObj U y).left.left)
    (q : ℕ) :
    ((cechComplex U).obj ((P)_*[AddCommGrpCat.{u + 1}].obj
      ((P)^*[AddCommGrpCat.{u + 1}].obj G)).obj).ExactAt (q + 1) := by
  classical
  rw [exactAt_cechComplex_iff]
  intro z hz
  -- the components of `z` come from stages
  choose j w hw using fun y : Fin (q + 2) → Fin n ↦
    have := (hU (q + 1) y).1
    have := (hU (q + 1) y).2
    (unitComparison_app_isColimit_of_isLimit D π c P hP hc G (cechNerveObj U y).left).1 (z y)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  have hk' (y : Fin (q + 2) → Fin n) : Nonempty (k ⟶ j y) :=
    hk (Finset.mem_image_of_mem _ (Finset.mem_univ y))
  -- a cochain at the common stage `k`
  obtain ⟨w', hw'def⟩ : ∃ w' : ((cechComplex U).obj ((π.app k)_*[AddCommGrpCat.{u + 1}].obj
      ((π.app k)^*[AddCommGrpCat.{u + 1}].obj G)).obj).X (q + 1), ∀ y, w' y =
        (unitComparison (D.map (hk' y).some) (π.app (j y)) (π.app k)
          (natTrans_app_eq_map_comp_app π _) G).hom.app _ (w y) :=
    ⟨fun y ↦ (unitComparison (D.map (hk' y).some) (π.app (j y)) (π.app k)
      (natTrans_app_eq_map_comp_app π _) G).hom.app _ (w y), fun _ ↦ rfl⟩
  have hw' : ((cechComplex U).map (unitComparison (c.π.app k) (π.app k) P (hP k) G).hom).f
      (q + 1) w' = z := by
    funext y
    rw [cechComplex_map_f_apply, hw'def]
    exact (unitComparison_map_comp_apply D π c P hP (W := (cechNerveObj U y).left)
      (hk' y).some G (w y)).trans (hw y)
  have hdw (y : Fin (q + 3) → Fin n) :
      (unitComparison (c.π.app k) (π.app k) P (hP k) G).hom.app _
        ((((cechComplex U).obj _).d (q + 1) (q + 2) w') y) = 0 := by
    have := congr_fun (cechComplex_map_f_d_apply U
      (unitComparison (c.π.app k) (π.app k) P (hP k) G).hom (q + 1) w') y
    rw [hw', hz] at this
    exact this
  -- the components of its differential vanish at later stages
  choose m φ hφ using fun y : Fin (q + 3) → Fin n ↦
    have := (hU (q + 2) y).1
    have := (hU (q + 2) y).2
    (unitComparison_app_isColimit_of_isLimit D π c P hP hc G (cechNerveObj U y).left).2 k _
      (hdw y)
  obtain ⟨l, ψ, g, hg⟩ := exists_comp_eq_of_finite_aux m φ
  let w'' := ((cechComplex U).map (unitComparison (D.map ψ) (π.app k) (π.app l)
    (natTrans_app_eq_map_comp_app π ψ) G).hom).f (q + 1) w'
  have hdw'' : ((cechComplex U).obj _).d (q + 1) (q + 2) w'' = 0 := by
    rw [← cechComplex_map_f_d_apply]
    funext y
    rw [cechComplex_map_f_apply, ← hg y, ← unitComparison_map_map_apply D π (φ y) (g y) G,
      hφ y, map_zero]
    rfl
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1 (hG l U q) _ hdw''
  refine ⟨((cechComplex U).map (unitComparison (c.π.app l) (π.app l) P (hP l) G).hom).f q b, ?_⟩
  rw [← cechComplex_map_f_d_apply, hb, ← hw']
  funext y
  rw [cechComplex_map_f_apply, cechComplex_map_f_apply]
  simp only [w'']
  rw [cechComplex_map_f_apply]
  exact unitComparison_map_comp_apply D π c P hP (W := (cechNerveObj U y).left) ψ G (w' y)

end Limit

end AlgebraicGeometry.Etale
