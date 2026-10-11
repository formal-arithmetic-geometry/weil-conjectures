/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.CategoryTheory.Sites.CechComplexModule
public import WeilConjectures.CategoryTheory.Sites.CechCriterionExt

/-!
# Étale cohomology with coefficients in modules commutes with filtered colimits

This is the version for sheaves of `Λ`-modules of
`AlgebraicGeometry.Scheme.H_map_bijective_of_isColimit_of_isFiltered`. Let `X` be a
quasi-compact quasi-separated scheme, `D` a filtered diagram of étale sheaves of `Λ`-modules on
`X` with colimit `c`, and `G` a sheaf of `Λ`-modules corepresenting global sections (for
instance the free sheaf `Λ_X`). Then `Extᵠ(G, c.pt)` is the colimit of the `Extᵠ(G, D_j)`.

The proof is the same as in the abelian case: sections over qcqs étale `X`-schemes commute with
filtered colimits, so a filtered colimit of injective sheaves of modules has exact Čech
complexes on finite families of qcqs étale `X`-schemes (the Čech complexes of an injective sheaf
of modules being exact by `CategoryTheory.Presheaf.exactAt_cechComplex_forget₂_of_injective`),
hence no higher `Ext` out of `G` by the Čech criterion
`CategoryTheory.Sheaf.subsingleton_ext_succ_of_exactAt_cechComplex`; and one concludes by
dimension shifting, `CategoryTheory.Abelian.Ext.commutesWithColimit_of_isFiltered`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_app_eq_of_isColimit_moduleCat`,
  `AlgebraicGeometry.Scheme.exists_map_app_eq_zero_of_isColimit_moduleCat`: sections over qcqs
  étale `X`-schemes commute with filtered colimits.
- `AlgebraicGeometry.Scheme.subsingleton_ext_succ_of_isColimit_of_injective_moduleCat`: a
  filtered colimit of injective sheaves of modules has no higher `Ext` out of `G`.
- `AlgebraicGeometry.Scheme.commutesWithColimit_of_isFiltered_moduleCat`: `Extᵠ(G, -)`
  commutes with filtered colimits.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [Ring Λ]
variable {X : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
  {D : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone D}

section Sections

/-- A jointly surjective family of morphisms of étale `X`-schemes is a covering family for
every étale sheaf of `Λ`-modules. -/
lemma isSheafFor_ofArrows_moduleCat (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {W : X.Etale} {κ : Type*} {U : κ → X.Etale} (g : ∀ a, U a ⟶ W)
    (hg : ⋃ a, Set.range (g a).left = Set.univ) :
    Presieve.IsSheafFor (F.obj ⋙ CategoryTheory.forget _) (Presieve.ofArrows U g) := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ F.obj
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) F.property)
  rw [Presieve.isSheafFor_iff_generate]
  exact this _ ((ofArrows_mem_smallEtaleTopology_iff g).2 hg)


omit [IsFiltered J] in
/-- The legs of a cocone of sheaves of `Λ`-modules are compatible with the transition maps, on
sections. -/
lemma cocone_ι_app_map_apply_moduleCat (c : Cocone D) {i i' : J} (f : i ⟶ i') (V : X.Etaleᵒᵖ)
    (v : (D.obj i).obj.obj V) :
    (c.ι.app i').hom.app V ((D.map f).hom.app V v) = (c.ι.app i).hom.app V v := by
  rw [← c.w f]
  rfl

omit [IsFiltered J] in
/-- The transition maps of a diagram of sheaves of `Λ`-modules are functorial, on sections. -/
lemma map_comp_hom_app_apply_moduleCat (D : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {i i' i'' : J} (f : i ⟶ i') (g : i' ⟶ i'') (V : X.Etaleᵒᵖ) (v : (D.obj i).obj.obj V) :
    (D.map (f ≫ g)).hom.app V v = (D.map g).hom.app V ((D.map f).hom.app V v) := by
  rw [D.map_comp]
  rfl

variable (D) in
/-- Sections of the objectwise colimit of the presheaves underlying a filtered diagram of
sheaves of `Λ`-modules come from some stage. -/
lemma exists_colimit_ι_app_eq_moduleCat (V : X.Etaleᵒᵖ)
    (t : (colimit (D ⋙ sheafToPresheaf _ _)).obj V) :
    ∃ (j : J) (x : (D.obj j).obj.obj V),
      (colimit.ι (D ⋙ sheafToPresheaf _ _) j).app V x = t := by
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
  exact Concrete.isColimit_exists_rep _
    (isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj V) (colimit.isColimit _)) t

variable (D) in
/-- A section of a stage of a filtered diagram of sheaves of `Λ`-modules which vanishes in the
objectwise colimit of the underlying presheaves vanishes at a later stage. -/
lemma exists_map_app_eq_zero_of_colimit_ι_app_eq_zero_moduleCat (V : X.Etaleᵒᵖ) {j : J}
    (x : (D.obj j).obj.obj V) (hx : (colimit.ι (D ⋙ sheafToPresheaf _ _) j).app V x = 0) :
    ∃ (k : J) (φ : j ⟶ k), (D.map φ).hom.app V x = 0 := by
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
  obtain ⟨k, φ, ψ, h⟩ := Concrete.isColimit_exists_of_rep_eq _
    (isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj V)
      (colimit.isColimit (D ⋙ sheafToPresheaf _ _))) x 0 (by erw [hx, map_zero])
  exact ⟨k, φ, h.trans (map_zero _)⟩

/-- The two composites of an isomorphism of sheaves of `Λ`-modules and its inverse, on sections. -/
lemma _root_.CategoryTheory.Sheaf.iso_hom_app_inv_app_apply_moduleCat {C : Type*} [Category C]
    {K : GrothendieckTopology C} {F G : Sheaf K (ModuleCat.{u + 1} Λ)} (e : F ≅ G) (V : Cᵒᵖ)
    (s : G.obj.obj V) : e.hom.hom.app V (e.inv.hom.app V s) = s := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
  rfl

omit [IsFiltered J] in
/-- The comparison of a colimit cocone of sheaves of `Λ`-modules with the sheafification of the
objectwise colimit of the underlying presheaves. -/
lemma sheafifyCocone_ι_app_comp_coconePointUniqueUpToIso_moduleCat (hc : IsColimit c) (j : J) :
    ((Sheaf.sheafifyCocone (colimit.cocone (D ⋙ sheafToPresheaf _ _))).ι.app j).hom ≫
      ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso
        hc).hom.hom = (c.ι.app j).hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, IsColimit.comp_coconePointUniqueUpToIso_hom]

omit [IsFiltered J] in
/-- The comparison of a colimit cocone of sheaves of `Λ`-modules with the sheafification of the
objectwise colimit of the underlying presheaves, in the other direction. -/
lemma sheafifyCocone_ι_app_eq_moduleCat (hc : IsColimit c) (j : J) :
    ((Sheaf.sheafifyCocone (colimit.cocone (D ⋙ sheafToPresheaf _ _))).ι.app j).hom =
      (c.ι.app j).hom ≫
        ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso
        hc).inv.hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, IsColimit.comp_coconePointUniqueUpToIso_inv]

/-- **Sections of a filtered colimit come locally from a stage.** -/
lemma exists_mem_forall_exists_of_isColimit_moduleCat (hc : IsColimit c) {W : X.Etale}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (j : J) (x : (D.obj j).obj.obj (op V)),
        (c.ι.app j).hom.app (op V) x = c.pt.obj.map f.op s := by
  let e := (Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso hc
  refine ⟨_, Presheaf.imageSieve_mem X.smallEtaleTopology
    (toSheafify X.smallEtaleTopology (colimit (D ⋙ sheafToPresheaf _ _)))
    (e.inv.hom.app (op W) s), fun V f ⟨t, ht⟩ ↦ ?_⟩
  obtain ⟨j, x, rfl⟩ := exists_colimit_ι_app_eq_moduleCat D (op V) t
  refine ⟨j, x, ?_⟩
  have h₁ := Sheaf.sheafifyCocone_ι_app_val (colimit.cocone (D ⋙ sheafToPresheaf _ _)) j
  simp only [colimit.cocone_ι, colimit.cocone_x] at h₁
  have h₂ := congrArg (fun φ ↦ φ.app (op V) x)
    ((sheafifyCocone_ι_app_comp_coconePointUniqueUpToIso_moduleCat hc j).symm.trans
      (congrArg (· ≫ e.hom.hom) h₁))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₂
  refine h₂.trans ?_
  erw [ht, NatTrans.naturality_apply e.hom.hom f.op]
  congr 1
  exact Sheaf.iso_hom_app_inv_app_apply_moduleCat e _ s

/-- **A section vanishing in a filtered colimit vanishes locally at a later stage.** -/
lemma exists_mem_forall_exists_eq_zero_of_isColimit_moduleCat (hc : IsColimit c) {W : X.Etale} {j : J}
    (x : (D.obj j).obj.obj (op W)) (hx : (c.ι.app j).hom.app (op W) x = 0) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (k : J) (φ : j ⟶ k), (D.map φ).hom.app (op V) ((D.obj j).obj.map f.op x) = 0 := by
  have h₁ := Sheaf.sheafifyCocone_ι_app_val (colimit.cocone (D ⋙ sheafToPresheaf _ _)) j
  simp only [colimit.cocone_ι, colimit.cocone_x] at h₁
  have h₂ := congrArg (fun φ ↦ φ.app (op W) x) (h₁.symm.trans (sheafifyCocone_ι_app_eq_moduleCat hc j))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₂
  have h : (toSheafify X.smallEtaleTopology (colimit (D ⋙ sheafToPresheaf _ _))).app (op W)
      ((colimit.ι (D ⋙ sheafToPresheaf _ _) j).app (op W) x) =
      (toSheafify X.smallEtaleTopology (colimit (D ⋙ sheafToPresheaf _ _))).app (op W) 0 := by
    refine h₂.trans ?_
    rw [hx, map_zero, map_zero]
  refine ⟨_, Presheaf.equalizerSieve_mem X.smallEtaleTopology
    (toSheafify X.smallEtaleTopology (colimit (D ⋙ sheafToPresheaf _ _))) _ _ h,
    fun V f hf ↦ ?_⟩
  change (colimit (D ⋙ sheafToPresheaf _ _)).map f.op _ =
    (colimit (D ⋙ sheafToPresheaf _ _)).map f.op 0 at hf
  rw [map_zero] at hf
  exact exists_map_app_eq_zero_of_colimit_ι_app_eq_zero_moduleCat D (op V) _
    ((NatTrans.naturality_apply (colimit.ι (D ⋙ sheafToPresheaf _ _) j) f.op x).trans hf)

/-- **Sections of a filtered colimit over a quasi-compact étale `X`-scheme, injectivity.** Let
`c` be a colimit of a filtered diagram `D` of étale sheaves of `Λ`-modules on `X`, and `W` an étale
`X`-scheme with quasi-compact underlying space. A section of `D_j` over `W` which vanishes in
`c.pt` vanishes in some `D_k`, `j ⟶ k`. -/
lemma exists_map_app_eq_zero_of_isColimit_moduleCat (hc : IsColimit c) {W : X.Etale}
    [CompactSpace W.left] {j : J} (x : (D.obj j).obj.obj (op W))
    (hx : (c.ι.app j).hom.app (op W) x = 0) :
    ∃ (k : J) (φ : j ⟶ k), (D.map φ).hom.app (op W) x = 0 := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_eq_zero_of_isColimit_moduleCat hc x hx
  obtain ⟨n, U, g, hRg, -, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
  choose k φ hφ using fun a ↦ hloc (g a) (hRg a)
  obtain ⟨m, ψ, h, hh⟩ := IsFiltered.exists_forall_comp_eq k φ
  refine ⟨m, ψ, (isSheafFor_ofArrows_moduleCat (D.obj m) g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨a⟩
  change (D.obj m).obj.map _ _ = (D.obj m).obj.map _ 0
  rw [map_zero, ← NatTrans.naturality_apply, ← hh a, map_comp_hom_app_apply_moduleCat, hφ a, map_zero]

/-- **Sections of a filtered colimit over a qcqs étale `X`-scheme, surjectivity.** Let `c` be a
colimit of a filtered diagram `D` of étale sheaves of `Λ`-modules on `X`, and `W` an étale `X`-scheme
with quasi-compact quasi-separated underlying scheme. Every section of `c.pt` over `W` comes
from some `D_j`. -/
lemma exists_app_eq_of_isColimit_moduleCat (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (j : J) (x : (D.obj j).obj.obj (op W)), (c.ι.app j).hom.app (op W) x = s := by
  classical
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_of_isColimit_moduleCat hc s
  obtain ⟨n, U, g, hRg, hU, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
  choose j x hx using fun a ↦ hloc (g a) (hRg a)
  obtain ⟨k, hk⟩ := IsFiltered.exists_forall_nonempty_hom j
  let x' (a : Fin n) : (D.obj k).obj.obj (op (U a)) := (D.map (hk a).some).hom.app _ (x a)
  have hx' (a : Fin n) : (c.ι.app k).hom.app _ (x' a) = c.pt.obj.map (g a).op s := by
    rw [← hx a]
    exact cocone_ι_app_map_apply_moduleCat c _ _ _
  -- the differences on the overlaps die at a later stage
  have hW (a b : Fin n) : CompactSpace (pullback (g a) (g b)).left := by
    have := hU a
    have := hU b
    exact (compactSpace_and_quasiSeparatedSpace_pullback (g a) (g b)).1
  let d (a b : Fin n) := (D.obj k).obj.map (pullback.fst (g a) (g b)).op (x' a) -
    (D.obj k).obj.map (pullback.snd (g a) (g b)).op (x' b)
  have hd (a b : Fin n) : (c.ι.app k).hom.app _ (d a b) = 0 := by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, hx', hx']
    change c.pt.obj.map (pullback.fst (g a) (g b)).op (c.pt.obj.map (g a).op s) -
      c.pt.obj.map (pullback.snd (g a) (g b)).op (c.pt.obj.map (g b).op s) = 0
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition, sub_self]
  choose m φ hφ using fun ab : Fin n × Fin n ↦
    exists_map_app_eq_zero_of_isColimit_moduleCat hc (d ab.1 ab.2) (hd ab.1 ab.2)
  obtain ⟨l, ψ, h, hh⟩ := IsFiltered.exists_forall_comp_eq m φ
  let z (a : Fin n) : (D.obj l).obj.obj (op (U a)) := (D.map ψ).hom.app _ (x' a)
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows_moduleCat (D.obj l) g hcov)) z fun a b ↦ by
      change (D.obj l).obj.map _ ((D.map ψ).hom.app _ (x' a)) =
        (D.obj l).obj.map _ ((D.map ψ).hom.app _ (x' b))
      rw [← sub_eq_zero, ← NatTrans.naturality_apply (D.map ψ).hom,
        ← NatTrans.naturality_apply (D.map ψ).hom, ← map_sub,
        ← hh (a, b), map_comp_hom_app_apply_moduleCat]
      erw [hφ (a, b)]
      exact map_zero _
  refine ⟨l, y, (isSheafFor_ofArrows_moduleCat c.pt g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨a⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  erw [← NatTrans.naturality_apply]
  erw [hy a]
  exact (cocone_ι_app_map_apply_moduleCat c ψ _ (x' a)).trans (hx' a)

end Sections
section Cech

open Presheaf

/-- Let `c` be a colimit of a filtered diagram `D` of injective étale sheaves of `Λ`-modules on
`X`. On a finite family of étale `X`-schemes over `V` whose Čech nerve has quasi-compact
quasi-separated members, the Čech complex of (the underlying abelian presheaf of) `c.pt` is
exact in positive degrees. -/
lemma exactAt_cechComplex_of_isColimit_of_injective_moduleCat [∀ j, Injective (D.obj j)]
    (hc : IsColimit c) {V : X.Etale} {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n), CompactSpace (cechNerveObj U y).left.left ∧
      QuasiSeparatedSpace (cechNerveObj U y).left.left)
    (q : ℕ) :
    ((cechComplex U).obj
      (c.pt.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).ExactAt (q + 1) := by
  classical
  rw [exactAt_cechComplex_iff]
  intro z hz
  choose j w hw using fun y : Fin (q + 2) → Fin n ↦
    have := (hU (q + 1) y).1
    have := (hU (q + 1) y).2
    exists_app_eq_of_isColimit_moduleCat hc (W := (cechNerveObj U y).left) (z y)
  obtain ⟨k, hk⟩ := IsFiltered.exists_forall_nonempty_hom j
  let w' : ((cechComplex U).obj
      ((D.obj k).obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).X (q + 1) :=
    fun y ↦ (D.map (hk y).some).hom.app _ (w y)
  let ι' (i : J) := Functor.whiskerRight (c.ι.app i).hom
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let δ {i i' : J} (f : i ⟶ i') := Functor.whiskerRight (D.map f).hom
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hw' : ((cechComplex U).map (Y := c.pt.obj ⋙ forget₂ _ _) (ι' k)).f (q + 1) w' = z := by
    funext y
    exact (cocone_ι_app_map_apply_moduleCat c (hk y).some _ (w y)).trans (hw y)
  have hdw (y : Fin (q + 3) → Fin n) :
      (c.ι.app k).hom.app _ ((((cechComplex U).obj
        ((D.obj k).obj ⋙ forget₂ _ _)).d (q + 1) (q + 2) w') y) = 0 := by
    have := congr_fun (cechComplex_map_f_d_apply U (Q := c.pt.obj ⋙ forget₂ _ _) (ι' k)
      (q + 1) w') y
    rw [hw', hz] at this
    exact this
  choose m φ hφ using fun y : Fin (q + 3) → Fin n ↦
    have := (hU (q + 2) y).1
    exists_map_app_eq_zero_of_isColimit_moduleCat hc _ (hdw y)
  obtain ⟨l, ψ, h, hh⟩ := IsFiltered.exists_forall_comp_eq m φ
  have hdw'' : ((cechComplex U).obj ((D.obj l).obj ⋙ forget₂ _ _)).d (q + 1) (q + 2)
      (((cechComplex U).map (δ ψ)).f (q + 1) w') = 0 := by
    rw [← cechComplex_map_f_d_apply]
    funext y
    rw [cechComplex_map_f_apply]
    change (D.map ψ).hom.app _ _ = 0
    rw [← hh y, map_comp_hom_app_apply_moduleCat, hφ y, map_zero]
  have : Injective (D.obj l).obj := (sheafificationAdjunction _ _).map_injective _ inferInstance
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1
    (exactAt_cechComplex_forget₂_of_injective (D.obj l).obj U q) _ hdw''
  refine ⟨((cechComplex U).map (Y := c.pt.obj ⋙ forget₂ _ _) (ι' l)).f q b, ?_⟩
  rw [← cechComplex_map_f_d_apply, hb, ← hw']
  funext y
  exact cocone_ι_app_map_apply_moduleCat c ψ _ (w' y)

variable (X) in
/-- **A filtered colimit of injective sheaves of modules is acyclic on a qcqs scheme.** Let `X`
be quasi-compact quasi-separated and let `G` be a sheaf of `Λ`-modules on `X` corepresenting
global sections, via `e`. Then a filtered colimit of injective étale sheaves of `Λ`-modules has
no higher `Ext` out of `G`. -/
theorem subsingleton_ext_succ_of_isColimit_of_injective_moduleCat [CompactSpace X]
    [QuasiSeparatedSpace X] [∀ j, Injective (D.obj j)] (hc : IsColimit c)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      (G ⟶ F) ≃ F.obj.obj (op (Etale.mk (𝟙 X))))
    (he : ∀ {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : G ⟶ F) (g : F ⟶ F'),
      e F' (f ≫ g) = g.hom.app _ (e F f))
    (q : ℕ) : Subsingleton (Abelian.Ext G c.pt (q + 1)) := by
  let Φ := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : Φ.Additive := ⟨rfl⟩
  have : PreservesFiniteLimits Φ := by
    have : PreservesFiniteLimits (Φ ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have : Φ.PreservesEpimorphisms := ⟨fun {F F'} g _ ↦ by
    have hg : Sheaf.IsLocallySurjective g := (Sheaf.isLocallySurjective_iff_epi' (φ := g)).2 ‹_›
    have : Sheaf.IsLocallySurjective (Φ.map g) := ⟨fun s ↦ hg.imageSieve_mem s⟩
    exact Sheaf.epi_of_isLocallySurjective (Φ.map g)⟩
  let T : X.Etale := Etale.mk (𝟙 X)
  let B : X.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : X.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  exact Sheaf.subsingleton_ext_succ_of_exactAt_cechComplex Φ G (T := T) e he
    (fun I _ V n U q ↦
      have : Injective I.obj := (sheafificationAdjunction _ _).map_injective _ inferInstance
      exactAt_cechComplex_forget₂_of_injective I.obj U q)
    B ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov c.pt
    (fun V hV n U hU _ q ↦ exactAt_cechComplex_of_isColimit_of_injective_moduleCat hc U hU q) q

end Cech

/-- On a qcqs scheme, `Hom(G, -)` commutes with filtered colimits of étale sheaves of
`Λ`-modules, for `G` corepresenting global sections. -/
lemma commutesWithColimit_zero_moduleCat [CompactSpace X] [QuasiSeparatedSpace X]
    (hc : IsColimit c) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      (G ⟶ F) ≃ F.obj.obj (op (Etale.mk (𝟙 X))))
    (he : ∀ {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : G ⟶ F) (g : F ⟶ F'),
      e F' (f ≫ g) = g.hom.app _ (e F f)) :
    Abelian.Ext.CommutesWithColimit G 0 c := by
  let T : X.Etale := Etale.mk (𝟙 X)
  have : CompactSpace T.left := ‹CompactSpace X›
  have : QuasiSeparatedSpace T.left := ‹QuasiSeparatedSpace X›
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
    obtain ⟨j, y, hy⟩ := exists_app_eq_of_isColimit_moduleCat hc (e c.pt g)
    refine ⟨j, Abelian.Ext.mk₀ ((e _).symm y), ?_⟩
    rw [Abelian.Ext.mk₀_comp_mk₀]
    congr 1
    refine (e c.pt).injective ((he _ _).trans ?_)
    rw [Equiv.apply_symm_apply]
    exact hy
  · obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
    rw [Abelian.Ext.mk₀_comp_mk₀] at hy
    have hy' : f ≫ c.ι.app j = 0 := by
      rw [← Abelian.Ext.mk₀_zero] at hy
      exact (Abelian.Ext.mk₀_bijective _ _).1 hy
    have he₀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : e F 0 = 0 := by
      have := he (0 : G ⟶ F) (0 : F ⟶ F)
      rw [Limits.comp_zero] at this
      rw [this]
      rfl
    obtain ⟨k, φ, hφ⟩ := exists_map_app_eq_zero_of_isColimit_moduleCat hc (e _ f)
      ((he f (c.ι.app j)).symm.trans ((congrArg (e _) hy').trans (he₀ _)))
    refine ⟨k, φ, ?_⟩
    rw [Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.mk₀_zero]
    congr 1
    exact (e _).injective ((he _ _).trans (hφ.trans (he₀ _).symm))

end AlgebraicGeometry.Scheme
