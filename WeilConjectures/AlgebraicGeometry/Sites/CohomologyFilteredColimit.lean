/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.CategoryTheory.Abelian.ExtFilteredColimit
public import WeilConjectures.Mathlib.CategoryTheory.Filtered.Basic

/-!
# Étale cohomology of a qcqs scheme commutes with filtered colimits

Let `X` be a quasi-compact quasi-separated scheme and `D` a filtered diagram of abelian étale
sheaves on `X` with colimit `c`. We show that `Hᵠ(X, c.pt)` is the colimit of the `Hᵠ(X, D_j)`
([Stacks 03Q6]).

The argument follows [Stacks 0739]:

* sections over an étale `X`-scheme `W` with quasi-compact quasi-separated underlying scheme
  commute with filtered colimits: a section of `c.pt` comes locally from some stage, finitely
  many affine pieces suffice, and the local sections glue at a common later stage, their
  differences on the quasi-compact overlaps dying at a later stage;
* hence the Čech complexes of a filtered colimit of injective sheaves, on finite families of
  qcqs étale `X`-schemes, are filtered colimits of exact complexes, so exact in positive degrees,
  and the Čech criterion `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` shows
  that a filtered colimit of injective sheaves has no higher cohomology;
* the general case follows by dimension shifting,
  `CategoryTheory.Abelian.Ext.commutesWithColimit_of_isFiltered`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_app_eq_of_isColimit_addCommGrpCat`: every section of a
  filtered colimit of abelian étale sheaves over a qcqs étale `X`-scheme comes from some stage.
- `AlgebraicGeometry.Scheme.exists_map_app_eq_zero_of_isColimit`: a section of some stage
  which vanishes in the colimit, over an étale `X`-scheme with quasi-compact underlying space,
  vanishes at a later stage.
- `AlgebraicGeometry.Scheme.subsingleton_H_succ_of_isColimit_of_injective`: on a qcqs scheme, a
  filtered colimit of injective abelian sheaves has no higher cohomology.
- `AlgebraicGeometry.Scheme.H_map_bijective_of_isColimit_of_isFiltered`: étale cohomology of a
  qcqs scheme commutes with filtered colimits; for essentially `(u + 1)`-small index categories
  of any size, see `AlgebraicGeometry.Scheme.H_map_bijective_of_isColimit_of_essentiallySmall`.
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {J : Type (u + 1)} [Category.{u + 1} J] [IsFiltered J]
  {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}

section Sections

omit [IsFiltered J] in
/-- The legs of a cocone of abelian sheaves are compatible with the transition maps, on
sections. -/
lemma cocone_ι_app_map_apply (c : Cocone D) {i i' : J} (f : i ⟶ i') (V : X.Etaleᵒᵖ)
    (v : (D.obj i).obj.obj V) :
    (c.ι.app i').hom.app V ((D.map f).hom.app V v) = (c.ι.app i).hom.app V v := by
  rw [← c.w f]
  rfl

omit [IsFiltered J] in
/-- The transition maps of a diagram of abelian sheaves are functorial, on sections. -/
lemma map_comp_hom_app_apply (D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {i i' i'' : J} (f : i ⟶ i') (g : i' ⟶ i'') (V : X.Etaleᵒᵖ) (v : (D.obj i).obj.obj V) :
    (D.map (f ≫ g)).hom.app V v = (D.map g).hom.app V ((D.map f).hom.app V v) := by
  rw [D.map_comp]
  rfl

variable (D) in
/-- Sections of the objectwise colimit of the presheaves underlying a filtered diagram of
abelian sheaves come from some stage. -/
lemma exists_colimit_ι_app_eq (V : X.Etaleᵒᵖ)
    (t : (colimit (D ⋙ sheafToPresheaf _ _)).obj V) :
    ∃ (j : J) (x : (D.obj j).obj.obj V),
      (colimit.ι (D ⋙ sheafToPresheaf _ _) j).app V x = t := by
  exact Concrete.isColimit_exists_rep _
    (isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj V) (colimit.isColimit _)) t

variable (D) in
/-- A section of a stage of a filtered diagram of abelian sheaves which vanishes in the
objectwise colimit of the underlying presheaves vanishes at a later stage. -/
lemma exists_map_app_eq_zero_of_colimit_ι_app_eq_zero (V : X.Etaleᵒᵖ) {j : J}
    (x : (D.obj j).obj.obj V) (hx : (colimit.ι (D ⋙ sheafToPresheaf _ _) j).app V x = 0) :
    ∃ (k : J) (φ : j ⟶ k), (D.map φ).hom.app V x = 0 := by
  obtain ⟨k, φ, ψ, h⟩ := Concrete.isColimit_exists_of_rep_eq _
    (isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj V)
      (colimit.isColimit (D ⋙ sheafToPresheaf _ _))) x 0 (by erw [hx, map_zero])
  exact ⟨k, φ, h.trans (map_zero _)⟩

/-- The two composites of an isomorphism of abelian sheaves and its inverse, on sections. -/
lemma _root_.CategoryTheory.Sheaf.iso_hom_app_inv_app_apply {C : Type*} [Category C]
    {K : GrothendieckTopology C} {F G : Sheaf K AddCommGrpCat.{u + 1}} (e : F ≅ G) (V : Cᵒᵖ)
    (s : G.obj.obj V) : e.hom.hom.app V (e.inv.hom.app V s) = s := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
  rfl

omit [IsFiltered J] in
/-- The comparison of a colimit cocone of abelian sheaves with the sheafification of the
objectwise colimit of the underlying presheaves. -/
lemma sheafifyCocone_ι_app_comp_coconePointUniqueUpToIso (hc : IsColimit c) (j : J) :
    ((Sheaf.sheafifyCocone (colimit.cocone (D ⋙ sheafToPresheaf _ _))).ι.app j).hom ≫
      ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso
        hc).hom.hom = (c.ι.app j).hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, IsColimit.comp_coconePointUniqueUpToIso_hom]

omit [IsFiltered J] in
/-- The comparison of a colimit cocone of abelian sheaves with the sheafification of the
objectwise colimit of the underlying presheaves, in the other direction. -/
lemma sheafifyCocone_ι_app_eq (hc : IsColimit c) (j : J) :
    ((Sheaf.sheafifyCocone (colimit.cocone (D ⋙ sheafToPresheaf _ _))).ι.app j).hom =
      (c.ι.app j).hom ≫
        ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso
        hc).inv.hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, IsColimit.comp_coconePointUniqueUpToIso_inv]

/-- **Sections of a filtered colimit come locally from a stage.** -/
lemma exists_mem_forall_exists_of_isColimit (hc : IsColimit c) {W : X.Etale}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (j : J) (x : (D.obj j).obj.obj (op V)),
        (c.ι.app j).hom.app (op V) x = c.pt.obj.map f.op s := by
  let e := (Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)).coconePointUniqueUpToIso hc
  refine ⟨_, Presheaf.imageSieve_mem X.smallEtaleTopology
    (toSheafify X.smallEtaleTopology (colimit (D ⋙ sheafToPresheaf _ _)))
    (e.inv.hom.app (op W) s), fun V f ⟨t, ht⟩ ↦ ?_⟩
  obtain ⟨j, x, rfl⟩ := exists_colimit_ι_app_eq D (op V) t
  refine ⟨j, x, ?_⟩
  have h₁ := Sheaf.sheafifyCocone_ι_app_val (colimit.cocone (D ⋙ sheafToPresheaf _ _)) j
  simp only [colimit.cocone_ι, colimit.cocone_x] at h₁
  have h₂ := congrArg (fun φ ↦ φ.app (op V) x)
    ((sheafifyCocone_ι_app_comp_coconePointUniqueUpToIso hc j).symm.trans
      (congrArg (· ≫ e.hom.hom) h₁))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h₂
  refine h₂.trans ?_
  erw [ht, NatTrans.naturality_apply e.hom.hom f.op]
  congr 1
  exact Sheaf.iso_hom_app_inv_app_apply e _ s

/-- **A section vanishing in a filtered colimit vanishes locally at a later stage.** -/
lemma exists_mem_forall_exists_eq_zero_of_isColimit (hc : IsColimit c) {W : X.Etale} {j : J}
    (x : (D.obj j).obj.obj (op W)) (hx : (c.ι.app j).hom.app (op W) x = 0) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (k : J) (φ : j ⟶ k), (D.map φ).hom.app (op V) ((D.obj j).obj.map f.op x) = 0 := by
  have h₁ := Sheaf.sheafifyCocone_ι_app_val (colimit.cocone (D ⋙ sheafToPresheaf _ _)) j
  simp only [colimit.cocone_ι, colimit.cocone_x] at h₁
  have h₂ := congrArg (fun φ ↦ φ.app (op W) x) (h₁.symm.trans (sheafifyCocone_ι_app_eq hc j))
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
  exact exists_map_app_eq_zero_of_colimit_ι_app_eq_zero D (op V) _
    ((NatTrans.naturality_apply (colimit.ι (D ⋙ sheafToPresheaf _ _) j) f.op x).trans hf)

/-- **Sections of a filtered colimit over a quasi-compact étale `X`-scheme, injectivity.** Let
`c` be a colimit of a filtered diagram `D` of abelian étale sheaves on `X`, and `W` an étale
`X`-scheme with quasi-compact underlying space. A section of `D_j` over `W` which vanishes in
`c.pt` vanishes in some `D_k`, `j ⟶ k`. -/
lemma exists_map_app_eq_zero_of_isColimit (hc : IsColimit c) {W : X.Etale}
    [CompactSpace W.left] {j : J} (x : (D.obj j).obj.obj (op W))
    (hx : (c.ι.app j).hom.app (op W) x = 0) :
    ∃ (k : J) (φ : j ⟶ k), (D.map φ).hom.app (op W) x = 0 := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_eq_zero_of_isColimit hc x hx
  obtain ⟨n, U, g, hRg, -, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
  choose k φ hφ using fun a ↦ hloc (g a) (hRg a)
  obtain ⟨m, ψ, h, hh⟩ := IsFiltered.exists_forall_comp_eq k φ
  refine ⟨m, ψ, (isSheafFor_ofArrows (D.obj m) g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨a⟩
  change (D.obj m).obj.map _ _ = (D.obj m).obj.map _ 0
  rw [map_zero, ← NatTrans.naturality_apply, ← hh a, map_comp_hom_app_apply, hφ a, map_zero]

/-- **Sections of a filtered colimit over a qcqs étale `X`-scheme, surjectivity.** Let `c` be a
colimit of a filtered diagram `D` of abelian étale sheaves on `X`, and `W` an étale `X`-scheme
with quasi-compact quasi-separated underlying scheme. Every section of `c.pt` over `W` comes
from some `D_j`. -/
lemma exists_app_eq_of_isColimit_addCommGrpCat (hc : IsColimit c) {W : X.Etale}
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (j : J) (x : (D.obj j).obj.obj (op W)), (c.ι.app j).hom.app (op W) x = s := by
  classical
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_of_isColimit hc s
  obtain ⟨n, U, g, hRg, hU, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
  choose j x hx using fun a ↦ hloc (g a) (hRg a)
  obtain ⟨k, hk⟩ := IsFiltered.exists_forall_nonempty_hom j
  let x' (a : Fin n) : (D.obj k).obj.obj (op (U a)) := (D.map (hk a).some).hom.app _ (x a)
  have hx' (a : Fin n) : (c.ι.app k).hom.app _ (x' a) = c.pt.obj.map (g a).op s := by
    rw [← hx a]
    exact cocone_ι_app_map_apply c _ _ _
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
    exists_map_app_eq_zero_of_isColimit hc (d ab.1 ab.2) (hd ab.1 ab.2)
  obtain ⟨l, ψ, h, hh⟩ := IsFiltered.exists_forall_comp_eq m φ
  let z (a : Fin n) : (D.obj l).obj.obj (op (U a)) := (D.map ψ).hom.app _ (x' a)
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows (D.obj l) g hcov)) z fun a b ↦ by
      change (D.obj l).obj.map _ ((D.map ψ).hom.app _ (x' a)) =
        (D.obj l).obj.map _ ((D.map ψ).hom.app _ (x' b))
      rw [← sub_eq_zero, ← NatTrans.naturality_apply (D.map ψ).hom,
        ← NatTrans.naturality_apply (D.map ψ).hom, ← map_sub,
        ← hh (a, b), map_comp_hom_app_apply]
      erw [hφ (a, b)]
      exact map_zero _
  refine ⟨l, y, (isSheafFor_ofArrows c.pt g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨a⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  erw [← NatTrans.naturality_apply]
  erw [hy a]
  exact (cocone_ι_app_map_apply c ψ _ (x' a)).trans (hx' a)

end Sections
section Cech

open Presheaf

/-- Let `c` be a colimit of a filtered diagram `D` of injective abelian étale sheaves on `X`. On
a finite family of étale `X`-schemes over `V` whose Čech nerve has quasi-compact
quasi-separated members, the Čech complex of `c.pt` is exact in positive degrees: a Čech
cocycle comes from a cochain of some `D_k` whose differential vanishes at a later stage `D_l`,
whose Čech complex is exact. -/
lemma exactAt_cechComplex_of_isColimit_of_injective [∀ j, Injective (D.obj j)]
    (hc : IsColimit c) {V : X.Etale} {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n), CompactSpace (cechNerveObj U y).left.left ∧
      QuasiSeparatedSpace (cechNerveObj U y).left.left)
    (q : ℕ) : ((cechComplex U).obj c.pt.obj).ExactAt (q + 1) := by
  classical
  rw [exactAt_cechComplex_iff]
  intro z hz
  choose j w hw using fun y : Fin (q + 2) → Fin n ↦
    have := (hU (q + 1) y).1
    have := (hU (q + 1) y).2
    exists_app_eq_of_isColimit_addCommGrpCat hc (W := (cechNerveObj U y).left) (z y)
  obtain ⟨k, hk⟩ := IsFiltered.exists_forall_nonempty_hom j
  let w' : ((cechComplex U).obj (D.obj k).obj).X (q + 1) := fun y ↦
    (D.map (hk y).some).hom.app _ (w y)
  have hw' : ((cechComplex U).map (Y := c.pt.obj) (c.ι.app k).hom).f (q + 1) w' = z := by
    funext y
    exact (cocone_ι_app_map_apply c (hk y).some _ (w y)).trans (hw y)
  have hdw (y : Fin (q + 3) → Fin n) :
      (c.ι.app k).hom.app _ ((((cechComplex U).obj (D.obj k).obj).d (q + 1) (q + 2) w') y) =
        0 := by
    have := congr_fun (cechComplex_map_f_d_apply U (Q := c.pt.obj) (c.ι.app k).hom (q + 1) w') y
    rw [hw', hz] at this
    exact this
  choose m φ hφ using fun y : Fin (q + 3) → Fin n ↦
    have := (hU (q + 2) y).1
    exists_map_app_eq_zero_of_isColimit hc _ (hdw y)
  obtain ⟨l, ψ, h, hh⟩ := IsFiltered.exists_forall_comp_eq m φ
  have hdw'' : ((cechComplex U).obj (D.obj l).obj).d (q + 1) (q + 2)
      (((cechComplex U).map (D.map ψ).hom).f (q + 1) w') = 0 := by
    rw [← cechComplex_map_f_d_apply]
    funext y
    rw [cechComplex_map_f_apply, ← hh y, map_comp_hom_app_apply, hφ y, map_zero]
    rfl
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1
    (Sheaf.exactAt_cechComplex_of_injective (D.obj l) U q) _ hdw''
  refine ⟨((cechComplex U).map (Y := c.pt.obj) (c.ι.app l).hom).f q b, ?_⟩
  rw [← cechComplex_map_f_d_apply, hb, ← hw']
  funext y
  exact cocone_ι_app_map_apply c ψ _ (w' y)

variable (X) in
/-- **A filtered colimit of injective sheaves is acyclic on a qcqs scheme.** On a quasi-compact
quasi-separated scheme `X`, a filtered colimit of injective abelian étale sheaves has no higher
cohomology. This follows from the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` applied to the étale
`X`-schemes with quasi-compact quasi-separated underlying scheme, by
`AlgebraicGeometry.Scheme.exactAt_cechComplex_of_isColimit_of_injective`. -/
theorem subsingleton_H_succ_of_isColimit_of_injective [CompactSpace X] [QuasiSeparatedSpace X]
    [∀ j, Injective (D.obj j)] (hc : IsColimit c) (q : ℕ) :
    Subsingleton (Sheaf.H c.pt (q + 1)) := by
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
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
  exact Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov c.pt
    (fun V hV n U hU _ q ↦ exactAt_cechComplex_of_isColimit_of_injective hc U hU q) q

end Cech

/-- On a qcqs scheme, the functor of global sections `H⁰(X, -)` commutes with filtered
colimits of abelian étale sheaves. -/
lemma commutesWithColimit_zero [CompactSpace X] [QuasiSeparatedSpace X] (hc : IsColimit c) :
    Abelian.Ext.CommutesWithColimit
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) 0 c := by
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  have : CompactSpace T.left := ‹CompactSpace X›
  have : QuasiSeparatedSpace T.left := ‹QuasiSeparatedSpace X›
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨j, y, hy⟩ :=
      exists_app_eq_of_isColimit_addCommGrpCat hc (Sheaf.H.equiv₀ c.pt hT x)
    refine ⟨j, (Sheaf.H.equiv₀ _ hT).symm y, (Sheaf.H.equiv₀ c.pt hT).injective ?_⟩
    refine (Sheaf.H.equiv₀_naturality hT (c.ι.app j) _).symm.trans ?_
    rw [AddEquiv.apply_symm_apply, hy]
  · obtain ⟨k, φ, hφ⟩ := exists_map_app_eq_zero_of_isColimit hc (Sheaf.H.equiv₀ _ hT y)
      ((Sheaf.H.equiv₀_naturality hT (c.ι.app j) y).trans
        ((congrArg (Sheaf.H.equiv₀ c.pt hT) hy).trans (map_zero _)))
    exact ⟨k, φ, (Sheaf.H.equiv₀ _ hT).injective
      ((Sheaf.H.equiv₀_naturality hT (D.map φ) y).symm.trans (hφ.trans (map_zero _).symm))⟩

variable (X) in
/-- **Étale cohomology commutes with filtered colimits on a qcqs scheme.** Let `X` be
quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered diagram `D` of
abelian étale sheaves on `X`. Then for every `q` the canonical map
`colim_j Hᵠ(X, D_j) ⟶ Hᵠ(X, colim_j D_j)` is bijective; this is spelled out elementwise: every
class on the colimit comes from some `D_j`, and a class on `D_j` which dies on the colimit
already dies on some `D_k`, `j ⟶ k`. (blueprint: `lem-weil-pbc-cohomology-filtered-colimit`) -/
@[stacks 03Q6]
theorem H_map_bijective_of_isColimit_of_isFiltered [CompactSpace X] [QuasiSeparatedSpace X]
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (j : J) (y : Sheaf.H (D.obj j) q),
      Sheaf.H.map (c.ι.app j) q y = x) ∧
    ∀ (j : J) (y : Sheaf.H (D.obj j) q), Sheaf.H.map (c.ι.app j) q y = 0 →
      ∃ (k : J) (φ : j ⟶ k), Sheaf.H.map (D.map φ) q y = 0 := by
  have : IsFiltered (AsSmall.{u + 1} J) := IsFiltered.of_equivalence AsSmall.equiv
  have : HasExactColimitsOfShape J (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasExactColimitsOfShape.of_domain_equivalence _ AsSmall.equiv.symm
  exact Abelian.Ext.commutesWithColimit_of_isFiltered _
    (fun _ _ hc ↦ commutesWithColimit_zero hc)
    (fun _ _ hc _ q x ↦ (subsingleton_H_succ_of_isColimit_of_injective X hc q).elim _ _) q D c hc

variable (X) in
/-- **Étale cohomology commutes with essentially small filtered colimits on a qcqs scheme.**
The version of `AlgebraicGeometry.Scheme.H_map_bijective_of_isColimit_of_isFiltered` for a
filtered index category `K` of any size which is essentially `(u + 1)`-small, for instance a
`u`-small category or a preorder in `Type (u + 1)`.
(blueprint: `lem-weil-pbc-cohomology-filtered-colimit`) -/
@[stacks 03Q6]
theorem H_map_bijective_of_isColimit_of_essentiallySmall [CompactSpace X] [QuasiSeparatedSpace X]
    {K : Type w} [Category.{w'} K] [IsFiltered K] [EssentiallySmall.{u + 1} K]
    {E : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {d : Cocone E} (hd : IsColimit d)
    (q : ℕ) :
    (∀ x : Sheaf.H d.pt q, ∃ (k : K) (y : Sheaf.H (E.obj k) q),
      Sheaf.H.map (d.ι.app k) q y = x) ∧
    ∀ (k : K) (y : Sheaf.H (E.obj k) q), Sheaf.H.map (d.ι.app k) q y = 0 →
      ∃ (k' : K) (φ : k ⟶ k'), Sheaf.H.map (E.map φ) q y = 0 := by
  let e := equivSmallModel.{u + 1} K
  have : IsFiltered (SmallModel.{u + 1} K) := IsFiltered.of_equivalence e
  have h := H_map_bijective_of_isColimit_of_isFiltered X
    ((IsColimit.whiskerEquivalenceEquiv e.symm).1 hd) q
  refine ⟨fun x ↦ ?_, fun k y hy ↦ ?_⟩
  · obtain ⟨j, y, hy⟩ := h.1 x
    exact ⟨_, y, hy⟩
  · obtain ⟨j, φ, hφ⟩ := h.2 (e.functor.obj k) (Sheaf.H.map (E.map (e.unit.app k)) q y) (by
      change Sheaf.H.map (d.ι.app _) q (Sheaf.H.map (E.map (e.unit.app k)) q y) = 0
      rw [← Sheaf.H.map_comp_apply, d.w]
      exact hy)
    refine ⟨_, e.unit.app k ≫ e.inverse.map φ, ?_⟩
    rw [E.map_comp, Sheaf.H.map_comp_apply]
    exact hφ

end AlgebraicGeometry.Scheme
