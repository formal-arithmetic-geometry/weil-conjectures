/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Presentable.Directed
public import WeilConjectures.AlgebraicGeometry.CompatiblePullbackSheafSystem
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.Continuity

/-!
# Continuity of étale cohomology at cofiltered limits

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S` with
affine transition maps and limit `X`, and let `F` be an abelian étale sheaf on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ})` ([Stacks, Tag 09YQ])
(`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit'`).

The index category is replaced by a cofinal directed poset (Deligne,
`CategoryTheory.IsFiltered.exists_directed`), and the pullbacks of `F` form a system of sheaves
whose colimit on `X` is the pullback of `F`, to which
`AlgebraicGeometry.Etale.SystemData.isContinuousAt` applies.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

namespace SystemData

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- **Continuity of étale cohomology for systems.** -/
theorem isContinuousAt (S : SystemData D c) (hS : S.Laws) (n : ℕ) : S.IsContinuousAt n := by
  induction n generalizing S with
  | zero => exact isContinuousAt_zero hc S hS
  | succ n ih => exact isContinuousAt_succ hc (fun S hS ↦ ih S hS) S hS

end SystemData

section CohomologyMapComp

variable {X Y Z : Scheme.{u}}

/-- The map induced on cohomology by an isomorphism of sheaves is injective. -/
lemma eq_zero_of_sheafH_map_eq_zero {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') [IsIso φ] {q : ℕ} {x : Sheaf.H G q} (h : Sheaf.H.map φ q x = 0) : x = 0 := by
  have := congrArg (Sheaf.H.map (inv φ) q) h
  rwa [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply, map_zero] at this

lemma cohomologyMap_comp_eq_zero_of_eq_zero (u : X ⟶ Y) (w : Y ⟶ Z) (uw : X ⟶ Z)
    (h : u ≫ w = uw) (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (y : Sheaf.H G q) (hy : cohomologyMap uw G q y = 0) :
    cohomologyMap u ((upperStar AddCommGrpCat.{u + 1} w).obj G) q (cohomologyMap w G q y) = 0 := by
  subst h
  rw [(cohomologyPullbackFunctorial u w G q).2.1, hy, map_zero]

lemma cohomologyMap_comp_eq_zero_of_comp_eq_zero (u : X ⟶ Y) (w : Y ⟶ Z)
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (y : Sheaf.H G q)
    (hy : cohomologyMap u ((upperStar AddCommGrpCat.{u + 1} w).obj G) q
      (cohomologyMap w G q y) = 0) :
    cohomologyMap (u ≫ w) G q y = 0 := by
  rw [(cohomologyPullbackFunctorial u w G q).2.1] at hy
  exact eq_zero_of_sheafH_map_eq_zero _ hy

end CohomologyMapComp

/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an abelian étale sheaf on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ})` along the pullback maps: every class on `X` comes from some
`Dᵢ`, and a class on `Dᵢ` which vanishes on `X` already vanishes on some `Dⱼ`, `j ⟶ i`. -/
theorem cohomologyMap_isColimit_of_isLimit' {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    (∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x) ∧
    ∀ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
      Etale.cohomologyMap (c.π.app i).left _ q y = 0 →
        ∃ (j : I) (g : j ⟶ i), Etale.cohomologyMap (D.map g).left _ q y = 0 := by
  obtain ⟨α, _, _, _, Φ, _⟩ := IsFiltered.exists_directed Iᵒᵖ
  have : IsFiltered α := isFiltered_of_directed_le_nonempty α
  have : IsConnected α := IsFiltered.isConnected α
  let E : αᵒᵖ ⥤ Scheme.{u} := Φ.leftOp ⋙ D ⋙ Over.forget S
  let cE : Cone E := ((Over.forget S).mapCone c).whisker Φ.leftOp
  have hcE : IsLimit cE := (Functor.Initial.isLimitWhiskerEquiv Φ.leftOp _).symm hc
  have (a : αᵒᵖ) : CompactSpace (E.obj a) := inferInstanceAs (CompactSpace (D.obj _).left)
  have (a : αᵒᵖ) : QuasiSeparatedSpace (E.obj a) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj _).left)
  have (a b : αᵒᵖ) (f : a ⟶ b) : IsAffineHom (E.map f) :=
    inferInstanceAs (IsAffineHom (D.map _).left)
  let v (a : α) : E.obj (op a) ⟶ S := (D.obj (Φ.obj a).unop).hom
  have wv (a b : α) (f : a ⟶ b) : v b = E.map f.op ≫ v a := (Over.w (D.map _)).symm
  have wLimit (a : α) : c.pt.hom = cE.π.app (op a) ≫ v a := (Over.w (c.π.app _)).symm
  obtain ⟨hid, hcomp, hG⟩ := compatiblePullbackSheafSystem E cE S F v wv c.pt.hom wLimit
  let Sys : SystemData E cE :=
    { F := fun a ↦ (upperStar AddCommGrpCat.{u + 1} (v a)).obj F
      φ := fun {a b} f ↦ (upperStarComp AddCommGrpCat.{u + 1} (E.map f.op) (v a) (v b)
        (wv a b f)).inv.app F
      G := (Functor.const α).obj ((upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F)
      eG := fun a ↦ (upperStarComp AddCommGrpCat.{u + 1} (cE.π.app (op a)) (v a) c.pt.hom
        (wLimit a)).app F
      hG := hG
      L := constCocone α _
      hL := isColimitConstCocone α _ }
  have hcont := SystemData.isContinuousAt hcE Sys ⟨hid, hcomp⟩ q
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨a, y, hy⟩ := hcont.1 x
    refine ⟨(Φ.obj a).unop, y, ?_⟩
    rw [← hy]
    change _ = Sheaf.H.map _ q (Sheaf.H.map _ q _)
    rw [← Sheaf.H.map_comp_apply]
    change _ = Sheaf.H.map (((upperStarComp AddCommGrpCat.{u + 1} (c.π.app _).left
      (D.obj _).hom c.pt.hom _).inv.app F ≫ 𝟙 _) ≫ (upperStarComp AddCommGrpCat.{u + 1}
        (c.π.app _).left (D.obj _).hom c.pt.hom _).hom.app F) q _
    rw [Category.comp_id, Iso.inv_hom_id_app, Sheaf.H.map_id_apply]
    rfl
  · obtain ⟨⟨_, a, m⟩⟩ : Nonempty (StructuredArrow (op i) Φ) := inferInstance
    let m' : (Φ.obj a).unop ⟶ i := m.unop
    let e := upperStarComp AddCommGrpCat.{u + 1} (D.map m').left (D.obj i).hom (v a)
      (Over.w (D.map m')).symm
    let ya : Sheaf.H (Sys.F a) q :=
      Sheaf.H.map (e.inv.app F) q (cohomologyMap (D.map m').left _ q y)
    have h₁ : cohomologyMap (cE.π.app (op a)) _ q (cohomologyMap (D.map m').left _ q y) = 0 :=
      cohomologyMap_comp_eq_zero_of_eq_zero _ _ _
        (congrArg CommaMorphism.left (c.w m')) _ _ _ hy
    have h₂ : Sys.toLimitH a q ya = 0 := by
      change Sheaf.H.map _ q (cohomologyMap _ _ q (Sheaf.H.map _ q _)) = 0
      rw [cohomologyMap_map]
      erw [h₁]
      rw [map_zero, map_zero]
    obtain ⟨b, f, hf⟩ := hcont.2 a ya h₂
    refine ⟨(Φ.obj b).unop, (Φ.map f).unop ≫ m', ?_⟩
    have h₃ : cohomologyMap (E.map f.op) _ q
        (Sheaf.H.map (e.inv.app F) q (cohomologyMap (D.map m').left _ q y)) = 0 :=
      eq_zero_of_sheafH_map_eq_zero (Sys.φ f) hf
    erw [cohomologyMap_map] at h₃
    have h₄ := eq_zero_of_sheafH_map_eq_zero _ h₃
    rw [D.map_comp, Over.comp_left]
    exact cohomologyMap_comp_eq_zero_of_comp_eq_zero _ _ _ _ _ h₄

end AlgebraicGeometry.Etale
