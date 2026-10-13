/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Modules.DescentEffective
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.PreimageGlue
public import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ModulesAffine

/-!
# Modules of finite presentation descend to a finite stage of a cofiltered limit

Let `{Dⱼ}` be a cofiltered system of quasi-compact separated schemes with affine transition
morphisms and limit `lim Dⱼ`. Every module of finite presentation on `lim Dⱼ` is the pullback of
a module of finite presentation on some stage `Dⱼ` (Stacks, Tag 01ZR; EGA IV₃, 8.5.2).

## Proof

Fix a stage `S = Dᵢ₀` and a finite affine open cover `U a` of `S`. Over each `U a` the system
`{Dⱼᵢ₀⁻¹ U a}` consists of affine schemes, with limit the preimage of `U a` in `lim Dⱼ`, so the
restriction of the module descends to a module `O a` on some stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_of_isLimit_of_isAffine`). Since `S` is
separated, the intersections of the `U a` are affine, so the gluing isomorphisms of the
restrictions on the preimages of `U a ⊓ U b` descend to some stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullHom_eq_of_isLimit_of_isAffine`), and the identity
and cocycle conditions, which hold in the limit, hold at some later stage
(`AlgebraicGeometry.Scheme.Modules.exists_pullHom_eq_pullHom_of_isLimit_of_isAffine`). At that
stage the gluing morphisms define a descent datum for the open cover by the preimages of the
`U a` (`CategoryTheory.Pseudofunctor.DescentData'.ofGlue`), which is effective. The glued
module is of finite presentation, and its pullback to the limit is the original module
(`CategoryTheory.Pseudofunctor.DescentData'.nonempty_map_iso_of_ofGlue`), since morphisms of
modules glue along open covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace AlgebraicGeometry

namespace Scheme.Modules

lemma modulesPseudofunctor_pullHom_eq' {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules}
    {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁)
    (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := modulesPseudofunctor) φ g gf₁ gf₂ h₁ h₂ =
      (pullbackCompOfEq g f₁ gf₁ h₁ M₁).inv ≫ (pullback g).map φ ≫
        (pullbackCompOfEq g f₂ gf₂ h₂ M₂).hom := by
  subst h₁ h₂
  rw [modulesPseudofunctor_pullHom_eq]
  simp [pullbackCompOfEq, pullbackCongr]

section PullHom

variable {J : Type u} [Category.{u} J] [IsCofiltered J] {E : J ⥤ Scheme.{u}} {c : Cone E}
  [∀ j, IsAffine (E.obj j)]

set_option backward.isDefEq.respectTransparency false in
/-- **Morphisms of modules descend to a finite stage, affine case**, in the form of `pullHom`:
a morphism between the pullbacks to the limit of modules of finite presentation `O₁`, `O₂` along
morphisms factoring through a stage is the pullback of a morphism defined over a later stage. -/
theorem exists_pullHom_eq_of_isLimit_of_isAffine (hc : IsLimit c) {j : J} {W₁ W₂ : Scheme.{u}}
    {O₁ : W₁.Modules} {O₂ : W₂.Modules} [O₁.IsFinitePresentation] [O₂.IsFinitePresentation]
    (x₁ : E.obj j ⟶ W₁) (x₂ : E.obj j ⟶ W₂) {y₁ : c.pt ⟶ W₁} {y₂ : c.pt ⟶ W₂}
    (hy₁ : c.π.app j ≫ x₁ = y₁) (hy₂ : c.π.app j ≫ x₂ = y₂)
    (φ : (modulesPseudofunctor.map y₁.op.toLoc).toFunctor.obj O₁ ⟶
      (modulesPseudofunctor.map y₂.op.toLoc).toFunctor.obj O₂) :
    ∃ (k : J) (t : k ⟶ j)
      (ψ : (modulesPseudofunctor.map (E.map t ≫ x₁).op.toLoc).toFunctor.obj O₁ ⟶
        (modulesPseudofunctor.map (E.map t ≫ x₂).op.toLoc).toFunctor.obj O₂),
      pullHom ψ (c.π.app k) y₁ y₂ (by rw [← hy₁, c.w_assoc]) (by rw [← hy₂, c.w_assoc]) = φ := by
  let φ' : (pullback (c.π.app j)).obj ((pullback x₁).obj O₁) ⟶
      (pullback (c.π.app j)).obj ((pullback x₂).obj O₂) :=
    (modulesPseudofunctor.mapComp' x₁.op.toLoc (c.π.app j).op.toLoc y₁.op.toLoc
        (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app O₁ ≫ φ ≫
      (modulesPseudofunctor.mapComp' x₂.op.toLoc (c.π.app j).op.toLoc y₂.op.toLoc
        (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app O₂
  obtain ⟨k, t, ψ', hψ'⟩ := exists_pullback_map_eq_of_isLimit_of_isAffine' hc φ'
  refine ⟨k, t, (modulesPseudofunctor.mapComp' x₁.op.toLoc (E.map t).op.toLoc
      (E.map t ≫ x₁).op.toLoc (op_toLoc_comp_eq rfl)).hom.toNatTrans.app O₁ ≫ ψ' ≫
    (modulesPseudofunctor.mapComp' x₂.op.toLoc (E.map t).op.toLoc
      (E.map t ≫ x₂).op.toLoc (op_toLoc_comp_eq rfl)).inv.toNatTrans.app O₂, ?_⟩
  refine (pullHom_mapComp'_conj_symm (F := modulesPseudofunctor) x₁ x₂ (E.map t) (E.map t) _ _ rfl
    rfl ψ' (c.π.app k) (c.π.app j) (c.π.app j) (c.w t) (c.w t) y₁ y₂ hy₁ hy₂).trans ?_
  have : pullHom (F := modulesPseudofunctor) ψ' (c.π.app k) (c.π.app j) (c.π.app j) (c.w t)
      (c.w t) = φ' := by
    rw [modulesPseudofunctor_pullHom_eq']
    exact hψ'
  rw [this]
  simp only [φ', Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

/-- **Equalities of morphisms of modules descend to a finite stage, affine case**, in the form
of `pullHom`. -/
theorem exists_pullHom_eq_pullHom_of_isLimit_of_isAffine (hc : IsLimit c) {j : J}
    {W₁ W₂ : Scheme.{u}} {O₁ : W₁.Modules} {O₂ : W₂.Modules} [O₁.IsFinitePresentation]
    [O₂.IsFinitePresentation] (x₁ : E.obj j ⟶ W₁) (x₂ : E.obj j ⟶ W₂) {y₁ : c.pt ⟶ W₁}
    {y₂ : c.pt ⟶ W₂} (hy₁ : c.π.app j ≫ x₁ = y₁) (hy₂ : c.π.app j ≫ x₂ = y₂)
    (ψ₁ ψ₂ : (modulesPseudofunctor.map x₁.op.toLoc).toFunctor.obj O₁ ⟶
      (modulesPseudofunctor.map x₂.op.toLoc).toFunctor.obj O₂)
    (h : pullHom ψ₁ (c.π.app j) y₁ y₂ hy₁ hy₂ = pullHom ψ₂ (c.π.app j) y₁ y₂ hy₁ hy₂) :
    ∃ (k : J) (t : k ⟶ j), pullHom ψ₁ (E.map t) (E.map t ≫ x₁) (E.map t ≫ x₂) rfl rfl =
      pullHom ψ₂ (E.map t) (E.map t ≫ x₁) (E.map t ≫ x₂) rfl rfl := by
  obtain ⟨k, t, ht⟩ := exists_pullback_map_eq_of_isLimit_of_isAffine hc
    (N₁ := (pullback x₁).obj O₁) (N₂ := (pullback x₂).obj O₂) ψ₁ ψ₂
    (map_eq_map_of_pullHom_eq _ _ _ hy₁ hy₂ h)
  exact ⟨k, t, pullHom_eq_pullHom_of_map_eq _ _ _ rfl rfl ht⟩

/-- Variant of `exists_pullHom_eq_pullHom_of_isLimit_of_isAffine` with the projection of the
limit cone replaced by an equal morphism. -/
theorem exists_pullHom_eq_pullHom_of_isLimit_of_isAffine' (hc : IsLimit c) {j : J}
    {W₁ W₂ : Scheme.{u}} {O₁ : W₁.Modules} {O₂ : W₂.Modules} [O₁.IsFinitePresentation]
    [O₂.IsFinitePresentation] (x₁ : E.obj j ⟶ W₁) (x₂ : E.obj j ⟶ W₂) {y₁ : c.pt ⟶ W₁}
    {y₂ : c.pt ⟶ W₂} (r : c.pt ⟶ E.obj j) (hr : c.π.app j = r) (hy₁ : r ≫ x₁ = y₁)
    (hy₂ : r ≫ x₂ = y₂)
    (ψ₁ ψ₂ : (modulesPseudofunctor.map x₁.op.toLoc).toFunctor.obj O₁ ⟶
      (modulesPseudofunctor.map x₂.op.toLoc).toFunctor.obj O₂)
    (h : pullHom ψ₁ r y₁ y₂ hy₁ hy₂ = pullHom ψ₂ r y₁ y₂ hy₁ hy₂) :
    ∃ (k : J) (t : k ⟶ j), pullHom ψ₁ (E.map t) (E.map t ≫ x₁) (E.map t ≫ x₂) rfl rfl =
      pullHom ψ₂ (E.map t) (E.map t ≫ x₁) (E.map t ≫ x₂) rfl rfl := by
  subst hr
  exact exists_pullHom_eq_pullHom_of_isLimit_of_isAffine hc x₁ x₂ hy₁ hy₂ ψ₁ ψ₂ h

end PullHom

end Scheme.Modules

section Stages

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {i₀ : I}

open Scheme.Modules

lemma opensCone_π_app_eq_resTo (c : Cone D) (V : (D.obj i₀).Opens) (j : Over i₀) :
    (opensCone D c i₀ V).π.app j = resTo (c.π.app j.left) (c.w j.hom) (le_refl V) := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp

lemma opensDiagram_map_eq_resTo (V : (D.obj i₀).Opens) {j k : Over i₀} (t : j ⟶ k) :
    (opensDiagram D i₀ V).map t =
      resTo (D.map t.left) (by rw [← D.map_comp, Over.w t]) (le_refl V) := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp

end Stages

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

open Scheme.Modules in
/-- **Modules of finite presentation descend to a finite stage** (Stacks, Tag 01ZR). Let `{Dⱼ}`
be a cofiltered system of quasi-compact separated schemes with affine transition morphisms and
limit cone `c`. Every module of finite presentation `ℱ` on `lim Dⱼ` is isomorphic to the pullback
of a module of finite presentation on some stage `Dᵢ`. -/
theorem Scheme.Modules.exists_isFinitePresentation_pullback_iso_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, (D.obj i).IsSeparated] (hc : IsLimit c) (ℱ : c.pt.Modules)
    [ℱ.IsFinitePresentation] :
    ∃ (i : I) (𝒢 : (D.obj i).Modules), 𝒢.IsFinitePresentation ∧
      Nonempty ((Modules.pullback (c.π.app i)).obj 𝒢 ≅ ℱ) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  -- A finite affine open cover `U` of `D.obj i₀`.
  obtain ⟨s, hs⟩ := (isCompact_univ (X := D.obj i₀)).elim_finite_subcover
    (fun V : (D.obj i₀).affineOpens ↦ ((V : (D.obj i₀).Opens) : Set (D.obj i₀)))
    (fun V ↦ V.1.2) (fun x _ ↦ by
      obtain ⟨V, hx⟩ := TopologicalSpace.Opens.mem_iSup.1
        ((iSup_affineOpens_eq_top (D.obj i₀)).ge (Set.mem_univ x) :
          x ∈ ⨆ V : (D.obj i₀).affineOpens, (V : (D.obj i₀).Opens))
      exact Set.mem_iUnion.2 ⟨V, hx⟩)
  let U (a : s) : (D.obj i₀).Opens := a.1.1
  have hU (a : s) : IsAffineOpen (U a) := a.1.2
  have hUtop : ⨆ a, U a = ⊤ := eq_top_iff.2 fun x _ ↦ by
    obtain ⟨V, hVs, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hVs⟩, hx⟩
  have hAff (V : (D.obj i₀).Opens) (hV : IsAffineOpen V) (j : Over i₀) :
      IsAffine ((opensDiagram D i₀ V).obj j) :=
    hV.preimage (D.map j.hom)
  have hU₂ (a b : s) : IsAffineOpen (U a ⊓ U b) := (hU a).inf (hU b)
  have hU₃ (a b d : s) : IsAffineOpen (U a ⊓ U b ⊓ U d) := (hU₂ a b).inf (hU d)
  -- Step 1: the restrictions of `ℱ` to the preimages of the `U a` descend.
  have h₁ (a : s) := by
    haveI := hAff (U a) (hU a)
    exact exists_pullback_iso_of_isLimit_of_isAffine (isLimitOpensCone D c hc i₀ (U a))
      ((Modules.pullback (c.π.app i₀ ⁻¹ᵁ U a).ι).obj ℱ)
  choose j N hN e using h₁
  let gL := c.π.app i₀
  let W (a : s) := (opensDiagram D i₀ (U a)).obj (j a)
  let μL (a : s) : (gL ⁻¹ᵁ U a).toScheme ⟶ W a :=
    resTo (c.π.app (j a).left) (c.w (j a).hom) (le_refl (U a))
  let ε (a : s) : (modulesPseudofunctor.map (μL a).op.toLoc).toFunctor.obj (N a) ≅
      (modulesPseudofunctor.map (gL ⁻¹ᵁ U a).ι.op.toLoc).toFunctor.obj ℱ :=
    ((Modules.pullbackCongr (opensCone_π_app_eq_resTo D c (U a) (j a))).app (N a)).symm ≪≫
      (e a).some
  let HL := DescentData'.isoGlueHom (preimageChosenPullback U gL) ε
  -- Step 2: a common stage `k₀` below the `j a`.
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let t (a : s) : k₀ ⟶ j a := (hk₀ (Finset.mem_image_of_mem j (Finset.mem_univ a))).some
  let g₀ := D.map k₀.hom
  let μ₀ (a : s) : (g₀ ⁻¹ᵁ U a).toScheme ⟶ W a :=
    resTo (D.map (t a).left) (by rw [← D.map_comp, Over.w (t a)]) (le_refl (U a))
  -- Step 3: the gluing isomorphisms descend.
  have h₃ (p : s × s) := by
    haveI := hAff (U p.1 ⊓ U p.2) (hU₂ p.1 p.2)
    haveI := hN p.1
    haveI := hN p.2
    exact exists_pullHom_eq_of_isLimit_of_isAffine (isLimitOpensCone D c hc i₀ (U p.1 ⊓ U p.2))
      (j := k₀) (O₁ := N p.1) (O₂ := N p.2)
      ((preimageChosenPullback U g₀ p.1 p.2).p₁ ≫ μ₀ p.1)
      ((preimageChosenPullback U g₀ p.1 p.2).p₂ ≫ μ₀ p.2)
      (y₁ := (preimageChosenPullback U gL p.1 p.2).p₁ ≫ μL p.1)
      (y₂ := (preimageChosenPullback U gL p.1 p.2).p₂ ≫ μL p.2)
      (by rw [opensCone_π_app_eq_resTo, ← cancel_mono (Scheme.Opens.ι _)]; simp [μ₀, μL, g₀, gL])
      (by rw [opensCone_π_app_eq_resTo, ← cancel_mono (Scheme.Opens.ι _)]; simp [μ₀, μL, g₀, gL])
      (HL p.1 p.2)
  choose k' t' ψ hψ using h₃
  -- Step 4: a common stage `k₁` below the `k' p`, over `k₀`, with the descended gluing
  -- morphisms `H₁`, whose pullbacks to the limit are `HL`.
  obtain ⟨k₁, v₁, w, hw⟩ := IsCofiltered.wideCospan t'
  have hw' (p : s × s) {Z : Scheme.{u}} (x : D.obj k₀.left ⟶ Z) :
      D.map (w p).left ≫ D.map (t' p).left ≫ x = D.map v₁.left ≫ x := by
    rw [← D.map_comp_assoc, ← Over.comp_left, hw]
  let g₁ := D.map k₁.hom
  let μ₁ (a : s) : (g₁ ⁻¹ᵁ U a).toScheme ⟶ W a :=
    resTo (D.map (v₁ ≫ t a).left) (by rw [← D.map_comp, Over.w (v₁ ≫ t a)]) (le_refl (U a))
  let H₁ (a b : s) :
      (modulesPseudofunctor.map ((preimageChosenPullback U g₁ a b).p₁ ≫ μ₁ a).op.toLoc).toFunctor.obj
        (N a) ⟶
      (modulesPseudofunctor.map ((preimageChosenPullback U g₁ a b).p₂ ≫ μ₁ b).op.toLoc).toFunctor.obj
        (N b) :=
    pullHom (ψ (a, b)) ((opensDiagram D i₀ (U a ⊓ U b)).map (w (a, b))) _ _
      (by
        rw [opensDiagram_map_eq_resTo, opensDiagram_map_eq_resTo, ← cancel_mono (Scheme.Opens.ι _)]
        simp [μ₀, μ₁, g₀, g₁, hw'])
      (by
        rw [opensDiagram_map_eq_resTo, opensDiagram_map_eq_resTo, ← cancel_mono (Scheme.Opens.ι _)]
        simp [μ₀, μ₁, g₀, g₁, hw'])
  have hμL₁ (a : s) : resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U a)) ≫ μ₁ a = μL a :=
    resTo_resTo _ _ _ _ (c.w _) _ _ _ _
  have hA : DescentData'.pullGlue (H := H₁) (sq' := preimageChosenPullback U gL)
      (fun a b ↦ resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U a ⊓ U b)))
      (resTo_p₁ U (c.π.app k₁.left) (c.w k₁.hom)) (resTo_p₂ U (c.π.app k₁.left) (c.w k₁.hom))
      hμL₁ = HL := by
    funext a b
    simp only [DescentData'.pullGlue, H₁, pullHom_pullHom]
    rw [← hψ (a, b)]
    refine pullHom_congr_left _ ?_ _ _ _ _
    rw [opensDiagram_map_eq_resTo, opensCone_π_app_eq_resTo]
    exact resTo_resTo _ _ _ _ (c.w _) _ _ _ _
  -- Step 5: the identity and cocycle conditions hold at the limit, hence at later stages.
  have hselfL : DescentData'.GlueSelf (H := HL) (preimageDiag U gL) (preimageDiag_p₁ U gL)
      (preimageDiag_p₂ U gL) :=
    DescentData'.glueSelf_isoGlueHom ε _ _ _
  have hcocL : DescentData'.GlueCocycle (preimageChosenPullback₃ U gL) HL :=
    DescentData'.glueCocycle_isoGlueHom ε
  have h₅ (a : s) := by
    haveI := hAff (U a) (hU a)
    haveI := hN a
    exact exists_pullHom_eq_pullHom_of_isLimit_of_isAffine (isLimitOpensCone D c hc i₀ (U a))
      (j := k₁) (O₁ := N a) (O₂ := N a) (μ₁ a) (μ₁ a) (y₁ := μL a) (y₂ := μL a)
      (by rw [opensCone_π_app_eq_resTo]; exact hμL₁ a)
      (by rw [opensCone_π_app_eq_resTo]; exact hμL₁ a)
      (DescentData'.glueSelfLHS H₁ (preimageDiag U g₁) (preimageDiag_p₁ U g₁)
        (preimageDiag_p₂ U g₁) a) (𝟙 _)
      (by
        rw [pullHom_congr_left _ (opensCone_π_app_eq_resTo D c (U a) k₁),
          pullHom_congr_left (𝟙 _) (opensCone_π_app_eq_resTo D c (U a) k₁),
          DescentData'.pullHom_glueSelfLHS (H := H₁) (sq' := preimageChosenPullback U gL)
            (fun a b ↦ resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U a ⊓ U b)))
            (resTo_p₁ U (c.π.app k₁.left) (c.w k₁.hom))
            (resTo_p₂ U (c.π.app k₁.left) (c.w k₁.hom)) hμL₁ (preimageDiag U gL)
            (preimageDiag_p₁ U gL) (preimageDiag_p₂ U gL)
            (preimageDiag_resTo U (c.π.app k₁.left) (c.w k₁.hom)), hA, hselfL a,
          pullHom_id_eq_id])
  choose kS tS htS using h₅
  have h₅' (q : s × s × s) := by
    haveI := hAff (U q.1 ⊓ U q.2.1 ⊓ U q.2.2) (hU₃ q.1 q.2.1 q.2.2)
    haveI := hN q.1
    haveI := hN q.2.2
    exact exists_pullHom_eq_pullHom_of_isLimit_of_isAffine'
      (isLimitOpensCone D c hc i₀ (U q.1 ⊓ U q.2.1 ⊓ U q.2.2)) (j := k₁) (O₁ := N q.1)
      (O₂ := N q.2.2) ((preimageChosenPullback₃ U g₁ q.1 q.2.1 q.2.2).p₁ ≫ μ₁ q.1)
      ((preimageChosenPullback₃ U g₁ q.1 q.2.1 q.2.2).p₃ ≫ μ₁ q.2.2)
      (y₁ := (preimageChosenPullback₃ U gL q.1 q.2.1 q.2.2).p₁ ≫ μL q.1)
      (y₂ := (preimageChosenPullback₃ U gL q.1 q.2.1 q.2.2).p₃ ≫ μL q.2.2)
      (resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U q.1 ⊓ U q.2.1 ⊓ U q.2.2)))
      (opensCone_π_app_eq_resTo D c _ k₁)
      (by rw [← cancel_mono (Scheme.Opens.ι _)]; simp [μ₁, μL, g₁, gL])
      (by rw [← cancel_mono (Scheme.Opens.ι _)]; simp [μ₁, μL, g₁, gL])
      (DescentData'.glueCocLHS (preimageChosenPullback₃ U g₁) H₁ q.1 q.2.1 q.2.2)
      (DescentData'.glueCocRHS (preimageChosenPullback₃ U g₁) H₁ q.1 q.2.1 q.2.2)
      (by
        rw [DescentData'.pullHom_glueCocLHS (H := H₁) (sq' := preimageChosenPullback U gL)
            (sq₃ := preimageChosenPullback₃ U g₁) (sq₃' := preimageChosenPullback₃ U gL)
            (r₂ := fun a b ↦ resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U a ⊓ U b)))
            (hr₂₁ := resTo_p₁ U (c.π.app k₁.left) (c.w k₁.hom))
            (hr₂₂ := resTo_p₂ U (c.π.app k₁.left) (c.w k₁.hom)) (hμ := hμL₁)
            (r₃ := fun a b d ↦
              resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U a ⊓ U b ⊓ U d)))
            (h₁₂ := resTo_p₁₂ U (c.π.app k₁.left) (c.w k₁.hom))
            (h₂₃ := resTo_p₂₃ U (c.π.app k₁.left) (c.w k₁.hom))
            (hr₃₁ := resTo_p₁' U (c.π.app k₁.left) (c.w k₁.hom))
            (hr₃₂ := resTo_p₂' U (c.π.app k₁.left) (c.w k₁.hom))
            (hr₃₃ := resTo_p₃' U (c.π.app k₁.left) (c.w k₁.hom)),
          DescentData'.pullHom_glueCocRHS (H := H₁) (sq' := preimageChosenPullback U gL)
            (sq₃ := preimageChosenPullback₃ U g₁) (sq₃' := preimageChosenPullback₃ U gL)
            (r₂ := fun a b ↦ resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U a ⊓ U b)))
            (hr₂₁ := resTo_p₁ U (c.π.app k₁.left) (c.w k₁.hom))
            (hr₂₂ := resTo_p₂ U (c.π.app k₁.left) (c.w k₁.hom)) (hμ := hμL₁)
            (r₃ := fun a b d ↦
              resTo (c.π.app k₁.left) (c.w k₁.hom) (le_refl (U a ⊓ U b ⊓ U d)))
            (h₁₃ := resTo_p₁₃ U (c.π.app k₁.left) (c.w k₁.hom))
            (hr₃₁ := resTo_p₁' U (c.π.app k₁.left) (c.w k₁.hom))
            (hr₃₃ := resTo_p₃' U (c.π.app k₁.left) (c.w k₁.hom)), hA]
        exact hcocL q.1 q.2.1 q.2.2)
  choose kC tC htC using h₅'
  -- Step 6: a common stage `k₂` below the `kS a` and the `kC q`, over `k₁`, where the identity
  -- and cocycle conditions hold.
  obtain ⟨k₂, v₂, w₂, hw₂⟩ := IsCofiltered.wideCospan (I := s ⊕ (s × s × s))
    (j := Sum.elim kS kC) (fun x ↦ match x with
      | .inl a => tS a
      | .inr q => tC q)
  let g₂ := D.map k₂.hom
  have hv₂ : D.map v₂.left ≫ g₁ = g₂ := by rw [← D.map_comp, Over.w v₂]
  let μ₂ (a : s) : (g₂ ⁻¹ᵁ U a).toScheme ⟶ W a :=
    resTo (D.map (v₂ ≫ v₁ ≫ t a).left) (by rw [← D.map_comp, Over.w (v₂ ≫ v₁ ≫ t a)])
      (le_refl (U a))
  have hμ₂₁ (a : s) : resTo (D.map v₂.left) hv₂ (le_refl (U a)) ≫ μ₁ a = μ₂ a :=
    resTo_resTo _ _ _ _ (by rw [← D.map_comp, ← Over.comp_left]) _ _ _ _
  let H₂ := DescentData'.pullGlue (H := H₁) (sq' := preimageChosenPullback U g₂)
    (fun a b ↦ resTo (D.map v₂.left) hv₂ (le_refl (U a ⊓ U b))) (resTo_p₁ U _ hv₂)
    (resTo_p₂ U _ hv₂) hμ₂₁
  have hself₂ : DescentData'.GlueSelf (H := H₂) (preimageDiag U g₂) (preimageDiag_p₁ U g₂)
      (preimageDiag_p₂ U g₂) := fun a ↦ by
    rw [← DescentData'.pullHom_glueSelfLHS (H := H₁) (sq' := preimageChosenPullback U g₂)
      (d := preimageDiag U g₁) (hd₁ := preimageDiag_p₁ U g₁) (hd₂ := preimageDiag_p₂ U g₁)
      (fun a b ↦ resTo (D.map v₂.left) hv₂ (le_refl (U a ⊓ U b))) (resTo_p₁ U _ hv₂)
      (resTo_p₂ U _ hv₂) hμ₂₁ (preimageDiag U g₂) (preimageDiag_p₁ U g₂) (preimageDiag_p₂ U g₂)
      (preimageDiag_resTo U (D.map v₂.left) hv₂)]
    have hres : resTo (D.map v₂.left) hv₂ (le_refl (U a)) =
        resTo (D.map (w₂ (.inl a)).left)
          (by rw [← D.map_comp, Over.w (w₂ (.inl a))]) (le_refl (U a)) ≫
        (opensDiagram D i₀ (U a)).map (tS a) := by
      rw [opensDiagram_map_eq_resTo]
      exact (resTo_resTo _ _ _ _ (by rw [← D.map_comp, ← Over.comp_left, ← hw₂ (.inl a)])
        _ _ _ _).symm
    rw [pullHom_congr_left _ hres, ← pullHom_pullHom (g := (opensDiagram D i₀ (U a)).map (tS a))
      (gf₁ := (opensDiagram D i₀ (U a)).map (tS a) ≫ μ₁ a)
      (gf₂ := (opensDiagram D i₀ (U a)).map (tS a) ≫ μ₁ a) (hgf₁ := rfl) (hgf₂ := rfl)
      (g'f₁ := μ₂ a) (g'f₂ := μ₂ a) (hg'f₁ := by rw [← Category.assoc, ← hres, hμ₂₁])
      (hg'f₂ := by rw [← Category.assoc, ← hres, hμ₂₁]), htS a,
      pullHom_pullHom, pullHom_id_eq_id]
  have hcoc₂ : DescentData'.GlueCocycle (preimageChosenPullback₃ U g₂) H₂ := fun a b d ↦ by
    have hres : resTo (D.map v₂.left) hv₂ (le_refl (U a ⊓ U b ⊓ U d)) =
        resTo (D.map (w₂ (.inr (a, b, d))).left)
          (by rw [← D.map_comp, Over.w (w₂ (.inr (a, b, d)))]) (le_refl (U a ⊓ U b ⊓ U d)) ≫
        (opensDiagram D i₀ (U a ⊓ U b ⊓ U d)).map (tC (a, b, d)) := by
      rw [opensDiagram_map_eq_resTo]
      exact (resTo_resTo _ _ _ _
        (by rw [← D.map_comp, ← Over.comp_left, ← hw₂ (.inr (a, b, d))]) _ _ _ _).symm
    have h := htC (a, b, d)
    dsimp only at h
    rw [← DescentData'.pullHom_glueCocLHS (H := H₁) (sq' := preimageChosenPullback U g₂)
        (sq₃ := preimageChosenPullback₃ U g₁) (sq₃' := preimageChosenPullback₃ U g₂)
        (r₂ := fun a b ↦ resTo (D.map v₂.left) hv₂ (le_refl (U a ⊓ U b)))
        (hr₂₁ := resTo_p₁ U _ hv₂) (hr₂₂ := resTo_p₂ U _ hv₂) (hμ := hμ₂₁)
        (r₃ := fun a b d ↦ resTo (D.map v₂.left) hv₂ (le_refl (U a ⊓ U b ⊓ U d)))
        (h₁₂ := resTo_p₁₂ U _ hv₂) (h₂₃ := resTo_p₂₃ U _ hv₂) (hr₃₁ := resTo_p₁' U _ hv₂)
        (hr₃₂ := resTo_p₂' U _ hv₂) (hr₃₃ := resTo_p₃' U _ hv₂),
      ← DescentData'.pullHom_glueCocRHS (H := H₁) (sq' := preimageChosenPullback U g₂)
        (sq₃ := preimageChosenPullback₃ U g₁) (sq₃' := preimageChosenPullback₃ U g₂)
        (r₂ := fun a b ↦ resTo (D.map v₂.left) hv₂ (le_refl (U a ⊓ U b)))
        (hr₂₁ := resTo_p₁ U _ hv₂) (hr₂₂ := resTo_p₂ U _ hv₂) (hμ := hμ₂₁)
        (r₃ := fun a b d ↦ resTo (D.map v₂.left) hv₂ (le_refl (U a ⊓ U b ⊓ U d)))
        (h₁₃ := resTo_p₁₃ U _ hv₂) (hr₃₁ := resTo_p₁' U _ hv₂) (hr₃₃ := resTo_p₃' U _ hv₂),
      pullHom_congr_left _ hres, pullHom_congr_left _ hres]
    have hy₁ : resTo (D.map (w₂ (.inr (a, b, d))).left)
        (by rw [← D.map_comp, Over.w (w₂ (.inr (a, b, d)))]) (le_refl (U a ⊓ U b ⊓ U d)) ≫
        ((opensDiagram D i₀ (U a ⊓ U b ⊓ U d)).map (tC (a, b, d)) ≫
          (preimageChosenPullback₃ U g₁ a b d).p₁ ≫ μ₁ a) =
        (preimageChosenPullback₃ U g₂ a b d).p₁ ≫ μ₂ a := by
      rw [← Category.assoc, ← hres, ← hμ₂₁, ← Category.assoc, ← Category.assoc,
        resTo_p₁' U _ hv₂]
    have hy₃ : resTo (D.map (w₂ (.inr (a, b, d))).left)
        (by rw [← D.map_comp, Over.w (w₂ (.inr (a, b, d)))]) (le_refl (U a ⊓ U b ⊓ U d)) ≫
        ((opensDiagram D i₀ (U a ⊓ U b ⊓ U d)).map (tC (a, b, d)) ≫
          (preimageChosenPullback₃ U g₁ a b d).p₃ ≫ μ₁ d) =
        (preimageChosenPullback₃ U g₂ a b d).p₃ ≫ μ₂ d := by
      rw [← Category.assoc, ← hres, ← hμ₂₁, ← Category.assoc, ← Category.assoc,
        resTo_p₃' U _ hv₂]
    rw [← pullHom_pullHom (g := (opensDiagram D i₀ (U a ⊓ U b ⊓ U d)).map (tC (a, b, d)))
        (hgf₁ := rfl) (hgf₂ := rfl) (hg'f₁ := hy₁) (hg'f₂ := hy₃),
      ← pullHom_pullHom (g := (opensDiagram D i₀ (U a ⊓ U b ⊓ U d)).map (tC (a, b, d)))
        (hgf₁ := rfl) (hgf₂ := rfl) (hg'f₁ := hy₁) (hg'f₂ := hy₃), h]
  sorry

end AlgebraicGeometry
