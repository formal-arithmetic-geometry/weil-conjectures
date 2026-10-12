/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimitAux

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf of `Λ`-modules on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ], blueprint
`lemma-weil-pbc-etale-cohomology-continuity`). For `Λ = ℤ` these are abelian étale sheaves; no
torsion hypothesis is needed.

The statement is spelled out elementwise
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`,
`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_zero_of_isLimit`): every class on `X`
comes from some `Xᵢ`, and a class on `Xᵢ` which dies on `X` dies on some `Xⱼ`.

The proof follows the blueprint: a class on `X` is the class of a cocycle on a qcqs hypercover of
`X` (`AlgebraicGeometry.Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover`); the truncation of
the hypercover in degrees `≤ q + 1` descends to some `Xᵢ`
(blueprint `lemma-weil-pbc-finite-hypercover-descent`), and so do the cocycle and the cocycle
condition by continuity of sections (blueprint `lem-weil-pbc-etale-section-continuity`). For
injectivity one descends in the same way a refinement on which the cocycle becomes a coboundary
(`AlgebraicGeometry.Scheme.exists_isCoboundary_of_isQcqsHypercover`), the refinement map and the
primitive.

## Main definitions

- `AlgebraicGeometry.Etale.cohomologyRestrictOver`: for a morphism `f : Y ⟶ Z` of schemes over
  `S`, the restriction map `Hᵠ(Z, F|_Z) ⟶ Hᵠ(Y, F|_Y)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}}

/-- For a morphism `f : Y ⟶ Z` of schemes over `S` (with structure maps `pY`, `pZ`), the
restriction map `Hᵠ(Z, F|_Z) ⟶ Hᵠ(Y, F|_Y)` of the étale cohomology of the pullbacks of a sheaf
`F` on `S`: pullback along `f` followed by the identification `f^* (pZ^* F) ≅ pY^* F`. -/
noncomputable def cohomologyRestrictOver {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ pZ = pY) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    Ext (SemiSimplicialObject.constSheaf Z.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pZ).obj F) q →+
      Ext (SemiSimplicialObject.constSheaf Y.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F) q :=
  (Ext.mk₀ ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm).inv.app F)).postcomp _
      (add_zero q) |>.comp (Etale.cohomologyRestrict Λ f _ q)

/-- **Restriction of classes of hypercover cocycles.** Let `g : Y ⟶ Z` be a morphism over `S`,
`s` a `q`-cocycle of `F|_Z` on a hypercover `H` of `Z`, and `U` a hypercover of `Y` with morphisms
`μ_n : U_n ⟶ H_n` over `g` (`n ≤ q`) commuting with the face maps. Then the restriction to `Y` of
the class of `s` is the class of the restriction of `s` along `μ_q`. -/
theorem cohomologyRestrictOver_cohomologyClass {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (g : Y ⟶ Z) (hg : g ≫ pZ = pY) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) {H : SemiSimplicialObject Z.Etale} (hH : H.IsHypercover Z.smallEtaleTopology)
    (s : ((Etale.upperStar (ModuleCat.{u + 1} Λ) pZ).obj F).obj.obj (op (H.obj q)))
    (hs : H.IsCocycle _ q s) {U : SemiSimplicialObject Y.Etale}
    (hU : U.IsHypercover Y.smallEtaleTopology) (μ : ∀ n, n ≤ q → ((U.obj n).left ⟶ (H.obj n).left))
    (hμ : ∀ n (h : n ≤ q), μ n h ≫ (H.obj n).hom = (U.obj n).hom ≫ g)
    (hμδ : ∀ n (h : n < q) (i : Fin (n + 2)),
      (U.δ n i).left ≫ μ n h.le = μ (n + 1) h ≫ (H.δ n i).left)
    (hs' : U.IsCocycle _ q
      (Etale.ModuleSheaf.restrictAlong pZ F g pY hg.symm (μ q le_rfl) (hμ q le_rfl) s)) :
    cohomologyRestrictOver Λ pY pZ g hg F q (hH.cohomologyClass _ q s hs) =
      hU.cohomologyClass _ q _ hs' := by
  let f (n : ℕ) (h : n ≤ q) : U.obj n ⟶ (H.baseChange g).obj n :=
    Etale.homToPullback g (μ n h) (hμ n h)
  have hf (n : ℕ) (h : n < q) (i : Fin (n + 2)) :
      f (n + 1) h ≫ (H.baseChange g).δ n i = U.δ n i ≫ f n h.le :=
    Etale.hom_ext_pullback _ (by simpa [f] using (hμδ n h i).symm)
  have key : Etale.ModuleSheaf.restrictAlong pZ F g pY hg.symm (μ q le_rfl) (hμ q le_rfl) s =
      (((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F).obj.map (f q le_rfl).op).hom
        (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F).hom.app _
          (Etale.pullbackSection Λ g _ (H.obj q) s)) := by
    exact Etale.ModuleSheaf.restrictAlong_comp_fst_eq pZ F g pY hg.symm (f q le_rfl) _ _
      (Etale.homToPullback_left_fst g (μ q le_rfl) (hμ q le_rfl)) s
  have hw : (H.baseChange g).IsCocycle ((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F) q
      (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F).hom.app _
        (Etale.pullbackSection Λ g _ (H.obj q) s)) :=
    SemiSimplicialObject.IsCocycle.map _
      (hs.map ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _))
  rw [hU.cohomologyClass_congr _ q key hs' (key ▸ hs'),
    (hH.baseChange g).cohomologyClass_restrict_of_le hU q f hf _ _ hw]
  refine Eq.trans ?_ ((hH.baseChange g).cohomologyClass_map
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F) q _
    (hs.map ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _))).symm
  change (Etale.cohomologyRestrict Λ g _ q (hH.cohomologyClass _ q s hs)).comp (Ext.mk₀ _)
    (add_zero q) = _
  rw [Etale.cohomologyRestrict_cohomologyClass]
  rfl


section SchemeDiagram

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)
  (π : D ⟶ (Functor.const I).obj S) (P : c.pt ⟶ S) (hP : ∀ i, P = c.π.app i ≫ π.app i)
  (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))

open SemiSimplicialObject

include hc in
/-- **Continuity of étale cohomology, surjectivity**, for a cofiltered diagram of schemes `Dᵢ`
over `S` with limit `X`: every cohomology class of the pullback of `F` to `X` comes from some
`Dᵢ`. -/
theorem exists_cohomologyRestrictOver_eq_of_isLimit_of_scheme (q : ℕ)
    (x : Ext (constSheaf c.pt.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) P).obj F) q) :
    ∃ (i : I) (y : Ext (constSheaf (D.obj i).smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (π.app i)).obj F) q),
      cohomologyRestrictOver Λ P (π.app i) (c.π.app i) (hP i).symm F q y = x := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_pt hc
  obtain ⟨U, hU, z, hz, rfl⟩ := Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover Λ _ q x
  obtain ⟨k, ⟨d⟩⟩ := exists_truncatedDescent hc U
    (fun n ↦ ⟨hU.compactSpace n, hU.quasiSeparatedSpace n⟩) (q + 1)
  obtain ⟨k₀, f₀, hhyp⟩ := d.exists_isHypercover hc hU.isHypercover
  -- the cocycle descends to a section at a stage
  obtain ⟨_, _⟩ := (d.baseChange (𝟙 k)).qcqs_cosk q (by omega)
  obtain ⟨K, h, hK⟩ := ModuleSheaf.exists_restrictAlong_eq_of_isLimit hc π P hP F
    ((d.baseChange (𝟙 k)).T.cosk.obj q) ((d.baseChange (𝟙 k)).toCoskLeft q (by omega))
    ((d.baseChange (𝟙 k)).isPullback_toCoskLeft q (by omega)) z
  obtain ⟨k₁, a₁, b₁, hab⟩ := IsCofiltered.cospan h f₀
  obtain ⟨s₁, hs₁⟩ := hK a₁ ((d.baseChange (a₁ ≫ h)).T.cosk.obj q)
    (d.coskTransition (𝟙 k) (a₁ ≫ h) (a₁ ≫ h) (Category.comp_id _) q (by omega))
    (by rw [d.coskTransition_hom])
    ((d.baseChange (a₁ ≫ h)).toCoskLeft q (by omega))
    ((d.baseChange (a₁ ≫ h)).toCoskLeft_hom q (by omega))
    (d.toCoskLeft_coskTransition _ _ _ _ q (by omega))
  -- the cocycle condition holds at a later stage
  have hσ : ModuleSheaf.restrictAlong (π.app k₁) F (c.π.app k₁) P (hP k₁)
      ((d.baseChange (a₁ ≫ h)).toCoskLeft (q + 1) le_rfl)
      ((d.baseChange (a₁ ≫ h)).toCoskLeft_hom (q + 1) le_rfl)
      (((d.baseChange (a₁ ≫ h)).T.cosk.cochainDifferential
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (π.app k₁)).obj F).obj q).hom s₁) = 0 := by
    rw [← ModuleSheaf.cochainDifferential_restrictAlong (π.app k₁) F (c.π.app k₁) P (hP k₁)
      (A := U) (B := (d.baseChange (a₁ ≫ h)).T.cosk) q
      ((d.baseChange (a₁ ≫ h)).toCoskLeft q (by omega))
      ((d.baseChange (a₁ ≫ h)).toCoskLeft_hom q (by omega))
      ((d.baseChange (a₁ ≫ h)).toCoskLeft (q + 1) le_rfl)
      ((d.baseChange (a₁ ≫ h)).toCoskLeft_hom (q + 1) le_rfl)
      (fun i ↦ (d.baseChange (a₁ ≫ h)).toCoskLeft_δ q (Nat.lt_succ_self q) i), hs₁]
    exact hz
  obtain ⟨_, _⟩ := (d.baseChange (a₁ ≫ h)).qcqs_cosk (q + 1) le_rfl
  obtain ⟨K₂, g₂, hK₂⟩ := ModuleSheaf.exists_restrictAlong_eq_zero_of_isLimit hc π P hP F
    ((d.baseChange (a₁ ≫ h)).T.cosk.obj (q + 1))
    ((d.baseChange (a₁ ≫ h)).toCoskLeft (q + 1) le_rfl)
    ((d.baseChange (a₁ ≫ h)).isPullback_toCoskLeft (q + 1) le_rfl) _ hσ
  -- the hypercover and the cocycle at the stage `K₂`
  have hH : (d.baseChange (g₂ ≫ a₁ ≫ h)).T.cosk.IsHypercover (D.obj K₂).smallEtaleTopology := by
    have H := hhyp K₂ (g₂ ≫ b₁)
    rwa [Category.assoc, ← hab] at H
  let tr := d.coskTransition (a₁ ≫ h) g₂ (g₂ ≫ a₁ ≫ h) rfl
  let s₂ := ModuleSheaf.restrictAlong (π.app k₁) F (D.map g₂) (π.app K₂)
    (Etale.app_eq_map_comp_app π g₂)
    (tr q (by omega)) (d.coskTransition_hom _ _ _ _ q (by omega)) s₁
  have hs₂ : (d.baseChange (g₂ ≫ a₁ ≫ h)).T.cosk.IsCocycle _ q s₂ := by
    rw [IsCocycle, ModuleSheaf.cochainDifferential_restrictAlong (π.app k₁) F (D.map g₂)
      (π.app K₂) (Etale.app_eq_map_comp_app π g₂) (A := (d.baseChange (g₂ ≫ a₁ ≫ h)).T.cosk)
      (B := (d.baseChange (a₁ ≫ h)).T.cosk) q (tr q (by omega))
      (d.coskTransition_hom _ _ _ _ q (by omega)) (tr (q + 1) le_rfl)
      (d.coskTransition_hom _ _ _ _ (q + 1) le_rfl)
      (fun i ↦ d.coskTransition_δ _ _ _ _ q (by omega) i)]
    exact hK₂ (𝟙 _) g₂ (Category.id_comp _) _ _ _
  have hres : ModuleSheaf.restrictAlong (π.app K₂) F (c.π.app K₂) P (hP K₂)
      ((d.baseChange (g₂ ≫ a₁ ≫ h)).toCoskLeft q (by omega))
      ((d.baseChange (g₂ ≫ a₁ ≫ h)).toCoskLeft_hom q (by omega)) s₂ = z := by
    rw [ModuleSheaf.restrictAlong_restrictAlong,
      ModuleSheaf.restrictAlong_congr_hom F _ _ _ (c.w g₂),
      ModuleSheaf.restrictAlong_congr _ _ _ _ _ _
        (d.toCoskLeft_coskTransition _ _ _ _ q (by omega))]
    exact hs₁
  refine ⟨K₂, hH.cohomologyClass _ q s₂ hs₂, ?_⟩
  rw [cohomologyRestrictOver_cohomologyClass Λ P (π.app K₂) (c.π.app K₂) (hP K₂).symm F q hH s₂
    hs₂ hU.isHypercover (fun n _ ↦ (d.baseChange (g₂ ≫ a₁ ≫ h)).toCoskLeft n (by omega))
    (fun n _ ↦ (d.baseChange (g₂ ≫ a₁ ≫ h)).toCoskLeft_hom n (by omega))
    (fun n hn i ↦ (d.baseChange (g₂ ≫ a₁ ≫ h)).toCoskLeft_δ n (by omega) i) (hres ▸ hz)]
  exact hU.isHypercover.cohomologyClass_congr _ q hres _ _

end SchemeDiagram
/-- The structure morphisms `Dᵢ ⟶ S` of a diagram of schemes over `S`, as a natural
transformation from the underlying diagram of schemes to the constant diagram. -/
@[simps]
def _root_.CategoryTheory.Over.forgetπ {I : Type*} [Category* I] (D : I ⥤ Over S) :
    D ⋙ Over.forget S ⟶ (Functor.const I).obj S where
  app i := (D.obj i).hom
  naturality _ _ f := by simp

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
  (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
  (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))

include hc

/-- **Continuity of étale cohomology, surjectivity** (blueprint
`lemma-weil-pbc-etale-cohomology-continuity`): every cohomology class of the pullback of `F` to
the limit `X = lim Xᵢ` comes from some `Xᵢ`. -/
@[stacks 09YQ]
theorem exists_cohomologyRestrictOver_eq_of_isLimit (q : ℕ)
    (x : Ext (SemiSimplicialObject.constSheaf c.pt.left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) c.pt.hom).obj F) q) :
    ∃ (i : I) (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q),
      cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = x := by
  have (i : I) : CompactSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (f : i ⟶ j) : IsAffineHom ((D ⋙ Over.forget S).map f) :=
    inferInstanceAs (IsAffineHom (D.map f).left)
  exact exists_cohomologyRestrictOver_eq_of_isLimit_of_scheme Λ hc (Over.forgetπ D) c.pt.hom
    (fun i ↦ (Over.w (c.π.app i)).symm) F q x

/-- **Continuity of étale cohomology, injectivity** (blueprint
`lemma-weil-pbc-etale-cohomology-continuity`): a cohomology class of the pullback of `F` to some
`Xᵢ` which vanishes on the limit `X = lim Xᵢ` vanishes on some `Xⱼ`, `j ⟶ i`. -/
@[stacks 09YQ]
theorem exists_cohomologyRestrictOver_eq_zero_of_isLimit (q : ℕ) (i : I)
    (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q)
    (hy : cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = 0) :
    ∃ (j : I) (φ : j ⟶ i),
      cohomologyRestrictOver Λ (D.obj j).hom (D.obj i).hom (D.map φ).left (Over.w _) F q y = 0 :=
  sorry

end AlgebraicGeometry.Etale
