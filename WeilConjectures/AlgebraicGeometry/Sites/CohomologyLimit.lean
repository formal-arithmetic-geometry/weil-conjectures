/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.HypercoverDescent

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

section Restrict

open SemiSimplicialObject

variable {Λ} {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) (g : Y ⟶ Z) (hg : g ≫ pZ = pY)
  {V : SemiSimplicialObject Z.Etale} {U : SemiSimplicialObject Y.Etale}
  (φ : U ⟶ V.baseChange g)

/-- The projection `U_n ⟶ V_n` underlying a morphism `φ : U ⟶ V ×_Z Y` of semi-simplicial étale
schemes. -/
noncomputable abbrev baseChangeProj (n : ℕ) : (U.obj n).left ⟶ (V.obj n).left :=
  (φ.app n).left ≫ pullback.fst (V.obj n).hom g

include φ in
lemma baseChangeProj_w (n : ℕ) :
    baseChangeProj g φ n ≫ (V.obj n).hom = (U.obj n).hom ≫ g := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact MorphismProperty.Over.w (φ.app n)

@[reassoc]
lemma _root_.CategoryTheory.SemiSimplicialObject.baseChange_δ_left_fst (n : ℕ) (i : Fin (n + 2)) :
    ((V.baseChange g).δ n i).left ≫ pullback.fst (V.obj n).hom g =
      pullback.fst (V.obj (n + 1)).hom g ≫ (V.δ n i).left :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma _root_.CategoryTheory.SemiSimplicialObject.baseChange_δ_left_snd (n : ℕ) (i : Fin (n + 2)) :
    ((V.baseChange g).δ n i).left ≫ pullback.snd (V.obj n).hom g =
      pullback.snd (V.obj (n + 1)).hom g :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma baseChangeProj_δ (n : ℕ) (i : Fin (n + 2)) :
    baseChangeProj g φ (n + 1) ≫ (V.δ n i).left = (U.δ n i).left ≫ baseChangeProj g φ n := by
  have h : (φ.app (n + 1) ≫ (V.baseChange g).δ n i).left ≫ pullback.fst (V.obj n).hom g =
      (U.δ n i ≫ φ.app n).left ≫ pullback.fst (V.obj n).hom g := by rw [φ.app_δ]
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
    Category.assoc, baseChange_δ_left_fst] at h
  simpa only [baseChangeProj, Category.assoc] using h

/-- For a factorisation `g = g' ≫ h`, a morphism `U ⟶ V ×_Z Y` induces a morphism
`U ⟶ (V ×_Z Z') ×_{Z'} Y`. -/
noncomputable def baseChangeLift {Z' : Scheme.{u}} (g' : Y ⟶ Z') (h : Z' ⟶ Z) (hgh : g' ≫ h = g) :
    U ⟶ (V.baseChange h).baseChange g' where
  app n := homToPullback g' (pullback.lift (baseChangeProj g φ n) ((U.obj n).hom ≫ g')
      (by rw [baseChangeProj_w, Category.assoc, hgh]))
    (pullback.lift_snd _ _ _)
  app_δ n i := by
    apply hom_ext_pullback
    apply pullback.hom_ext
    · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
        Category.assoc, Category.assoc, Category.assoc, baseChange_δ_left_fst_assoc,
        homToPullback_left_fst_assoc, homToPullback_left_fst_assoc, baseChange_δ_left_fst,
        pullback.lift_fst_assoc, pullback.lift_fst]
      exact baseChangeProj_δ g φ n i
    · rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
        Category.assoc, Category.assoc, Category.assoc, baseChange_δ_left_fst_assoc,
        homToPullback_left_fst_assoc, homToPullback_left_fst_assoc, pullback.lift_snd,
        baseChange_δ_left_snd, pullback.lift_snd, ← Category.assoc, MorphismProperty.Over.w]

lemma baseChangeProj_baseChangeLift {Z' : Scheme.{u}} (g' : Y ⟶ Z') (h : Z' ⟶ Z)
    (hgh : g' ≫ h = g) (n : ℕ) :
    baseChangeProj g' (baseChangeLift g φ g' h hgh) n ≫ pullback.fst (V.obj n).hom h =
      baseChangeProj g φ n := by
  simp [baseChangeLift, baseChangeProj]

variable (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- Restriction of sections of `pZ^* F` over `V_n` to sections of `pY^* F` over `U_n` along a
morphism `φ : U ⟶ V ×_Z Y`. -/
noncomputable abbrev restrictAlongBaseChange (n : ℕ) :
    ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj n)) ⟶
      ((pY)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (U.obj n)) :=
  ModuleSheaf.restrictAlong pZ F g pY hg.symm (baseChangeProj g φ n) (baseChangeProj_w g φ n)

lemma cochainDifferential_restrictAlongBaseChange (n : ℕ)
    (s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj n))) :
    (U.cochainDifferential ((pY)^*[ModuleCat.{u + 1} Λ].obj F).obj n).hom
        (restrictAlongBaseChange pY pZ g hg φ F n s) =
      restrictAlongBaseChange pY pZ g hg φ F (n + 1)
        ((V.cochainDifferential ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj n).hom s) := by
  simp only [cochainDifferential, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  rw [ModuleSheaf.map_restrictAlong, ModuleSheaf.restrictAlong_map]
  exact congrArg (fun r ↦ r s)
    (ModuleSheaf.restrictAlong_congr pZ F g pY hg.symm _ (baseChangeProj_δ g φ n i).symm)

lemma _root_.CategoryTheory.SemiSimplicialObject.IsCocycle.restrictAlongBaseChange {q : ℕ}
    {s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj q))}
    (hs : V.IsCocycle ((pZ)^*[ModuleCat.{u + 1} Λ].obj F) q s) :
    U.IsCocycle ((pY)^*[ModuleCat.{u + 1} Λ].obj F) q
      (restrictAlongBaseChange pY pZ g hg φ F q s) := by
  rw [IsCocycle, cochainDifferential_restrictAlongBaseChange, hs, map_zero]

/-- **Base change of hypercover classes**: for a morphism `g : Y ⟶ Z` over `S`, hypercovers `V`
of `Z` and `U` of `Y` and a morphism `φ : U ⟶ V ×_Z Y`, the restriction to `Y` of the class of a
cocycle `s` on `V` is the class of the restriction of `s` along `φ`. -/
theorem cohomologyRestrictOver_cohomologyClass (hV : V.IsHypercover Z.smallEtaleTopology)
    (hU : U.IsHypercover Y.smallEtaleTopology) (q : ℕ)
    (s : ((pZ)^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (V.obj q)))
    (hs : V.IsCocycle ((pZ)^*[ModuleCat.{u + 1} Λ].obj F) q s) :
    cohomologyRestrictOver Λ pY pZ g hg F q (hV.cohomologyClass _ q s hs) =
      hU.cohomologyClass _ q (restrictAlongBaseChange pY pZ g hg φ F q s)
        (hs.restrictAlongBaseChange pY pZ g hg φ F) := by
  let ψ := (Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F
  have h₁ : cohomologyRestrictOver Λ pY pZ g hg F q (hV.cohomologyClass _ q s hs) =
      (Etale.cohomologyRestrict Λ g _ q (hV.cohomologyClass _ q s hs)).comp (Ext.mk₀ ψ)
        (add_zero q) := rfl
  rw [h₁, Etale.cohomologyRestrict_cohomologyClass, ← IsHypercover.cohomologyClass_map,
    ← IsHypercover.cohomologyClass_restrict _ hU φ]
  refine IsHypercover.cohomologyClass_congr _ _ _ ?_ _ _
  simp only [restrictAlongBaseChange, ModuleSheaf.restrictAlong, ModuleSheaf.transition]
  have : homToPullback g (baseChangeProj g φ q) (baseChangeProj_w g φ q) =
      φ.app q := by
    apply hom_ext_pullback
    simp
  rw [this]
  rfl

end Restrict

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
  classical
  let D' := D ⋙ Over.forget S
  let c' := (Over.forget S).mapCone c
  let π : D' ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality _ _ f := by simp [D'] }
  have hP (j : I) : c.pt.hom = c'.π.app j ≫ π.app j := (Over.w (c.π.app j)).symm
  have : ∀ i, CompactSpace (D'.obj i) := fun i ↦ inferInstanceAs (CompactSpace (D.obj i).left)
  have : ∀ i, QuasiSeparatedSpace (D'.obj i) := fun i ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D'.map f) := fun f ↦
    inferInstanceAs (IsAffineHom (D.map f).left)
  have : CompactSpace c.pt.left := Scheme.compactSpace_of_isLimit D' c' hc
  have : QuasiSeparatedSpace c.pt.left := quasiSeparatedSpace_pt hc
  -- a class on the limit is the class of a cocycle on a qcqs hypercover `U`
  obtain ⟨U, hU, z, hz, rfl⟩ := Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover Λ _ q x
  -- the truncation of `U` in degrees `≤ q + 1` descends to a stage
  obtain ⟨k, ⟨d⟩⟩ := exists_truncatedDescent hc U
    (fun n ↦ ⟨hU.compactSpace n, hU.quasiSeparatedSpace n⟩) (q + 1)
  obtain ⟨k₀, f₀, hk₀⟩ := d.exists_isHypercover hc hU.isHypercover
  have hq : q ≤ q + 1 := Nat.le_succ q
  obtain ⟨_, _⟩ := d.qcqs q hq
  -- the cocycle descends to a stage
  obtain ⟨K, h, hK⟩ := ModuleSheaf.exists_restrictAlong_eq_of_isLimit hc π c.pt.hom hP F
    (d.T.obj q hq) (d.m q hq) (d.isPullback q hq) z
  obtain ⟨k', a, b, hab⟩ := IsCofiltered.cospan h f₀
  let d' := d.baseChange (b ≫ f₀)
  let V := d'.T.cosk
  have hV : V.IsHypercover (D'.obj k').smallEtaleTopology := hk₀ k' b
  let m' : (V.obj q).left ⟶ (d.T.obj q hq).left :=
    (d'.T.coskIso q hq).hom.left ≫ pullback.fst _ _
  have hm' : m' ≫ (d.T.obj q hq).hom = (V.obj q).hom ≫ D'.map (a ≫ h) := by
    have := MorphismProperty.Over.w (d'.T.coskIso q hq).hom
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      show (d'.T.coskIso q hq).hom.left ≫ pullback.snd _ _ = (V.obj q).hom from this, hab]
  have hnm : baseChangeProj (c'.π.app k') d'.toCosk q ≫ m' = d.m q hq := by
    simp only [baseChangeProj, m', Category.assoc]
    rw [← Category.assoc (d'.toCosk.app q).left, d'.toCosk_app_left_fst q hq, Category.assoc,
      ← Category.assoc (d'.T.coskIso q hq).inv.left, Scheme.Etale.inv_hom_id_left,
      Category.id_comp]
    exact pullback.lift_fst _ _ _
  obtain ⟨s, hs⟩ := hK a (V.obj q) m' hm' _ (baseChangeProj_w (c'.π.app k') d'.toCosk q) hnm
  -- the cocycle condition descends to a later stage
  let ds := (V.cochainDifferential ((π.app k')^*[ModuleCat.{u + 1} Λ].obj F).obj q).hom s
  have hds : restrictAlongBaseChange c.pt.hom (π.app k') (c'.π.app k') (hP k').symm d'.toCosk F
      (q + 1) ds = 0 := by
    rw [← cochainDifferential_restrictAlongBaseChange]
    exact (congrArg _ hs).trans hz
  obtain ⟨_, _⟩ : Scheme.Etale.qcqs _ (V.obj (q + 1)) :=
    (Scheme.Etale.qcqs _).prop_of_iso (d'.T.coskIso (q + 1) le_rfl).symm (d'.qcqs (q + 1) le_rfl)
  have hpb : IsPullback (baseChangeProj (c'.π.app k') d'.toCosk (q + 1)) (U.obj (q + 1)).hom
      (V.obj (q + 1)).hom (c'.π.app k') := by
    have := d'.isIso_toCosk_app (q + 1) le_rfl
    refine IsPullback.of_iso_pullback ⟨baseChangeProj_w _ _ _⟩
      (Scheme.Etale.leftIso (asIso (d'.toCosk.app (q + 1)))) rfl ?_
    exact MorphismProperty.Over.w (d'.toCosk.app (q + 1))
  obtain ⟨k'', f'', hk''⟩ := ModuleSheaf.exists_restrictAlong_eq_zero_of_isLimit hc π c.pt.hom
    hP F (V.obj (q + 1)) _ hpb ds hds
  let W := V.baseChange (D'.map f'')
  have hW : W.IsHypercover (D'.obj k'').smallEtaleTopology := hV.baseChange _
  have hπ : D'.map f'' ≫ π.app k' = π.app k'' := π.naturality f'' |>.trans (Category.comp_id _)
  let s'' := restrictAlongBaseChange (π.app k'') (π.app k') (D'.map f'') hπ (𝟙 W) F q s
  have hs'' : W.IsCocycle _ q s'' := by
    rw [SemiSimplicialObject.IsCocycle, cochainDifferential_restrictAlongBaseChange]
    exact hk'' (𝟙 _) f'' (Category.id_comp _) _ _ _
  refine ⟨k'', hW.cohomologyClass _ q s'' hs'', ?_⟩
  have hgh : c'.π.app k'' ≫ D'.map f'' = c'.π.app k' := c'.w f''
  refine (cohomologyRestrictOver_cohomologyClass c.pt.hom (π.app k'') (c'.π.app k'') (Over.w _)
    (baseChangeLift (c'.π.app k') d'.toCosk (c'.π.app k'') (D'.map f'') hgh) F hW hU.isHypercover
    q s'' hs'').trans ?_
  apply SemiSimplicialObject.IsHypercover.cohomologyClass_congr
  rw [← hs]
  simp only [restrictAlongBaseChange, s'']
  rw [ModuleSheaf.restrictAlong_restrictAlong,
    ModuleSheaf.restrictAlong_congr_hom F (π.app k') c.pt.hom _ hgh]
  have hm : baseChangeProj (c'.π.app k'')
      (baseChangeLift (c'.π.app k') d'.toCosk (c'.π.app k'') (D'.map f'') hgh) q ≫
        baseChangeProj (D'.map f'') (𝟙 W) q = baseChangeProj (c'.π.app k') d'.toCosk q := by
    simpa [baseChangeProj] using baseChangeProj_baseChangeLift (c'.π.app k') d'.toCosk
      (c'.π.app k'') (D'.map f'') hgh q
  rw [ModuleSheaf.restrictAlong_congr _ _ _ _ _ _ hm]

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
