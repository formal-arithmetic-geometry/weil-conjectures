/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuityAcyclic
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePullbackSections
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.CategoryTheory.Abelian.ExtCofilteredLimit

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ]). This is blueprint
`lemma-weil-pbc-etale-cohomology-continuity`, which belongs to the subsection `sk-prop-h2`; its
proof is not formalised here. It is recorded in the form in which it is used: if all the
`H^q(Xᵢ, F|_{Xᵢ})` vanish, so does `H^q(X, F|_X)`.

## Main definitions

- `AlgebraicGeometry.Etale.sectionsFunctor`: the global sections functor of the small étale
  site, the sections over the terminal object.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The global sections functor `Γ(X, -)` on étale sheaves: the sections over the terminal
object `X` of the small étale site. -/
noncomputable abbrev sectionsFunctor (X : Scheme.{u}) : Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf _ A ⋙
    (evaluation _ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))

/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Dᵢ, F|_{Dᵢ})`; in particular `H^q(X, F|_X)` vanishes as soon as all
the `H^q(Dᵢ, F|_{Dᵢ})` do. -/
theorem isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (h : ∀ i, IsZero (((sectionsFunctor A (D.obj i).left).rightDerived q).obj
      ((Etale.upperStar A (D.obj i).hom).obj F))) :
    IsZero (((sectionsFunctor A c.pt.left).rightDerived q).obj
      ((Etale.upperStar A c.pt.hom).obj F)) :=
  sorry


end AlgebraicGeometry.Etale

/-! ### Continuity of étale cohomology for abelian sheaves -/

namespace AlgebraicGeometry.Etale

section FreeSheaf

variable (X : Scheme.{u})

/-- The free abelian sheaf `ℤ[W]` on an étale `X`-scheme `W`: the sheafification of the presheaf
`V ↦ ℤ^{(Hom_X(V, W))}`. It corepresents sections over `W`
(`AlgebraicGeometry.Etale.freeAbSheafHomEquiv`), so that `Extᵠ(ℤ[W], F)` is the étale
cohomology `Hᵠ(W, F|_W)`. -/
noncomputable def freeAbSheaf : X.Etale ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf _ _

variable {X}

/-- The free abelian sheaf `ℤ[W]` corepresents sections over `W`. -/
noncomputable def freeAbSheafHomEquiv (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((freeAbSheaf X).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans <|
    ((AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

lemma freeAbSheafHomEquiv_comp (W : X.Etale)
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : (freeAbSheaf X).obj W ⟶ G)
    (ψ : G ⟶ G') :
    freeAbSheafHomEquiv W G' (f ≫ ψ) = ψ.hom.app (op W) (freeAbSheafHomEquiv W G f) := by
  simp only [freeAbSheafHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right,
    uliftYonedaEquiv_comp]
  rfl

set_option maxHeartbeats 1000000 in
lemma freeAbSheafHomEquiv_map {W W' : X.Etale} (a : W' ⟶ W)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : (freeAbSheaf X).obj W ⟶ G) :
    freeAbSheafHomEquiv W' G ((freeAbSheaf X).map a ≫ f) =
      G.obj.map a.op (freeAbSheafHomEquiv W G f) := by
  have h : (freeAbSheaf X).map a = (presheafToSheaf _ _).map
      (Functor.whiskerRight (uliftYoneda.{u + 1}.map a) AddCommGrpCat.free) := rfl
  rw [h]
  simp only [freeAbSheafHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ a.op).symm

/-- The generator of `ℤ[W]`: the section over `W` corresponding to `𝟙 ℤ[W]`. -/
noncomputable def freeAbSheafGenerator (W : X.Etale) : ((freeAbSheaf X).obj W).obj.obj (op W) :=
  freeAbSheafHomEquiv W _ (𝟙 _)

lemma freeAbSheafHomEquiv_eq (W : X.Etale)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : (freeAbSheaf X).obj W ⟶ G) :
    freeAbSheafHomEquiv W G f = f.hom.app (op W) (freeAbSheafGenerator W) := by
  rw [freeAbSheafGenerator, ← freeAbSheafHomEquiv_comp, Category.id_comp]

end FreeSheaf

section Continuity

variable {S : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
  [∀ i, AlgebraicGeometry.Etale (D.obj i).hom]

/-- The stages of a system of étale `S`-schemes, as objects of the small étale site of `S`. -/
@[simps]
noncomputable def stageEtale : I ⥤ S.Etale where
  obj i := Scheme.Etale.mk (D.obj i).hom
  map g := MorphismProperty.Over.homMk (D.map g).left (Over.w (D.map g))
  map_id i := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg CommaMorphism.left (D.map_id i)
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    simp

variable (c : Cone D)

/-- The terminal object `S ×_S X` of the small étale site of the limit `X`. -/
noncomputable abbrev limitTerminal : c.pt.left.Etale :=
  (c.pt.hom).Etale.obj (Scheme.Etale.mk (𝟙 S))

/-- The base change of `S` is terminal. -/
noncomputable def isTerminal_limitTerminal : IsTerminal (limitTerminal D c) :=
  IsTerminal.isTerminalObj _ _ (MorphismProperty.Over.mkIdTerminal _ S)

/-- The projection `S ×_S X ⟶ Dᵢ`. -/
noncomputable abbrev limitTerminalToStage (i : I) :
    (limitTerminal D c).left ⟶ ((stageEtale D).obj i).left :=
  pullback.snd (𝟙 S) c.pt.hom ≫ (c.π.app i).left

lemma limitTerminalToStage_comp (i : I) :
    limitTerminalToStage D c i ≫ ((stageEtale D).obj i).hom =
      (limitTerminal D c).hom ≫ c.pt.hom := by
  change pullback.snd (𝟙 S) c.pt.hom ≫ (c.π.app i).left ≫ (D.obj i).hom = _
  rw [Over.w (c.π.app i)]
  rfl

/-- The constant sheaf `ℤ` on the limit, so that `Extᵠ(ℤ, -)` is `Sheaf.H`. -/
noncomputable abbrev constantZ (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- The canonical morphism `ℤ ⟶ P^* ℤ[Dᵢ]` on the limit `X`, for `P : X ⟶ S`: the global
section of `P^* ℤ[Dᵢ]` given by the pullback of the generator of `ℤ[Dᵢ]` along `X ⟶ Dᵢ`. -/
noncomputable def limitSectionZ (i : I) :
    constantZ c.pt.left ⟶ (c.pt.hom)^*[AddCommGrpCat.{u + 1}].obj
      ((stageEtale D ⋙ freeAbSheaf S).obj i) :=
  Abelian.Ext.homEquiv₀ ((Sheaf.H.equiv₀ _ (isTerminal_limitTerminal D c)).symm
    (pullSection c.pt.hom _ (limitTerminalToStage D c i) (limitTerminalToStage_comp D c i)
      (freeAbSheafGenerator _)))

lemma equiv₀_mk₀_limitSectionZ_comp (i : I) {F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : (stageEtale D ⋙ freeAbSheaf S).obj i ⟶ F) :
    Sheaf.H.equiv₀ _ (isTerminal_limitTerminal D c) (Abelian.Ext.mk₀ (limitSectionZ D c i ≫
      (c.pt.hom)^*[AddCommGrpCat.{u + 1}].map ψ)) =
      pullSection c.pt.hom F (limitTerminalToStage D c i) (limitTerminalToStage_comp D c i)
        (freeAbSheafHomEquiv _ F ψ) := by
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Sheaf.H.map_apply, ← Sheaf.H.equiv₀_naturality,
    limitSectionZ, Abelian.Ext.mk₀_homEquiv₀_apply, AddEquiv.apply_symm_apply,
    pullSection_naturality, freeAbSheafHomEquiv_eq]
  rfl


/-- The structure morphisms `Dᵢ ⟶ S` of a system of `S`-schemes. -/
@[simps]
noncomputable def stageStructure : D ⋙ Over.forget S ⟶ (Functor.const I).obj S where
  app i := (D.obj i).hom
  naturality i j g := by simp

variable [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g).left]

/-- **Continuity of global sections**: `colimᵢ Hom(ℤ[Dᵢ], F) ⟶ Hom(ℤ, P^* F)` is bijective, for a
quasi-compact quasi-separated base `S`. This is the continuity of sections
`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`, the sections of `F` over the
étale `S`-scheme `Dᵢ` being identified with the global sections of its inverse image to `Dᵢ`. -/
theorem commutesWithLimit_zero_of_isLimit [CompactSpace S] [QuasiSeparatedSpace S]
    (hc : IsLimit ((Over.forget S).mapCone c))
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Abelian.Ext.CommutesWithLimit (c.pt.hom)^*[AddCommGrpCat.{u + 1}]
      (stageEtale D ⋙ freeAbSheaf S) (constantZ c.pt.left) (limitSectionZ D c) 0 F := by
  have (i : I) : CompactSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (g : i ⟶ j) : IsAffineHom ((D ⋙ Over.forget S).map g) :=
    inferInstanceAs (IsAffineHom (D.map g).left)
  have (i : I) : AlgebraicGeometry.Etale ((stageStructure D).app i) :=
    inferInstanceAs (AlgebraicGeometry.Etale (D.obj i).hom)
  let π := stageStructure D
  have hP (i : I) : c.pt.hom = ((Over.forget S).mapCone c).π.app i ≫ π.app i :=
    (Over.w (c.π.app i)).symm
  let W : S.Etale := Scheme.Etale.mk (𝟙 S)
  have : CompactSpace W.left := inferInstanceAs (CompactSpace S)
  have : QuasiSeparatedSpace W.left := inferInstanceAs (QuasiSeparatedSpace S)
  have hsc := unitComparison_app_isColimit_of_isLimit (D ⋙ Over.forget S) π
    ((Over.forget S).mapCone c) c.pt.hom hP hc F W
  -- sections over `Dᵢ` and over the base change of `W` to `Dᵢ`
  have hφ (i : I) : pullback.snd (𝟙 S) (π.app i) ≫ ((stageEtale D).obj i).hom =
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (π.app i)).obj W).hom ≫
        π.app i := rfl
  have hbij (i : I) := pullSection_bijective_of_isIso (π.app i) F
    (T := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (π.app i)).obj W)
    (U := (stageEtale D).obj i)
    (pullback.snd (𝟙 S) (π.app i)) (hφ i)
  have key (i : I) (g : F.obj.obj (op ((stageEtale D).obj i))) :
      (unitComparison (((Over.forget S).mapCone c).π.app i) (π.app i) c.pt.hom (hP i) F).hom.app
        (op W) (pullSection (π.app i) F _ (hφ i) g) =
      pullSection c.pt.hom F (limitTerminalToStage D c i) (limitTerminalToStage_comp D c i) g := by
    rw [unitComparison_hom_app_eq]
    erw [restrictAlong_pullSection]
    exact pullSection_congr _ _ _ (by exact pullback.lift_snd _ _ _) _
  have key₂ {i k : I} (f : k ⟶ i) (g : F.obj.obj (op ((stageEtale D).obj i))) :
      (unitComparison ((D ⋙ Over.forget S).map f) (π.app i) (π.app k) (by simp [π]) F).hom.app
        (op W) (pullSection (π.app i) F _ (hφ i) g) =
      pullSection (π.app k) F _ (hφ k) (F.obj.map ((stageEtale D).map f).op g) := by
    rw [unitComparison_hom_app_eq]
    erw [restrictAlong_pullSection]
    rw [← pullSection_comp]
    exact pullSection_congr _ _ _ (by exact pullback.lift_snd _ _ _) _
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨i, σ, hσ⟩ := hsc.1 (Sheaf.H.equiv₀ _ (isTerminal_limitTerminal D c) x)
    obtain ⟨g, rfl⟩ := (hbij i).2 σ
    refine ⟨i, Abelian.Ext.mk₀ ((freeAbSheafHomEquiv _ F).symm g), ?_⟩
    apply (Sheaf.H.equiv₀ _ (isTerminal_limitTerminal D c)).injective
    rw [Abelian.Ext.limitComparison_apply, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.mk₀_comp_mk₀, equiv₀_mk₀_limitSectionZ_comp, Equiv.apply_symm_apply, ← key]
    exact hσ
  · obtain ⟨ψ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
    rw [Abelian.Ext.limitComparison_apply, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.mk₀_comp_mk₀] at hy
    have h₁ := equiv₀_mk₀_limitSectionZ_comp D c i ψ
    rw [hy, map_zero, ← key] at h₁
    obtain ⟨k, f, hf⟩ := hsc.2 i _ h₁.symm
    refine ⟨k, f, ?_⟩
    rw [key₂] at hf
    have h₂ : F.obj.map ((stageEtale D).map f).op (freeAbSheafHomEquiv _ F ψ) = 0 := by
      refine (hbij k).1 ?_
      rw [pullSection_zero]
      exact hf
    have h₃ : (stageEtale D ⋙ freeAbSheaf S).map f ≫ ψ = 0 := by
      apply (freeAbSheafHomEquiv _ F).injective
      refine (freeAbSheafHomEquiv_map ((stageEtale D).map f) F ψ).trans ?_
      rw [h₂, freeAbSheafHomEquiv_eq]
      rfl
    rw [Abelian.Ext.mk₀_comp_mk₀, h₃, Abelian.Ext.mk₀_zero]

/-- The comparison morphisms `ℤ ⟶ P^* ℤ[Dᵢ]` are compatible with the transition maps. -/
lemma limitSectionZ_comp_map {i j : I} (f : i ⟶ j) :
    limitSectionZ D c i ≫ (c.pt.hom)^*[AddCommGrpCat.{u + 1}].map
      ((stageEtale D ⋙ freeAbSheaf S).map f) = limitSectionZ D c j := by
  apply (Abelian.Ext.mk₀_bijective _ _).1
  apply (Sheaf.H.equiv₀ _ (isTerminal_limitTerminal D c)).injective
  rw [equiv₀_mk₀_limitSectionZ_comp, limitSectionZ, Abelian.Ext.mk₀_homEquiv₀_apply,
    AddEquiv.apply_symm_apply, Functor.comp_map, ← Category.comp_id ((freeAbSheaf S).map _),
    freeAbSheafHomEquiv_map, ← pullSection_comp]
  refine pullSection_congr _ _ _ ?_ _
  have := congrArg CommaMorphism.left (c.w f)
  simp only [Over.comp_left] at this
  simp [limitTerminalToStage, this]

/-- **Continuity of étale cohomology at a cofiltered limit of étale schemes.** Let `S` be a
quasi-compact quasi-separated scheme, `(Dᵢ)` a cofiltered system of quasi-compact
quasi-separated étale `S`-schemes with affine transition maps, `X = lim Dᵢ` with `P : X ⟶ S`, and
`F` an abelian étale sheaf on `S`. Then for every `q` the canonical map
`colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ}) ⟶ Hᵠ(X, P^* F)` is bijective, elementwise
(`CategoryTheory.Abelian.Ext.CommutesWithLimit`): every class of `Hᵠ(X, P^* F)` comes from some
stage, and a class at a stage which vanishes on `X` vanishes at a later stage. Here
`Hᵠ(Dᵢ, F|_{Dᵢ})` is `Extᵠ(ℤ[Dᵢ], F)`, with `ℤ[Dᵢ]` the free abelian sheaf on `Dᵢ`, and
`Hᵠ(X, P^* F) = Extᵠ(ℤ, P^* F)` is `Sheaf.H`; the comparison maps pull classes back to `X` and
restrict them along the canonical section `ℤ ⟶ P^* ℤ[Dᵢ]`.

The blueprint states this for arbitrary qcqs stages with affine transition maps; this is the case
of étale stages, which covers the strict henselization stalk formula.
(blueprint: `lemma-weil-pbc-etale-cohomology-continuity`) -/
@[stacks 09YQ]
theorem commutesWithLimit_of_isLimit [CompactSpace S] [QuasiSeparatedSpace S]
    (hc : IsLimit ((Over.forget S).mapCone c))
    (q : ℕ) (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Abelian.Ext.CommutesWithLimit (c.pt.hom)^*[AddCommGrpCat.{u + 1}]
      (stageEtale D ⋙ freeAbSheaf S) (constantZ c.pt.left) (limitSectionZ D c) q F := by
  refine Abelian.Ext.commutesWithLimit_of_isCofiltered _ _ _ _ (limitSectionZ_comp_map D c)
    (fun F ↦ commutesWithLimit_zero_of_isLimit D c hc F) (fun J _ q x ↦ ?_) q F
  have (i : I) : CompactSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (g : i ⟶ j) : IsAffineHom ((D ⋙ Over.forget S).map g) :=
    inferInstanceAs (IsAffineHom (D.map g).left)
  have (i : I) : AlgebraicGeometry.Etale ((stageStructure D).app i) :=
    inferInstanceAs (AlgebraicGeometry.Etale (D.obj i).hom)
  have := subsingleton_H_succ_upperStar_of_isLimit (D ⋙ Over.forget S)
    ((Over.forget S).mapCone c) (stageStructure D) c.pt.hom (fun i ↦ (Over.w (c.π.app i)).symm)
    hc J (fun i ↦ injective_upperStar_obj_of_etale_addCommGrp _ J) q
  exact @Subsingleton.elim _ this x 0

end Continuity

end AlgebraicGeometry.Etale
