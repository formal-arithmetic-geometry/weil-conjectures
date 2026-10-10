/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.Algebra.Homology.ResolutionByClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Lifting sections of étale sheaves along epimorphisms

An epimorphism of étale sheaves is locally surjective: a section of the target over a
quasi-compact étale `X`-scheme `W` lifts, after refining `W` by finitely many affine étale
`X`-schemes jointly covering it.

## Main statements

- `AlgebraicGeometry.Etale.exists_affine_refinement`: a covering sieve of a quasi-compact
  object of the small étale site contains a finite family of affine étale `X`-schemes jointly
  covering it.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {X : Scheme.{u}}

/-- **Finite affine refinement of an étale covering sieve.** A covering sieve `S` of an object
`W` of the small étale site of `X` with quasi-compact `W` contains finitely many arrows
`φ k : V k ⟶ W` from affine étale `X`-schemes whose images cover `W`. -/
lemma exists_affine_refinement {W : X.Etale} [CompactSpace W.left] (S : Sieve W)
    (hS : S ∈ X.smallEtaleTopology W) :
    ∃ (n : ℕ) (V : Fin n → X.Etale) (φ : ∀ k, V k ⟶ W), (∀ k, S (φ k)) ∧
      (∀ k, IsAffine (V k).left) ∧ ⋃ k, Set.range (φ k).left = Set.univ := by
  rw [Scheme.mem_smallEtaleTopology_iff] at hS
  choose V g hg hx using hS
  choose v hv using hx
  have hU (w : W.left) : ∃ U ∈ (V w).left.affineOpens, v w ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hvU, -⟩ :=
      (V w).left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (v w)) isOpen_univ
    exact ⟨U, hU, hvU⟩
  choose U hUa hvU using hU
  let V' (w : W.left) : X.Etale := Scheme.Etale.mk ((U w).ι ≫ (V w).hom)
  let ψ (w : W.left) : V' w ⟶ V w := MorphismProperty.Over.homMk (U w).ι rfl
  let φ (w : W.left) : V' w ⟶ W := ψ w ≫ g w
  have hφ (w : W.left) : (φ w).left = (U w).ι ≫ (g w).left := rfl
  let O (w : W.left) : Set W.left := Set.range (φ w).left
  have hO (w : W.left) : IsOpen (O w) := (φ w).left.isOpenMap.isOpen_range
  have hwO (w : W.left) : w ∈ O w := ⟨⟨v w, hvU w⟩, by
    rw [hφ, Scheme.Hom.comp_apply]
    exact hv w⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun w _ ↦ Set.mem_iUnion.2 ⟨w, hwO w⟩)
  let e := t.equivFin.symm
  refine ⟨t.card, fun k ↦ V' (e k), fun k ↦ φ (e k), fun k ↦ S.downward_closed (hg _) _,
    fun k ↦ hUa (e k), ?_⟩
  refine Set.eq_univ_of_forall fun w ↦ ?_
  obtain ⟨w', hw', hw⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  refine Set.mem_iUnion.2 ⟨e.symm ⟨w', hw'⟩, ?_⟩
  have : (e (e.symm ⟨w', hw'⟩) : W.left) = w' := by rw [Equiv.apply_symm_apply]
  change w ∈ O (e (e.symm ⟨w', hw'⟩) : W.left)
  rw [this]
  exact hw

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- `Sheaf.freeYonedaHomEquiv` is natural in the target. -/
lemma freeYonedaHomEquiv_comp {W : X.Etale} {M : ModuleCat.{u + 1} Λ}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : Sheaf.freeYoneda X.smallEtaleTopology W M ⟶ F) (f : F ⟶ G) :
    Sheaf.freeYonedaHomEquiv (α ≫ f) = Sheaf.freeYonedaHomEquiv α ≫ f.hom.app (op W) := by
  simp only [Sheaf.freeYonedaHomEquiv, Equiv.trans_apply]
  have h := (sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).homEquiv_naturality_right
    (X := Presheaf.freeYoneda W M) α f
  erw [h, Presheaf.freeYonedaHomEquiv_comp]
  rfl

/-- **Local lifting along an epimorphism.** Let `p : A ⟶ G` be an epimorphism of étale sheaves
of `Λ`-modules and `s : Λ[W] ⟶ G` a map from the free sheaf on a quasi-compact étale
`X`-scheme `W`. Then there are finitely many affine étale `X`-schemes `V k` with maps
`φ k : V k ⟶ W` whose images cover `W`, and lifts `t k : Λ[V k] ⟶ A` of the restrictions of
`s` to the `V k`. -/
lemma exists_lift_freeYoneda {A G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (p : A ⟶ G) [Epi p] (W : X.Etale) [CompactSpace W.left]
    (s : Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ G) :
    ∃ (n : ℕ) (V : Fin n → X.Etale) (φ : ∀ k, V k ⟶ W)
      (t : ∀ k, Sheaf.freeYoneda X.smallEtaleTopology (V k) (ModuleCat.of Λ Λ) ⟶ A),
      (∀ k, IsAffine (V k).left) ∧ ⋃ k, Set.range (φ k).left = Set.univ ∧
      ∀ k, Sheaf.freeYonedaHomEquiv (t k ≫ p) =
        Sheaf.freeYonedaHomEquiv s ≫ G.obj.map (φ k).op := by
  have : Sheaf.IsLocallySurjective p :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := p)).2 inferInstance
  let x := (Sheaf.freeYonedaHomEquiv s).hom (1 : Λ)
  obtain ⟨n, V, φ, hφ, hV, hcov⟩ := exists_affine_refinement _
    (Presheaf.imageSieve_mem X.smallEtaleTopology p.hom (U := op W) x)
  choose a ha using hφ
  refine ⟨n, V, φ, fun k ↦ Sheaf.freeYonedaHomEquiv.symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ (a k))), hV, hcov, fun k ↦ ?_⟩
  rw [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]
  ext
  simpa [x] using ha k

omit [CommRing Λ] in
/-- A property of objects of an abelian category which contains the zero objects and is closed
under isomorphisms and binary biproducts is closed under finite coproducts. -/
lemma _root_.CategoryTheory.ObjectProperty.isClosedUnderFiniteCoproducts_of_biprod
    {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] (h : ∀ X Y, P X → P Y → P (X ⊞ Y)) :
    P.IsClosedUnderFiniteCoproducts := by
  have : P.IsClosedUnderBinaryCoproducts := ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    exact P.prop_of_iso ((biprod.isoCoprod _ _) ≪≫ (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
      (h _ _ (hF _) (hF _)))
  exact .mk'

/-- **Lifting along epimorphisms by free sheaves.** Let `S` be a property of étale sheaves of
`Λ`-modules closed under finite coproducts and containing the free sheaves `Λ[W]` on the affine
étale `X`-schemes `W`, and let `T` be a property such that every sheaf `G` in `T` is a quotient
of a finite coproduct of such free sheaves, that is, receives a jointly epimorphic finite
family of maps from them. Then `S` lifts along epimorphisms onto `T`: sections
lift locally along an epimorphism (`AlgebraicGeometry.Etale.exists_lift_freeYoneda`), and the
local pieces again form a finite coproduct of free sheaves on affine étale `X`-schemes. -/
theorem liftsAlongEpi_of_exists_epi_sigma_freeYoneda
    (S T : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [S.IsClosedUnderFiniteCoproducts]
    (hS : ∀ W : X.Etale, IsAffine W.left →
      S (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)))
    (hgen : ∀ G, T G → ∃ (n : ℕ) (W : Fin n → X.Etale)
      (s : ∀ i, Sheaf.freeYoneda X.smallEtaleTopology (W i) (ModuleCat.of Λ Λ) ⟶ G),
      (∀ i, IsAffine (W i).left) ∧ ∀ ⦃F⦄ (f : G ⟶ F), (∀ i, s i ≫ f = 0) → f = 0) :
    ChainComplex.LiftsAlongEpi S T := by
  intro A B G p _ g hG
  obtain ⟨n, W, s, hWa, hepi⟩ := hgen G hG
  have : Epi (pullback.snd p g) := inferInstance
  choose m V φ t hV hcov ht using fun i ↦ exists_lift_freeYoneda (pullback.snd p g) (W i) (s i)
  have : HasFiniteCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := inferInstance
  have := hasColimitsOfShape_discrete (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Σ i, Fin (m i))
  let free (Z : X.Etale) := Sheaf.freeYoneda X.smallEtaleTopology Z (ModuleCat.of Λ Λ)
  let e : ∐ (fun j : Σ i, Fin (m i) ↦ free (V j.1 j.2)) ⟶ G := Sigma.desc fun j ↦
    Sheaf.freeYonedaHomEquiv.symm (Sheaf.freeYonedaHomEquiv (s j.1) ≫ G.obj.map (φ j.1 j.2).op)
  have he (j : Σ i, Fin (m i)) : t j.1 j.2 ≫ pullback.snd p g = Sigma.ι _ j ≫ e := by
    apply Sheaf.freeYonedaHomEquiv.injective
    rw [ht, Sigma.ι_desc, Equiv.apply_symm_apply]
  refine ⟨_, e, Sigma.desc (fun j ↦ t j.1 j.2) ≫ pullback.fst p g,
    S.prop_coproduct (fun j ↦ hS _ (hV _ _)), ?_, ?_⟩
  · refine Preadditive.epi_of_cancel_zero _ fun {F} f hf ↦ ?_
    have hs (i : Fin n) : s i ≫ f = 0 := by
      apply Sheaf.freeYonedaHomEquiv.injective
      rw [freeYonedaHomEquiv_comp, ← comp_zero (f := s i), freeYonedaHomEquiv_comp]
      refine F.property.hom_ext_ofArrows (φ i)
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 (hcov i)) fun k ↦ ?_
      have h₁ := congrArg Sheaf.freeYonedaHomEquiv
        (Sigma.ι (fun j : Σ i, Fin (m i) ↦ free (V j.1 j.2)) ⟨i, k⟩ ≫= hf)
      rw [comp_zero, ← Category.assoc, Sigma.ι_desc, freeYonedaHomEquiv_comp,
        Equiv.apply_symm_apply] at h₁
      simp only [Category.assoc, ← NatTrans.naturality] at h₁ ⊢
      rw [h₁]
      calc Sheaf.freeYonedaHomEquiv (0 : free (V i k) ⟶ F)
          = Sheaf.freeYonedaHomEquiv ((0 : free (V i k) ⟶ F) ≫ (0 : F ⟶ F)) := by rw [comp_zero]
        _ = _ := freeYonedaHomEquiv_comp _ _
        _ = 0 := by simp
    exact hepi f hs
  · ext j
    simp only [Sigma.ι_desc_assoc, Category.assoc, pullback.condition]
    rw [← Category.assoc, he, Category.assoc]

omit [CommRing Λ] in
/-- A colimit of flat objects of shape `J`, for colimits of shape `J` exact, is flat: tensoring
with it is the colimit of the left exact functors of tensoring with the terms. -/
lemma _root_.CategoryTheory.ObjectProperty.flat_colimit {A : Type*} [Category* A] [Abelian A]
    [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A] {J : Type*} [Category* J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] (F : J ⥤ A)
    (hF : ∀ j, ObjectProperty.flat (F.obj j)) : ObjectProperty.flat (colimit F) := by
  have (j : J) : PreservesFiniteLimits (tensorLeft (F.obj j)) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits (F.obj j)).1 (hF j)
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesColimit F (MonoidalCategory.curriedTensor A) :=
    MonoidalCategory.Limits.preservesCoLimit_curriedTensor _
  have e : tensorLeft (colimit F) ≅ (F ⋙ MonoidalCategory.curriedTensor A).flip ⋙ colim :=
    preservesColimitIso (MonoidalCategory.curriedTensor A) F ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((F ⋙ MonoidalCategory.curriedTensor A).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (tensorLeft (F.obj j))))
  exact preservesFiniteLimits_of_natIso e.symm

/-- **Free sheaves are flat.** The free étale sheaf of `Λ`-modules `Λ[W]` on an étale
`X`-scheme `W` is flat: its stalks are filtered colimits of free `Λ`-modules. -/
theorem flat_freeYoneda (W : X.Etale) :
    ObjectProperty.flat (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) := by
  rw [flat_iff_forall_flat_sheafFiber_obj]
  intro Ω _ _ s
  let Φ := (Scheme.pointSmallEtale s).ulift.{u + 1}
  refine ObjectProperty.prop_of_iso _
    ((Φ.presheafToSheafCompSheafFiberIso _).app (Presheaf.freeYoneda W (ModuleCat.of Λ Λ))).symm
    (ObjectProperty.flat_colimit _ fun j ↦ ?_)
  have hunit : ObjectProperty.flat (ModuleCat.of Λ Λ) :=
    ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ (ModuleCat.{u + 1} Λ)))
  let f (_ : ULift.{u + 1} ((yoneda.obj W).obj (op j.unop.1))) := ModuleCat.of Λ Λ
  exact ObjectProperty.prop_of_iso _ (Sigma.whiskerEquiv Equiv.ulift (fun _ ↦ Iso.refl _))
    (ObjectProperty.flat_coproduct f fun _ ↦ hunit)

/-- **Base change of free sheaves.** For a morphism `g : Y ⟶ X` and an étale `X`-scheme `W`,
the pullback `g^* Λ[W]` is the free sheaf `Λ[W ×_X Y]` on the base change of `W`: both
corepresent `F ↦ F(W ×_X Y) = (g_* F)(W)`. -/
noncomputable def upperStarFreeYonedaIso {Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Etale) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
        (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) ≅
      Sheaf.freeYoneda Y.smallEtaleTopology (g.Etale.obj W) (ModuleCat.of Λ Λ) :=
  let e (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
        (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) ⟶ F) ≃
      (Sheaf.freeYoneda Y.smallEtaleTopology (g.Etale.obj W) (ModuleCat.of Λ Λ) ⟶ F) :=
    let e₁ := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).homEquiv
      (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) F
    let e₂ := Sheaf.freeYonedaHomEquiv (J := X.smallEtaleTopology) (X := W)
      (M := ModuleCat.of Λ Λ) (F := (Etale.lowerStar (ModuleCat.{u + 1} Λ) g).obj F)
    let e₃ := Sheaf.freeYonedaHomEquiv (J := Y.smallEtaleTopology) (X := g.Etale.obj W)
      (M := ModuleCat.of Λ Λ) (F := F)
    { toFun f := e₃.symm (e₂ (e₁ f))
      invFun f := e₁.symm (e₂.symm (e₃ f))
      left_inv f := by simp
      right_inv f := by simp }
  have he {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : _ ⟶ F) (h : F ⟶ F') :
      e F' (f ≫ h) = e F f ≫ h := by
    apply Sheaf.freeYonedaHomEquiv.injective
    dsimp only [e, Equiv.coe_fn_mk]
    rw [Equiv.apply_symm_apply, freeYonedaHomEquiv_comp, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, freeYonedaHomEquiv_comp]
    rfl
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f) (fun f ↦ by simp)
    (fun f ↦ by simp) (fun f h ↦ by
      apply (e _).injective
      rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- **Generic local constancy of free sheaves.** Let `Z` be a nonempty scheme with Noetherian
underlying space and `Λ` finite. The free étale sheaf `Λ[W]` on an affine étale `Z`-scheme `W`
is finite locally constant on some nonempty open `U ⊆ Z`: over a dense open `U` the morphism
`W ⟶ Z` is finite étale (it is finite étale over the generic points of `Z`, and this spreads
out), and the free sheaf on a finite étale `U`-scheme is finite locally constant, the finite
étale scheme splitting étale-locally on `U` (`lem-fet-locally-trivial`). -/
theorem exists_isFiniteLocallyConstantSheaf_freeYoneda [Finite Λ] {Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Z] [Nonempty Z] (W : Z.Etale) [IsAffine W.left] :
    ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ Scheme.IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
        (Sheaf.freeYoneda Z.smallEtaleTopology W (ModuleCat.of Λ Λ))) :=
  sorry

/-- **Free sheaves on affine étale schemes are constructible** [Stacks 03SA, 095M]. Let `X` be
a scheme with Noetherian underlying space and `Λ` finite. The free étale sheaf `Λ[W] = j_{W!} Λ_W`
on an affine étale `X`-scheme `W` is constructible. By Noetherian induction it is finite
locally constant on a nonempty open `U`
(`AlgebraicGeometry.Etale.exists_isFiniteLocallyConstantSheaf_freeYoneda`) and, by base change
(`AlgebraicGeometry.Etale.upperStarFreeYonedaIso`), its restriction to the closed complement of
`U` is the free sheaf on an affine étale scheme over a smaller closed subset. -/
theorem isConstructibleSheaf_freeYoneda [Finite Λ] [TopologicalSpace.NoetherianSpace X]
    (W : X.Etale) [IsAffine W.left] :
    Scheme.IsConstructibleSheaf (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) := by
  -- Noetherian induction on the closed subsets `C` of `X` containing the image of a closed
  -- subscheme `Z`
  suffices h : ∀ C : TopologicalSpace.Closeds X, ∀ (Z : Scheme.{u}) (i : Z ⟶ X)
      [IsClosedImmersion i], Set.range i.base ⊆ C → ∀ (W : Z.Etale) [IsAffine W.left],
      Scheme.IsConstructibleSheaf (Sheaf.freeYoneda Z.smallEtaleTopology W (ModuleCat.of Λ Λ)) by
    exact h ⊤ X (𝟙 X) (Set.subset_univ _) W
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
  intro Z i _ hZC W _
  have : TopologicalSpace.NoetherianSpace (Set.range i.base) := inferInstance
  have : TopologicalSpace.NoetherianSpace Z :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph
      i.isClosedEmbedding.isEmbedding.toHomeomorph).2 inferInstance
  by_cases hZ : IsEmpty Z
  · exact Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  rw [not_isEmpty_iff] at hZ
  obtain ⟨U, hU, hlc⟩ := exists_isFiniteLocallyConstantSheaf_freeYoneda (Λ := Λ) W
  let i' := Scheme.Opens.closedComplement U
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set Z))
  have hij : Set.range i'.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_closedComplement, Scheme.Opens.range_ι]
  rw [Scheme.isConstructibleSheaf_iff_upperStar U.ι i' hij]
  refine ⟨hlc.isConstructibleSheaf, ?_⟩
  have : IsAffine (i'.Etale.obj W).left :=
    have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
    isAffine_of_isAffineHom (pullback.fst W.hom i')
  let C' : TopologicalSpace.Closeds X :=
    ⟨Set.range (i' ≫ i).base, (i' ≫ i).isClosedEmbedding.isClosed_range⟩
  have hC' : C' < C := by
    refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
    · obtain ⟨z, rfl⟩ := hx
      exact hZC ⟨_, rfl⟩
    · obtain ⟨u, hu⟩ := hU
      have hx : i.base u ∈ (C : Set X) := hZC ⟨u, rfl⟩
      rw [← h] at hx
      obtain ⟨z, hz⟩ := hx
      rw [Scheme.Hom.comp_apply] at hz
      have := i.isClosedEmbedding.injective hz
      have hz' : u ∈ Set.range i'.base := ⟨z, this⟩
      rw [hij] at hz'
      exact hz' ⟨⟨u, hu⟩, rfl⟩
  have := ih C' hC' _ (i' ≫ i) subset_rfl (i'.Etale.obj W)
  exact Scheme.IsConstructibleSheaf.of_iso (upperStarFreeYonedaIso i' W).symm

/-- **Constructible sheaves are generated by finitely many sections** [Stacks 095M; SGA 4½,
Rapport, 4.6]. Let `X` be Noetherian and `Λ` finite. A constructible sheaf `G` of `Λ`-modules
on `X_ét` receives a jointly epimorphic finite family of maps from free sheaves `Λ[W i]` on
affine étale `X`-schemes. -/
theorem exists_jointlyEpi_freeYoneda [Finite Λ] [IsNoetherian X]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf G] :
    ∃ (n : ℕ) (W : Fin n → X.Etale)
      (s : ∀ i, Sheaf.freeYoneda X.smallEtaleTopology (W i) (ModuleCat.of Λ Λ) ⟶ G),
      (∀ i, IsAffine (W i).left) ∧ ∀ ⦃F⦄ (f : G ⟶ F), (∀ i, s i ≫ f = 0) → f = 0 :=
  sorry

end AlgebraicGeometry.Etale
