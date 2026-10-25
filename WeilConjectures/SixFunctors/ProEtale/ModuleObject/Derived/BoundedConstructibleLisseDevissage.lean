/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization

/-!
# Dévissage of bounded constructible complexes to lisse sheaves on locally closed subschemes

Let `Λ` be a commutative condensed ring and `T` a scheme with noetherian underlying space. A
triangulated functor `Φ : D(Mod_{Λ_T}) ⥤ D(Mod_{Λ_Y})`, where the bounded constructible
complexes on `Y` form a triangulated subcategory, carries `Dᵇc(T)` into `Dᵇc(Y)` as soon as it
does so for the extensions by zero `Rc_* j_! Rc'_* L` of the pro-étale locally finitely presented
(lisse) sheaves `L` along the locally closed immersions `E ⟶ W ⊆ D ⟶ T` (with `c` and `c'` closed
immersions and `W` open in `D`)
(`ProEtale.CondensedRing.boundedConstructible_obj_of_forall_lisse`).

The proof is a noetherian induction on the closed subset of `T` containing the image of a closed
immersion `c : D ⟶ T`, for complexes of the form `Rc_* M` with `M` bounded constructible on `D`.
By dévissage along the truncation triangles, `M` is a constructible sheaf `G` placed in degree
`0`. Some stratum of a stratification of `D` adapted to `G` contains a nonempty open `V` of `D`
(`ProEtale.CondensedRing.exists_nonempty_opens_subset_stratum`), and the open–closed triangle
`j_! Lj^* G ⟶ G ⟶ Ri_* Li^* G ⟶` for `V` and its closed complement splits `G` into the extension
by zero of a sheaf which is lisse on (a surjective closed immersion onto) `V`, and a complex
supported on the smaller closed subset `c(D ∖ V)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- In a finite union of closed sets with empty interiors, the interior is empty. -/
lemma interior_iUnion_eq_empty_of_isClosed {X : Type*} [TopologicalSpace X] {n : ℕ}
    (s : Fin n → Set X) (hc : ∀ a, IsClosed (s a)) (hi : ∀ a, interior (s a) = ∅) :
    interior (⋃ a, s a) = ∅ := by
  suffices h : ∀ t : Finset (Fin n), interior (⋃ a ∈ t, s a) = ∅ by
    simpa using h Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t _ ih =>
    rw [Finset.set_biUnion_insert, Set.union_comm,
      interior_union_isClosed_of_interior_empty (isClosed_biUnion_finset fun b _ ↦ hc b) (hi a), ih]

/-- A finite partition of a nonempty topological space into locally closed sets has a member
containing a nonempty open set. -/
lemma exists_nonempty_isOpen_subset_of_isLocallyClosed {X : Type*} [TopologicalSpace X]
    [Nonempty X] {n : ℕ} (s : Fin n → Set X) (hs : ∀ a, IsLocallyClosed (s a))
    (hU : ⋃ a, s a = Set.univ) :
    ∃ a, ∃ V : Set X, IsOpen V ∧ V.Nonempty ∧ V ⊆ s a := by
  obtain ⟨a, ha⟩ : ∃ a, (interior (closure (s a))).Nonempty := by
    by_contra! h
    have h' := interior_iUnion_eq_empty_of_isClosed (fun a ↦ closure (s a))
      (fun _ ↦ isClosed_closure) h
    have : (⋃ a, closure (s a)) = Set.univ :=
      Set.eq_univ_of_univ_subset (hU ▸ Set.iUnion_mono fun _ ↦ subset_closure)
    rw [this, interior_univ] at h'
    exact Set.univ_nonempty.ne_empty h'
  obtain ⟨U, C, hUo, hCc, hsUC⟩ := hs a
  obtain ⟨x, hx⟩ := ha
  have hxs : x ∈ closure (s a) := interior_subset hx
  obtain ⟨y, hyW, hys⟩ := mem_closure_iff.1 hxs _ isOpen_interior hx
  refine ⟨a, interior (closure (s a)) ∩ U, isOpen_interior.inter hUo,
    ⟨y, hyW, (hsUC ▸ hys).1⟩, fun z ⟨hzW, hzU⟩ ↦ ?_⟩
  rw [hsUC]
  refine ⟨hzU, ?_⟩
  have : closure (s a) ⊆ C := closure_minimal (hsUC ▸ Set.inter_subset_right) hCc
  exact this (interior_subset hzW)

/-- On a nonempty scheme, some stratum of a stratification contains a nonempty open. -/
lemma exists_nonempty_opens_subset_stratum {X : Scheme.{u}} [Nonempty X]
    (S : Scheme.Stratification X) :
    ∃ a, ∃ V : X.Opens, (V : Set X).Nonempty ∧ (V : Set X) ⊆ S.stratum a := by
  obtain ⟨a, V, hV, hne, hsub⟩ := exists_nonempty_isOpen_subset_of_isLocallyClosed S.stratum
    S.isLocallyClosed_stratum S.iUnion_stratum_eq_univ
  exact ⟨a, ⟨V, hV⟩, hne, hsub⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- A complex all of whose cohomology sheaves vanish is zero. -/
lemma isZero_of_forall_isZero_homology {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (h : ∀ n, IsZero ((DerivedCategory.homologyFunctor _ n).obj K)) : IsZero K := by
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 fun n _ ↦ h n
  have : K.IsLE (-1) := (DerivedCategory.isLE_iff K (-1)).2 fun n _ ↦ h n
  exact DerivedCategory.TStructure.t.isZero K (-1) 0 (by lia)

omit [IsCommMonObj Λ] in
/-- Every complex of module objects on an empty scheme is zero. -/
lemma isZero_derivedCategory_of_isEmpty' {X : Scheme.{u}} [IsEmpty X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) : IsZero K := by
  exact isZero_of_forall_isZero_homology Λ fun _ ↦ isZero_mod_of_isEmpty Λ _

/-- The derived pullback of a sheaf placed in degree `0` is the pullback, placed in degree
`0`. -/
noncomputable def leftDerivedUpperStarSingleIso {W X : Scheme.{u}} (g : W ⟶ X)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (L((g)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((g)^*⟦Λ⟧.obj F) :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _ ≪≫
    (((g)^*⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app F

omit [IsCommMonObj Λ] in
/-- A constructible sheaf placed in degree `0` is bounded constructible. -/
lemma boundedConstructible_singleFunctor_zero_obj {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    boundedConstructible (condensedRingObj Λ X) ((DerivedCategory.singleFunctor _ 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun i ↦ ?_⟩
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isGE _ 0 i hi)
  · exact IsConstructibleModuleObject.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · exact isConstructibleModuleObject_of_isZero _ (DerivedCategory.isZero_of_isLE _ 0 i hi)

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` of derived pushforwards, conjugate to
the composition isomorphism of derived pullbacks. -/
noncomputable def rightDerivedLowerStarComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R((f)_*⟦Λ⟧) ⋙ R((g)_*⟦Λ⟧) ≅ R((f ≫ g)_*⟦Λ⟧) :=
  conjugateIsoEquiv ((derivedUpperStarLowerStarAdjunction Λ g).comp
    (derivedUpperStarLowerStarAdjunction Λ f)) (derivedUpperStarLowerStarAdjunction Λ (f ≫ g))
    (leftDerivedUpperStarComp Λ f g)

omit [IsCommMonObj Λ] in
/-- Along a commutative square `a ≫ f = b ≫ g`, if `g^* M` is pro-étale locally finitely
presented, so is `(a ≫ f)^* M`. -/
lemma isLocallyFinitelyPresented_upperStar_comp_of_comm [IsCommMonObj Λ] {P U W X : Scheme.{u}}
    {a : P ⟶ U} {b : P ⟶ W} {f : U ⟶ X} {g : W ⟶ X} (h : a ≫ f = b ≫ g)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ P) ((a ≫ f)^*⟦Λ⟧.obj M) :=
  (IsLocallyFinitelyPresented.upperStar Λ b hM).of_iso
    (((upperStarComp Λ b g).app M).symm ≪≫ (upperStarCongr Λ h.symm).app M)

section Devissage

variable {T Y : Scheme.{u}} [(boundedConstructible (condensedRingObj Λ Y)).IsTriangulated]
  (Φ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
  [Φ.CommShift ℤ] [Φ.IsTriangulated]

/-- The hypothesis of the dévissage to lisse sheaves: `Φ` maps the extensions by zero
`Rc_* j_! Rc'_* L` of the lisse sheaves `L` along the locally closed immersions
`E ⟶ W ⊆ D ⟶ T` (`c`, `c'` closed immersions, `W` open in `D`) to bounded constructible
complexes. -/
def LisseHypothesis : Prop :=
  ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c] (W : D.Opens) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c']
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1}) (condensedRingObj Λ E)),
    IsLocallyFinitelyPresented (condensedRingObj Λ E) L →
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj
      (D((W.ι)_!open⟦Λ⟧).obj ((R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj L)))))

variable {Λ Φ}

/-- The open piece of the dévissage step: the restriction of a constructible sheaf `G` on `D` to
a nonempty open `V` contained in a stratum is (the pushforward along a surjective closed immersion
of) a lisse sheaf, so `Φ (Rc_* j_! Lj^* G)` is bounded constructible. -/
lemma boundedConstructible_lisse_open (hΦ : LisseHypothesis Λ Φ) {D : Scheme.{u}}
    (c : D ⟶ T) [IsClosedImmersion c] (S : Scheme.Stratification D) (a : Fin S.n)
    (V : D.Opens) (hVS : (V : Set D) ⊆ S.stratum a)
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
      ((S.immersion a)^*⟦Λ⟧.obj G)) :
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj
      (D((V.ι)_!open⟦Λ⟧).obj ((L((V.ι)^*⟦Λ⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))))) := by
  obtain ⟨E, c', b, hcb, _, _⟩ : ∃ (E : Scheme.{u}) (c' : E ⟶ V) (b : E ⟶ S.domain a),
      c' ≫ V.ι = b ≫ S.immersion a ∧ IsClosedImmersion c' ∧ Surjective c' := by
    have : Surjective (pullback.fst V.ι (S.immersion a)) :=
      surjective_pullback_fst_of_range_subset _ _ (by
        rw [Scheme.Opens.range_ι, S.range_immersion]
        exact hVS)
    exact ⟨_, pullback.fst V.ι (S.immersion a), pullback.snd V.ι (S.immersion a),
      pullback.condition, IsClosedImmersion.of_isImmersion_of_surjective _, this⟩
  have : IsEmpty (⊥ : V.toScheme.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have hc : IsCompl (Set.range c'.base) (Set.range (⊥ : V.toScheme.Opens).ι.base) := by
    rw [Set.range_eq_univ.2 c'.surjective, Scheme.Opens.range_ι]
    exact isCompl_top_bot
  have : QuasiCompact (⊥ : V.toScheme.Opens).ι :=
    ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hu := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ
    (⊥ : V.toScheme.Opens).ι c' hc
    (K := (L((V.ι)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G))
    (isZero_derivedCategory_of_isEmpty' Λ _)
  have hL : IsLocallyFinitelyPresented (condensedRingObj Λ E) ((c' ≫ V.ι)^*⟦Λ⟧.obj G) :=
    isLocallyFinitelyPresented_upperStar_comp_of_comm (Λ := Λ) hcb hG
  have e : (L((V.ι)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G) ≅
      (R((c')_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj ((c' ≫ V.ι)^*⟦Λ⟧.obj G)) :=
    asIso ((derivedUpperStarLowerStarAdjunction Λ c').unit.app _) ≪≫
      (R((c')_*⟦Λ⟧)).mapIso (((leftDerivedUpperStarComp Λ c' V.ι).app _).symm ≪≫
        leftDerivedUpperStarSingleIso Λ (c' ≫ V.ι) G)
  exact (boundedConstructible _).prop_of_iso
    (Φ.mapIso ((R((c)_*⟦Λ⟧)).mapIso (D((V.ι)_!open⟦Λ⟧).mapIso e))).symm
    (hΦ D c V E c' _ hL)

/-- The induction step of the dévissage to lisse sheaves, for a constructible sheaf `G` on a
closed subscheme `c : D ⟶ T` with image in the closed subset `Z`: split `G` along a nonempty open
`V` of `D` contained in a stratum; the closed piece is supported on `c(D ∖ V) < Z`. -/
lemma boundedConstructible_lisse_step (hΦ : LisseHypothesis Λ Φ)
    (Z : TopologicalSpace.Closeds T)
    (ih : ∀ Z' < Z, ∀ (D : Scheme.{u}) (c : D ⟶ T) [IsClosedImmersion c],
      Set.range c.base ⊆ Z' →
      ∀ M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D)), boundedConstructible _ M →
        boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj M)))
    {D : Scheme.{u}} (c : D ⟶ T) [IsClosedImmersion c] [TopologicalSpace.NoetherianSpace D]
    (hcZ : Set.range c.base ⊆ Z)
    (G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (hG : IsConstructibleModuleObject (condensedRingObj Λ D) G) :
    boundedConstructible (condensedRingObj Λ Y)
      (Φ.obj ((R((c)_*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · exact boundedConstructible_of_isZero Λ (Φ.map_isZero ((R((c)_*⟦Λ⟧)).map_isZero
      (isZero_derivedCategory_of_isEmpty' Λ _)))
  have hGc := hG
  obtain ⟨S, hS⟩ := hG
  obtain ⟨a, V, ⟨v, hv⟩, hVS⟩ := exists_nonempty_opens_subset_stratum S
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨D'', i', _, hi'⟩ : ∃ (D'' : Scheme.{u}) (i' : D'' ⟶ D), IsClosedImmersion i' ∧
      Set.range i'.base = (V : Set D)ᶜ :=
    ⟨_, V.closedComplement, inferInstance, V.range_closedComplement⟩
  have hc : IsCompl (Set.range i'.base) (Set.range V.ι.base) := by
    rw [hi', Scheme.Opens.range_ι]
    exact isCompl_compl.symm
  obtain ⟨δ, hT⟩ := exists_distTriang_openClosed_derived Λ V.ι i' hc
    ((DerivedCategory.singleFunctor _ 0).obj G)
  refine (boundedConstructible _).ext_of_isTriangulatedClosed₂ _
    ((R((c)_*⟦Λ⟧) ⋙ Φ).map_distinguished _ hT) ?_ ?_
  · exact boundedConstructible_lisse_open hΦ c S a V hVS G
      ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))
  · let Z' : TopologicalSpace.Closeds T := ⟨c.base '' Set.range i'.base,
      c.isClosedEmbedding.isClosedMap _ i'.isClosedEmbedding.isClosed_range⟩
    have hZ' : Z' < Z := by
      refine SetLike.lt_iff_le_and_exists.2 ⟨fun x ⟨w, _, hw⟩ ↦ hcZ ⟨w, hw⟩,
        c.base v, hcZ ⟨v, rfl⟩, fun ⟨w, hw, hwv⟩ ↦ ?_⟩
      rw [c.isClosedEmbedding.injective hwv, hi'] at hw
      exact hw hv
    have hrange : Set.range (i' ≫ c).base ⊆ Z' := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact subset_rfl
    exact (boundedConstructible _).prop_of_iso
      (Φ.mapIso ((rightDerivedLowerStarComp Λ i' c).app _).symm)
      (ih Z' hZ' D'' (i' ≫ c) hrange _ (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ
        i' _ (boundedConstructible_singleFunctor_zero_obj Λ G hGc)))

include Φ in
/-- **Dévissage of bounded constructible complexes to lisse sheaves on locally closed
subschemes**: on a scheme `T` with noetherian underlying space, a triangulated functor `Φ` which
maps the extensions by zero `Rc_* j_! Rc'_* L` of the lisse sheaves `L` along the locally closed
immersions `E ⟶ W ⊆ D ⟶ T` to bounded constructible complexes
(`ProEtale.CondensedRing.LisseHypothesis`) maps all bounded constructible complexes to bounded
constructible complexes. -/
theorem boundedConstructible_obj_of_forall_lisse [TopologicalSpace.NoetherianSpace T]
    (hΦ : LisseHypothesis Λ Φ)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (hK : boundedConstructible _ K) :
    boundedConstructible (condensedRingObj Λ Y) (Φ.obj K) := by
  have key : ∀ Z : TopologicalSpace.Closeds T, ∀ (D : Scheme.{u}) (c : D ⟶ T)
      [IsClosedImmersion c], Set.range c.base ⊆ Z →
      ∀ M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
        (condensedRingObj Λ D)), boundedConstructible _ M →
        boundedConstructible (condensedRingObj Λ Y) (Φ.obj ((R((c)_*⟦Λ⟧)).obj M)) := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
      intro D c _ hcZ M hM
      have : TopologicalSpace.NoetherianSpace D :=
        c.isClosedEmbedding.isInducing.noetherianSpace
      exact boundedConstructible_obj_of_forall_singleFunctor (R((c)_*⟦Λ⟧) ⋙ Φ)
        (fun G hG ↦ boundedConstructible_lisse_step hΦ Z ih c hcZ G hG) hM
  have : IsEmpty (⊥ : T.Opens).toScheme := ⟨fun x ↦ by obtain ⟨x, hx⟩ := x; exact hx⟩
  have : QuasiCompact (⊥ : T.Opens).ι := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have hc : IsCompl (Set.range (𝟙 T : T ⟶ T).base) (Set.range (⊥ : T.Opens).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact ⟨Set.disjoint_iff.2 fun x ⟨_, hx⟩ ↦ hx,
      codisjoint_iff.2 (Set.eq_univ_of_forall fun x ↦ Or.inl ⟨x, rfl⟩)⟩
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ (⊥ : T.Opens).ι (𝟙 T)
    hc (K := K) (isZero_derivedCategory_of_isEmpty' Λ _)
  exact (boundedConstructible _).prop_of_iso
    (Φ.mapIso (asIso ((derivedUpperStarLowerStarAdjunction Λ (𝟙 T)).unit.app K)).symm)
    (key ⊤ T (𝟙 T) (fun _ _ ↦ trivial) _
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ (𝟙 T) K hK))

end Devissage

end AlgebraicGeometry.ProEtale.CondensedRing
