/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Compactification.CommonRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
open CompactificationReindexing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard Profinite.padicAlgClCondensedRing

private theorem unit_shift_of_counit
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ]
    (a : F ⊣ G) [NatTrans.CommShift a.counit ℤ] :
    NatTrans.CommShift a.unit ℤ := by
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.commShiftIso_id_hom_app, Functor.commShiftIso_comp_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp]
  symm
  change a.unit.app (X⟦n⟧) ≫
      G.map ((F.commShiftIso n).hom.app X) ≫ (G.commShiftIso n).hom.app (F.obj X) =
    (a.unit.app X) ⟦n⟧'
  rw [← cancel_mono ((G.commShiftIso n).inv.app (F.obj X))]
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  apply (a.homEquiv _ _).symm.injective
  have h := Adjunction.CommShift.compatibilityCounit_left a
    (F.commShiftIso n) (G.commShiftIso n) (fun Y ↦ by
      simpa [Functor.commShiftIso_comp_hom_app, Category.assoc] using
        (NatTrans.shift_app_comm a.counit n Y).symm) X
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    a.counit_naturality]
  rw [← Category.assoc]
  erw [a.left_triangle_components (X⟦n⟧), Category.id_comp]
  exact h

private theorem open_adj_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U T : Scheme.{u}}
    (s : U ⟶ T) [IsOpenImmersion s] : (oa Λ s).CommShift ℤ :=
  commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight Λ s

attribute [local instance] open_adj_shift

private theorem clopen_unit_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U T : Scheme.{u}}
    (s : U ⟶ T) [IsOpenImmersion s] (hs : IsClosed (Set.range s)) :
    NatTrans.CommShift (clopenAdjunction Λ s hs).unit ℤ := by
  have := openUnit_isIso Λ s
  have : (oa Λ s).CommShift ℤ :=
    commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight Λ s
  have he : (clopenAdjunction Λ s hs).counit = inv (oa Λ s).unit := by
    unfold clopenAdjunction
    exact (clopenAdjunction_existsUnique Λ s hs).exists.choose_spec
  have : NatTrans.CommShift (clopenAdjunction Λ s hs).counit ℤ := by
    rw [he]
    infer_instance
  exact unit_shift_of_counit _

private theorem inverse_mate_shift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (β : TwoSquare R₁ H G R₂) [β.natTrans.CommShift ℤ] :
    ((mateEquiv a₁ a₂).symm β).natTrans.CommShift ℤ := by
  change ((Functor.leftUnitor (G ⋙ L₂)).inv ≫
    Functor.whiskerRight a₁.unit (G ⋙ L₂) ≫
    (Functor.associator (L₁ ⋙ R₁) G L₂).inv ≫
    Functor.whiskerRight (Functor.associator L₁ R₁ G).hom L₂ ≫
    Functor.whiskerRight (Functor.whiskerLeft L₁ β.natTrans) L₂ ≫
    Functor.whiskerRight (Functor.associator L₁ H R₂).inv L₂ ≫
    (Functor.associator (L₁ ⋙ H) R₂ L₂).hom ≫
    Functor.whiskerLeft (L₁ ⋙ H) a₂.counit ≫
    (Functor.rightUnitor (L₁ ⋙ H)).hom).CommShift ℤ
  infer_instance

private theorem beta_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback w j' j v) :
    NatTrans.CommShift (beta Λ sq).hom ℤ := by
  have : NatTrans.CommShift (pullbackSquareComparison Λ sq.toCommSq).hom ℤ := by
    rw [pullbackSquareComparison_eq]
    dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
    have := NatTrans.CommShift.eqToHom_congrArg (A := ℤ)
      (fun f : A' ⟶ B ↦ P Λ f) sq.toCommSq.w.symm
    infer_instance
  have : NatTrans.CommShift (openMate Λ sq.toCommSq) ℤ := by
    unfold openMate
    exact inverse_mate_shift (oa Λ j) (oa Λ j') _
  unfold beta
  exact NatTrans.CommShift.of_iso_inv _ ℤ

private theorem left_adjoint_uniq_refl_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {R : D ⥤ C} [F.CommShift ℤ] (a : F ⊣ R) :
    NatTrans.CommShift (a.leftAdjointUniq (a.ofNatIsoRight (Iso.refl R))).hom ℤ := by
  have he : a.ofNatIsoRight (Iso.refl R) = a := by
    apply Adjunction.ext
    ext X
    simp
  rw [he, Adjunction.leftAdjointUniq_refl]
  infer_instance

private theorem jCongr_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B : Scheme.{u}} {j i : A ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion i] (h : j = i) :
    NatTrans.CommShift (jCongr Λ h).hom ℤ := by
  subst i
  exact left_adjoint_uniq_refl_shift (oa Λ j)

private theorem jComp_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B C : Scheme.{u}}
    (j : A ⟶ B) (i : B ⟶ C) [IsOpenImmersion j] [IsOpenImmersion i] :
    NatTrans.CommShift (jComp Λ j i).hom ℤ := by
  dsimp only [jComp, Iso.symm_hom]
  infer_instance

private theorem rComp_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    NatTrans.CommShift (rightDerivedLowerStarComp Λ f g).hom ℤ := by
  infer_instance

private theorem whisker_homEquiv_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {L : D ⥤ E} {R : E ⥤ D} [L.CommShift ℤ] [R.CommShift ℤ]
    (a : L ⊣ R) [a.CommShift ℤ] {F : C ⥤ D} {G : C ⥤ E}
    [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⋙ L ⟶ G) [τ.CommShift ℤ] :
    NatTrans.CommShift
      (show F ⟶ G ⋙ R from (a.whiskerRight C).homEquiv F G τ) ℤ := by
  apply NatTrans.CommShift.of_homEquiv a τ
  intro X
  dsimp [Adjunction.homEquiv, Adjunction.whiskerRight]
  simp

private theorem projector_word_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F G H : C ⥤ E} {A : C ⥤ D} {B : D ⥤ C} {J : C ⥤ D} {K : D ⥤ E}
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [A.CommShift ℤ]
    [B.CommShift ℤ] [J.CommShift ℤ] [K.CommShift ℤ]
    (β : F ⟶ A ⋙ K) [β.CommShift ℤ] (η : 𝟭 D ⟶ B ⋙ J) [η.CommShift ℤ]
    (q : A ⋙ B ≅ 𝟭 C) [q.hom.CommShift ℤ]
    (c : J ⋙ K ⟶ H) [c.CommShift ℤ] (e : H ⟶ G) [e.CommShift ℤ] :
    NatTrans.CommShift (β ≫ Functor.whiskerLeft A (Functor.whiskerRight η K) ≫
      Functor.whiskerRight q.hom (J ⋙ K) ≫ (Functor.leftUnitor (J ⋙ K)).hom ≫ c ≫ e) ℤ := by
  have he : β ≫ Functor.whiskerLeft A (Functor.whiskerRight η K) ≫
      Functor.whiskerRight q.hom (J ⋙ K) ≫ (Functor.leftUnitor (J ⋙ K)).hom ≫ c ≫ e =
      β ≫ Functor.whiskerLeft A ((Functor.leftUnitor K).inv ≫
        Functor.whiskerRight η K ≫ (Functor.associator B J K).hom) ≫
      (Functor.associator A B (J ⋙ K)).inv ≫ Functor.whiskerRight q.hom (J ⋙ K) ≫
      (Functor.leftUnitor (J ⋙ K)).hom ≫ c ≫ e := by
    ext X
    simp
  rw [he]
  infer_instance

private theorem whisker_comp_shift
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift V ℤ]
    {A : C ⥤ D} {B : C ⥤ E} {R : E ⥤ D} {S : D ⥤ V} {T : E ⥤ V}
    [A.CommShift ℤ] [B.CommShift ℤ] [R.CommShift ℤ] [S.CommShift ℤ] [T.CommShift ℤ]
    (m : A ⟶ B ⋙ R) [m.CommShift ℤ] (e : R ⋙ S ⟶ T) [e.CommShift ℤ] :
    NatTrans.CommShift (Functor.whiskerRight m S ≫ Functor.whiskerLeft B e) ℤ := by
  have he : Functor.whiskerRight m S ≫ Functor.whiskerLeft B e =
      Functor.whiskerRight m S ≫ (Functor.associator B R S).hom ≫
        Functor.whiskerLeft B e := by
    ext X
    simp
  rw [he]
  infer_instance

set_option maxHeartbeats 800000 in
-- Native compositor elaboration needs more than the default heartbeat limit.
private theorem refinement_shift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
    NatTrans.CommShift (refinement Λ r) ℤ := by
  have ha : NatTrans.CommShift (refinementAdjunct Λ r) ℤ := by
    have := (section_clopen r).1
    have := clopen_unit_shift Λ (refinementSection r) (section_clopen r).2
    have := beta_shift Λ (IsPullback.of_hasPullback c₂.i r.hom)
    have hst : refinementSection r ≫ pullback.fst c₂.i r.hom = 𝟙 X :=
      pullback.lift_fst _ _ _
    have : NatTrans.CommShift (eqToHom (congrArg (P Λ) hst)) ℤ :=
      NatTrans.CommShift.eqToHom_congrArg (A := ℤ) (P Λ) hst
    have hsi : refinementSection r ≫ pullback.snd c₂.i r.hom = c₁.i :=
      pullback.lift_snd _ _ _
    have := jCongr_shift Λ hsi
    have := jComp_shift Λ (refinementSection r) (pullback.snd c₂.i r.hom)
    let q : P Λ (pullback.fst c₂.i r.hom) ⋙ P Λ (refinementSection r) ≅ 𝟭 (D Λ X) :=
      (leftDerivedUpperStarComp Λ (refinementSection r) (pullback.fst c₂.i r.hom)).symm ≪≫
        eqToIso (congrArg (P Λ) hst) ≪≫ leftDerivedUpperStarId Λ X
    have : NatTrans.CommShift q.hom ℤ := by
      dsimp only [q, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
      infer_instance
    unfold refinementAdjunct
    exact projector_word_shift (beta Λ (IsPullback.of_hasPullback c₂.i r.hom)).hom
      (clopenAdjunction Λ (refinementSection r) (section_clopen r).2).unit q
      (jComp Λ (refinementSection r) (pullback.snd c₂.i r.hom)).hom (jCongr Λ hsi).hom
  let m : J Λ c₂.i ⟶ J Λ c₁.i ⋙ R Λ r.hom :=
    ((derivedUpperStarLowerStarAdjunction Λ r.hom).whiskerRight _).homEquiv _ _
      (refinementAdjunct Λ r)
  have hm : NatTrans.CommShift m ℤ := by
    exact whisker_homEquiv_shift (derivedUpperStarLowerStarAdjunction Λ r.hom)
      (refinementAdjunct Λ r)
  have := NatTrans.CommShift.eqToHom_congrArg (A := ℤ) (R Λ) r.hom_g
  have := rComp_shift Λ r.hom c₂.g
  unfold refinement
  change NatTrans.CommShift (Functor.whiskerRight m (R Λ c₂.g) ≫
    Functor.whiskerLeft (J Λ c₁.i) ((rightDerivedLowerStarComp Λ r.hom c₂.g).hom ≫
      (eqToIso (congrArg (R Λ) r.hom_g)).hom)) ℤ
  exact whisker_comp_shift m ((rightDerivedLowerStarComp Λ r.hom c₂.g).hom ≫
    eqToHom (congrArg (R Λ) r.hom_g))

private theorem iso_hom_shift_of_cocycle
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G H : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (a : F ≅ G) (b : G ≅ H) (c : F ≅ H)
    [NatTrans.CommShift b.hom ℤ] [NatTrans.CommShift c.hom ℤ]
    (h : a ≪≫ b = c) : NatTrans.CommShift a.hom ℤ := by
  have he : a.hom = c.hom ≫ b.inv := by
    rw [← h]
    simp
  rw [he]
  infer_instance

private theorem restricted_iso_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (I : C ⥤ D) [I.CommShift ℤ] {F G : D ⥤ E}
    [F.CommShift ℤ] [G.CommShift ℤ] (e : I ⋙ F ≅ I ⋙ G)
    (τ : F ⟶ G) [τ.CommShift ℤ]
    (h : ∀ X, e.hom.app X = τ.app (I.obj X)) : NatTrans.CommShift e.hom ℤ := by
  have he : e.hom = Functor.whiskerLeft I τ := by
    ext X
    exact h X
  rw [he]
  infer_instance

private theorem family_comparison_shift
    {C D I : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : I → C ⥤ D) [∀ i, (F i).CommShift ℤ] (R : I → I → Type*)
    (e : ∀ i j, F i ≅ F j) (cocycle : ∀ i j k, e i j ≪≫ e j k = e i k)
    (common : ∀ i j, ∃ k, Nonempty (R k i) ∧ Nonempty (R k j))
    (normalized : ∀ i j, R j i → NatTrans.CommShift (e i j).hom ℤ) (i j : I) :
    NatTrans.CommShift (e i j).hom ℤ := by
  obtain ⟨k, ⟨r⟩, ⟨s⟩⟩ := common i j
  have := normalized i k r
  have := normalized j k s
  exact iso_hom_shift_of_cocycle (e i j) (e j k) (e i k) (cocycle i j k)

-- Match the coefficient-instance presentation used by `System` in the definitions module.
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

private theorem system_restricted_iso_shift (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [HasShift (ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) ℤ]
    [(constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι.CommShift ℤ]
    {c d : Compactification f}
    (τ : CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) c ⟶
      CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) d)
    [hτ : τ.CommShift ℤ]
    (e : (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
        CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) c ≅
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
        CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) d)
    (h : ∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      e.hom.app K = τ.app K.obj) :
    NatTrans.CommShift e.hom ℤ := by
  exact restricted_iso_shift
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι e τ h

private theorem system_refinement_shift (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [HasShift (ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) ℤ]
    [(constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι.CommShift ℤ]
    (S : System ℓ f) (c d : Compactification f) (r : d.Refinement c) :
    NatTrans.CommShift (S.comparison c d).hom ℤ := by
  exact system_restricted_iso_shift ℓ
    (τ := CompactificationReindexing.refinement (Profinite.padicAlgClRingObj ℓ) r)
    (hτ := refinement_shift (Profinite.padicAlgClRingObj ℓ) r)
    (e := S.comparison c d) (h := S.refinement c d r)

private theorem system_comparison_shift (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    [HasShift (ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) ℤ]
    [(constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι.CommShift ℤ]
    (S : System ℓ f) (c d : Compactification f) :
    NatTrans.CommShift (S.comparison c d).hom ℤ := by
  exact family_comparison_shift
    (fun c ↦ (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).ι ⋙
      CompactificationReindexing.F (Profinite.padicAlgClRingObj ℓ) c)
    (fun c d ↦ c.Refinement d) S.comparison S.comparison_cocycle
    Compactification.exists_common_refinement (system_refinement_shift ℓ S) c d

set_option linter.unusedVariables false in
-- The published statement retains the finite-field assumption hℓ.
/-- Shift compatibility of the three compactification comparison systems. For each
system, use a common refinement and the comparison cocycle. The defining refinement
map is the normalized proper/open restriction word; the qcqs calculus gives its
shift square, and the inverse square follows with `NatTrans.CommShift.of_iso_inv`.
Pasting the two refinement maps and the cocycle gives the comparison component.
This is done independently for `h₀`, `g₀`, and `h₀ ≫ g₀` after geometric base
change. Source: Stacks Tags 0F7J and 05SU.
(blueprint: new-m5-qcqs-composition-core-shift-alpha-comparison). -/
theorem qcqsCompositionCoreShiftAlphaComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj X₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Z₀).left)).IsTriangulated]
    [(bc ℓ (((Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap D.k₀ D.k)))).obj Y₀).left)).IsTriangulated]
    (A : Comparisons ℓ (modelMap D h₀) (modelMap D g₀)) :
    (∀ c d : Compactification (modelMap D h₀),
      NatTrans.CommShift (A.sh.comparison c d).hom ℤ) ∧
    (∀ c d : Compactification (modelMap D g₀),
      NatTrans.CommShift (A.sg.comparison c d).hom ℤ) ∧
    (∀ c d : Compactification (modelMap D h₀ ≫ modelMap D g₀),
      NatTrans.CommShift (A.sgh.comparison c d).hom ℤ) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let : QuasiCompact (modelMap D h₀) :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) t h₀ inferInstance
  let : QuasiCompact (modelMap D g₀) :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) t g₀ inferInstance
  exact ⟨system_comparison_shift ℓ A.sh, system_comparison_shift ℓ A.sg,
    system_comparison_shift ℓ A.sgh⟩
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
