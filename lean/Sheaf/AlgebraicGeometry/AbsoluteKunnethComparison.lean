/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryKunnethMap

/-!
# The absolute and relative canonical Künneth arrows

Source: Stacks Project, Tag 0F1E, the adjoint definition of the Künneth map.
(blueprint: lem-pur-absolute-kunneth-comparison).
-/

@[expose] public section

universe u uA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

private theorem transpose_comp_conjugate
    {C B : Type*} [Category C] [Category B]
    {L₁ L₂ : C ⥤ B} {R₁ R₂ : B ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {P : C} {V : B} (a : P ⟶ R₁.obj V) :
    (adj₂.homEquiv P V).symm (a ≫ (conjugateEquiv adj₁ adj₂ α).app V) =
      α.app P ≫ (adj₁.homEquiv P V).symm a := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc, conjugateEquiv_counit,
    ← reassoc_of% (α.naturality a)]

private theorem transpose_composite_adjunction
    {C B E : Type*} [Category C] [Category B] [Category E]
    {F₀ : C ⥤ B} {G₀ : B ⥤ C} {F₁ : B ⥤ E} {G₁ : E ⥤ B}
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁)
    {P : C} {V : B} {W : E} (a : P ⟶ G₀.obj V) (κ : V ⟶ G₁.obj W) :
    ((adj₀.comp adj₁).homEquiv P W).symm (a ≫ G₀.map κ) =
      F₁.map ((adj₀.homEquiv P V).symm a) ≫ (adj₁.homEquiv V W).symm κ := by
  rw [Adjunction.comp_homEquiv]
  change (adj₁.homEquiv _ _).symm ((adj₀.homEquiv _ _).symm _) = _
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]

private theorem transpose_transport_tensorMate
    {C B E : Type*} [Category C] [Category B] [Category E]
    (T : C ⥤ C ⥤ C) (T' : B ⥤ B ⥤ B)
    {F : C ⥤ B} {R : B ⥤ C} {G : B ⥤ E} {S : E ⥤ B}
    {F' : C ⥤ E} {R' : E ⥤ C}
    (adj₀ : F ⊣ R) (adjG : G ⊣ S) (adj₁ : F' ⊣ R') (α : F' ⟶ F ⋙ G)
    (δ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ B).obj F).obj F).obj T')
    {P Q : C} {V W : B} {Z : E} (a : F.obj P ⟶ V) (b : F.obj Q ⟶ W)
    (m : G.obj ((T'.obj V).obj W) ⟶ Z) :
    (adj₁.homEquiv _ _).symm
        (ordinaryKunnethTensorMate T T' F R adj₀ δ a b ≫
          R.map ((adjG.homEquiv _ _) m) ≫
          (conjugateEquiv (adj₀.comp adjG) adj₁ α).app Z) =
      α.app ((T.obj P).obj Q) ≫
        G.map ((δ.app P).app Q ≫ (T'.map a).app _ ≫ (T'.obj _).map b) ≫ m := by
  rw [← Category.assoc, transpose_comp_conjugate (adj₀.comp adjG) adj₁ α,
    transpose_composite_adjunction adj₀ adjG, ordinaryKunnethTensorMate,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

private instance evaluationMonoidal {C A : Type*} [Category C] [Category A]
    [MonoidalCategory A] (U : C) : ((evaluation C A).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

section
variable {C A : Type*} [Category C] [Category A] [MonoidalCategory A]
  (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  {T : C} (hT : IsTerminal T)
attribute [local instance] Sheaf.monoidalCategory

private noncomputable instance sectionsMonoidal : ((sheafSections J A).obj (op T)).LaxMonoidal :=
  inferInstanceAs (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)).LaxMonoidal

private instance constantPresheafAdj_monoidal : (constantPresheafAdj A hT).IsMonoidal := by
  constructor
  · simp [constantPresheafAdj, Functor.LaxMonoidal.ε, Functor.OplaxMonoidal.η]
  · intro X Y
    simp [constantPresheafAdj, Functor.LaxMonoidal.μ, Functor.OplaxMonoidal.δ]

private instance constantSheafAdj_monoidal : (constantSheafAdj J A hT).IsMonoidal := by
  unfold constantSheafAdj
  infer_instance
end

section Pullback
variable {C D A : Type*} [Category C] [Category D] [Category A]
  [MonoidalCategory A] [BraidedCategory A]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [F.IsContinuous J K]
attribute [local instance] Sheaf.monoidalCategory

private noncomputable def precomposeEvaluationIso (T : C) :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ (evaluation Cᵒᵖ A).obj (op T) ≅
      (evaluation Dᵒᵖ A).obj (op (F.obj T)) := Iso.refl _

private instance precomposeEvaluation_monoidal (T : C) : NatTrans.IsMonoidal
    (precomposeEvaluationIso (A := A) F T).hom where
  unit := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.ε]
  tensor P Q := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.μ]

private instance sheafSectionsNatIsoEvaluation_monoidal {T : C} : NatTrans.IsMonoidal
    (sheafSectionsNatIsoEvaluation J A (X := T)).hom := by
  change NatTrans.IsMonoidal (𝟙 (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)))
  infer_instance

private noncomputable def pushforwardSectionsIso (T : C) :
    F.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op T) ≅
      (sheafSections K A).obj (op (F.obj T)) :=
  Functor.isoWhiskerLeft _ (sheafSectionsNatIsoEvaluation J A) ≪≫
    (Functor.associator (F.sheafPushforwardContinuous A J K)
      (sheafToPresheaf J A) ((evaluation Cᵒᵖ A).obj (op T))).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
        F A J K).symm ((evaluation Cᵒᵖ A).obj (op T)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (precomposeEvaluationIso F T) ≪≫
    (sheafSectionsNatIsoEvaluation K A).symm

private instance pushforwardSections_monoidal (T : C) : NatTrans.IsMonoidal
    (pushforwardSectionsIso (A := A) F J K T).hom := by
  dsimp only [pushforwardSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

omit [MonoidalCategory A] [BraidedCategory A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
private theorem pushforwardUnderlying_inv_app (P : Sheaf K A) :
    (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).inv.app P = 𝟙 _ := by
  have h :=
    (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).hom_inv_id_app P
  rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    Category.id_comp] at h
  exact h

end Pullback

section SectionMaps
variable {C B : Type*} [Category C] [Category B] [MonoidalCategory B]
    (J : GrothendieckTopology C) [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
attribute [local instance] Sheaf.monoidalCategory

private theorem sectionsMap_monoidal {T U : C} (a : T ⟶ U) :
    NatTrans.IsMonoidal ((sheafSections J B).map a.op) := by
  constructor
  · with_unfolding_all change (𝟙 _ ≫ _) ≫ _ = 𝟙 _ ≫ _
    simpa using ((Functor.LaxMonoidal.ε (sheafToPresheaf J B)).naturality a.op).symm
  · intro P Q
    with_unfolding_all change (𝟙 _ ≫ _) ≫ _ = _ ≫ (𝟙 _ ≫ _)
    simpa using ((Functor.LaxMonoidal.μ (sheafToPresheaf J B) P Q).naturality a.op).symm
end SectionMaps

omit [HasSmallSiteSheafify A] [MonoidalPreadditive A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
private theorem terminalSectionsIso_monoidal {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.IsMonoidal (lowerStarCompSheafSectionsTerminalIso A f).hom := by
  let e := (PreservesTerminal.iso f.Etale).op.symm
  have h := sectionsMap_monoidal X.smallEtaleTopology (B := A) e.hom.unop
  have h' : NatTrans.IsMonoidal ((sheafSections X.smallEtaleTopology A).map e.hom) := h
  let : NatTrans.IsMonoidal ((sheafSections X.smallEtaleTopology A).map e.hom) := h'
  have hmono : NatTrans.IsMonoidal
      ((pushforwardSectionsIso (A := A) f.Etale S.smallEtaleTopology X.smallEtaleTopology
        (⊤_ S.Etale)).hom ≫ (sheafSections X.smallEtaleTopology A).map e.hom) := by
    infer_instance
  have he : (pushforwardSectionsIso (A := A) f.Etale S.smallEtaleTopology
        X.smallEtaleTopology (⊤_ S.Etale)).hom ≫
      (sheafSections X.smallEtaleTopology A).map e.hom =
      (lowerStarCompSheafSectionsTerminalIso A f).hom := by
    ext P
    simp [pushforwardSectionsIso, precomposeEvaluationIso,
      lowerStarCompSheafSectionsTerminalIso, e, pushforwardUnderlying_inv_app]
  rw [he] at hmono
  exact hmono

omit [HasSmallSiteSheafify A] [MonoidalPreadditive A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
private theorem constantPullback_monoidal {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.IsMonoidal (Scheme.upperStarConstantSheafIso A f).inv := by
  let adj₁ := (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal).comp
    (upperStarLowerStarAdjunction A f)
  let adj₂ := constantSheafAdj X.smallEtaleTopology A terminalIsTerminal
  let e := lowerStarCompSheafSectionsTerminalIso A f
  let : NatTrans.IsMonoidal e.hom := terminalSectionsIso_monoidal A f
  have h := isMonoidal_conjugateEquiv_symm adj₁ adj₂ e.hom
  have he : (conjugateEquiv adj₁ adj₂).symm e.hom =
      (Scheme.upperStarConstantSheafIso A f).inv := by
    ext P
    simp [Scheme.upperStarConstantSheafIso, Adjunction.leftAdjointUniq,
      conjugateEquiv_symm_apply_app, adj₁, adj₂, e]
  rw [he] at h
  exact h


attribute [-instance] evaluationMonoidal sectionsMonoidal
  constantPresheafAdj_monoidal constantSheafAdj_monoidal precomposeEvaluation_monoidal
  sheafSectionsNatIsoEvaluation_monoidal pushforwardSections_monoidal

/-- The canonical right-adjoint comparison associated to pullback of constant complexes.
It is defined by conjugacy, so its counit equation is an adjunction identity.
Source: Stacks Tag 0F1E (blueprint: lem-pur-absolute-kunneth-comparison). -/
noncomputable def ordinaryKunnethSectionsIso {X S : Scheme.{u}} (f : X ⟶ S) :
    (lowerStar A f).rightDerivedFunctor ⋙ rightDerivedGlobalSections A S ≅
      rightDerivedGlobalSections A X :=
  conjugateIsoEquiv
    ((derivedConstantGlobalSectionsAdjunction A S).comp
      (derivedUpperStarLowerStarAdjunction A f))
    (derivedConstantGlobalSectionsAdjunction A X) (derivedConstantPullbackIso A f)

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] in
private theorem sectionsIso_counit {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (constantSheaf X.smallEtaleTopology A).leftDerivedFunctor.map
        ((ordinaryKunnethSectionsIso A f).hom.app K) ≫
      (derivedConstantGlobalSectionsAdjunction A X).counit.app K =
    (derivedConstantPullbackIso A f).hom.app
        ((rightDerivedGlobalSections A S).obj ((lowerStar A f).rightDerivedFunctor.obj K)) ≫
      (upperStar A f).leftDerivedFunctor.map
        ((derivedConstantGlobalSectionsAdjunction A S).counit.app
          ((lowerStar A f).rightDerivedFunctor.obj K)) ≫
      (derivedUpperStarLowerStarAdjunction A f).counit.app K := by
  simpa only [ordinaryKunnethSectionsIso, conjugateIsoEquiv_apply_hom,
    Adjunction.comp_counit_app, Functor.comp_obj, Category.assoc] using
    (conjugateEquiv_counit
      ((derivedConstantGlobalSectionsAdjunction A S).comp
        (derivedUpperStarLowerStarAdjunction A f))
      (derivedConstantGlobalSectionsAdjunction A X)
      (derivedConstantPullbackIso A f).hom K)

/-- Relative Künneth, transported through the constant-complex adjunctions.
The point tensor comparison is the mate of the tensor of its two counits.
All comparison data are explicit canonical adjunction maps.
Source: Stacks Tag 0F1E (blueprint: lem-pur-absolute-kunneth-comparison). -/
noncomputable def ordinaryRelativeGlobalKunnethMap
    {S X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (w : q ≫ g = p ≫ f)
    [(constantSheaf S.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⊗
        (rightDerivedGlobalSections A Y).obj M ⟶
      (rightDerivedGlobalSections A Z).obj
        (((derivedTensor A Z).obj ((upperStar A p).leftDerivedFunctor.obj K)).obj
          ((upperStar A q).leftDerivedFunctor.obj M)) :=
  tensorHom ((ordinaryKunnethSectionsIso A f).inv.app K)
      ((ordinaryKunnethSectionsIso A g).inv.app M) ≫
    ordinaryKunnethTensorMate (curriedTensor (DerivedCategory A))
      (derivedTensor A S) (constantSheaf S.smallEtaleTopology A).leftDerivedFunctor
      (rightDerivedGlobalSections A S) (derivedConstantGlobalSectionsAdjunction A S)
      (constantSheaf S.smallEtaleTopology A).leftDerivedTensorComparison
      ((derivedConstantGlobalSectionsAdjunction A S).counit.app _)
      ((derivedConstantGlobalSectionsAdjunction A S).counit.app _) ≫
    (rightDerivedGlobalSections A S).map (kunnethMap A p q f g (p ≫ f) rfl w K M) ≫
    (ordinaryKunnethSectionsIso A (p ≫ f)).hom.app _

/-- The tensor-of-pulled-counits adjunct is relative Künneth transported by the
canonical right-adjoint comparisons for constants.

Source: Stacks Project, Tag 0F1E, terminal-topos specialization of the adjoint
construction in blueprint order 1740.
(blueprint: lem-pur-absolute-kunneth-comparison).

Proof: The comparisons identifying a constant complex on a source with the pullback
of a constant complex compose. This follows on sheaves from the constant-pullback
composition law, and after deriving from the counit normalization of the exact-functor
composition comparisons. They respect tensor: the constant-presheaf tensor constraints
have identity components, sheafification is monoidal, and the derived tensor comparison
respects monoidal natural isomorphisms and compositions of exact functors.
Transpose the claimed equality by the constants/sections adjunction on Z. The conjugate
counit equations for ordinaryKunnethSectionsIso replace each sections comparison by the
constant-pullback comparison followed by the composite adjunction counit. Naturality
moves the tensor of the two sections comparisons past the constant tensor constraint.
Expand the two Künneth adjuncts. Use the constant-pullback composition law for p,f and
q,g, and tensor compatibility to identify the front comparison. The unit and counit
at S cancel by the two triangle identities. Both sides now equal the constant tensor
comparison on Z followed by the tensor of the pulled-back counits on X and Y.
Injectivity of the adjunction bijection proves equality. This argument needs neither
coefficient finiteness, finite type, cartesianness, nor an equivalence at S; the empty
scheme and zero complexes obey the same adjunction identities. -/
theorem ordinaryGlobalKunnethMap_eq_relative
    {S X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (w : q ≫ g = p ≫ f)
    [(constantSheaf S.smallEtaleTopology A).PreservesFlat]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ordinaryGlobalKunnethMap A p q K M =
      ordinaryRelativeGlobalKunnethMap A p q f g w K M := by sorry

end AlgebraicGeometry.Etale
