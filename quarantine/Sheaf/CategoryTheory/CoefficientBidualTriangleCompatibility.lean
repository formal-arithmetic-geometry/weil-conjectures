/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import Sheaf.CategoryTheory.SignedDerivedInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
import Sheaf.CategoryTheory.RingedSiteSignedDualRestriction
import all Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.CategoryTheory.CoefficientBidualEvaluationShiftOne
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Coefficient biduality, signed shifts, triangles and scalar localization

Source: Stacks Project, sites-cohomology.tex, Tags 08JC, 0A97 and 08JB;
blueprint lem-coef-rational-retract-evaluation, proof paragraph 3
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r w w' a b k
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses CategoryTheory.Pretriangulated
namespace CategoryTheory.CoefficientBidual

section General
variable {E : Type a} [Category.{b} E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  (F : E ⥤ E) (d : 𝟭 E ⟶ F) [F.CommShift ℤ]

/-- All three triangle squares, and closure of the invertibility locus.
Source: Stacks 08JC and derived.tex 0144
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def TriangleCompatibility : Prop :=
  F.IsTriangulated ∧ NatTrans.CommShift d ℤ ∧
    (∀ T : Triangle E, T ∈ distTriang E →
      ∃ m : T ⟶ F.mapTriangle.obj T,
        m.hom₁ = d.app T.obj₁ ∧ m.hom₂ = d.app T.obj₂ ∧ m.hom₃ = d.app T.obj₃) ∧
    (∀ (X : E) (n : ℤ), IsIso (d.app X) ↔ IsIso (d.app (X⟦n⟧))) ∧
    (∀ T : Triangle E, T ∈ distTriang E →
      (IsIso (d.app T.obj₁) ∧ IsIso (d.app T.obj₂) → IsIso (d.app T.obj₃)) ∧
      (IsIso (d.app T.obj₁) ∧ IsIso (d.app T.obj₃) → IsIso (d.app T.obj₂)) ∧
      (IsIso (d.app T.obj₂) ∧ IsIso (d.app T.obj₃) → IsIso (d.app T.obj₁)))

/-- Scalar extension of an exact shift-compatible transformation: its components are Q(d), and its
shift comparison is the scalar extension of the given comparison.
Source: blueprint scalar localization and Stacks 08JC
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def ScalarCompatibility (A : Type k) [CommRing A] [Linear A E]
    [F.Additive] [F.Linear A] (s : A)
    [HasZeroObject (ScalarLocalization A E s)] [HasShift (ScalarLocalization A E s) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization A E s) n).Additive]
    [Pretriangulated (ScalarLocalization A E s)]
    [(ScalarLocalization.localization A E s).CommShift ℤ] : Prop :=
  ∃ S : (ScalarLocalization.map A E s F).CommShift ℤ,
    (fun [_shiftInst : (ScalarLocalization.map A E s F).CommShift ℤ] ↦
      ∃ delta : 𝟭 (ScalarLocalization A E s) ⟶ ScalarLocalization.map A E s F,
        (∀ X : ScalarLocalization A E s,
          delta.app X = (ScalarLocalization.localization A E s).map (d.app X.obj)) ∧
        (∀ (X : E) (n : ℤ),
          (ScalarLocalization.map A E s F).map
              (((ScalarLocalization.localization A E s).commShiftIso n).hom.app X) ≫
            ((ScalarLocalization.map A E s F).commShiftIso n).hom.app
              ((ScalarLocalization.localization A E s).obj X) =
          (ScalarLocalization.localization A E s).map ((F.commShiftIso n).hom.app X) ≫
            ((ScalarLocalization.localization A E s).commShiftIso n).hom.app (F.obj X)) ∧
        TriangleCompatibility (ScalarLocalization.map A E s F) delta) (_shiftInst := S)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The categorical conclusions follow from exactness and shift compatibility. -/
private theorem triangleCompatibility_of [F.IsTriangulated] [NatTrans.CommShift d ℤ] :
    TriangleCompatibility F d := by
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro T _
    let m := ((Functor.mapTriangleIdIso E).inv.app T) ≫ (NatTrans.mapTriangle d).app T
    refine ⟨m, ?_, ?_, ?_⟩
    · change 𝟙 _ ≫ d.app T.obj₁ = _
      exact Category.id_comp _
    · change 𝟙 _ ≫ d.app T.obj₂ = _
      exact Category.id_comp _
    · change 𝟙 _ ≫ d.app T.obj₃ = _
      exact Category.id_comp _
  · intro X n
    have h := NatTrans.app_shift d n X
    constructor
    · intro hX
      let := hX
      rw [h]
      infer_instance
    · intro hX
      let := hX
      have hs : IsIso ((d.app X)⟦n⟧') := by
        rw [NatTrans.shift_app d n X]
        infer_instance
      exact isIso_of_reflects_iso (d.app X) (shiftFunctor E n)
  · intro T hT
    exact ⟨fun h ↦ NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ d hT h.1 h.2,
      fun h ↦ NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ d hT h.1 h.2,
      fun h ↦ NatTrans.isIso_app_obj₁_of_isIso_app_obj₂₃ d hT h.1 h.2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility at an invertible shift implies compatibility at its inverse. -/
private theorem commShiftCore_neg
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (n : ℤ) (h : NatTrans.CommShiftCore τ n) :
    NatTrans.CommShiftCore τ (-n) := by
  constructor
  ext X
  apply (shiftFunctor D n).map_injective
  have hz : NatTrans.CommShiftCore τ (-n + n) := by
    simpa only [neg_add_cancel] using NatTrans.CommShiftCore.zero (τ := τ) ℤ
  have hs := hz.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Category.assoc] at hs
  rw [← NatTrans.naturality_assoc] at hs
  have hD := (shiftFunctorAdd D (-n) n).inv.naturality (τ.app X)
  dsimp only [Functor.comp_map] at hD
  rw [← hD] at hs
  apply (cancel_epi (F.map ((shiftFunctorAdd C (-n) n).hom.app X) ≫
    (F.commShiftIso n).hom.app (X⟦-n⟧))).mp
  apply (cancel_mono ((shiftFunctorAdd D (-n) n).inv.app (G.obj X))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_obj, Category.assoc, h.shift_app_comm_assoc τ] using hs

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coherence extends the degree-one square to every integral shift. -/
private theorem commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (h : NatTrans.CommShiftCore τ (1 : ℤ)) :
    NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn := commShiftCore_neg τ 1 h
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero (τ := τ) ℤ
  | @succ n ih => exact ih.add h
  | @pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

end General

section ScalarDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct

private theorem all_shift_linear
    (R : Type k) [CommRing R] (C : Type a) [Category.{b} C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [(shiftFunctor C (1 : ℤ)).Linear R] (n : ℤ) :
    (shiftFunctor C n).Linear R := by
  have hn : (shiftFunctor C (-1 : ℤ)).Linear R :=
    by
      have : (shiftEquiv C (1 : ℤ)).functor.Linear R := ‹_›
      exact Equivalence.inverseLinear R (shiftEquiv C (1 : ℤ))
  induction n using Int.induction_on with
  | zero => exact Functor.linear_of_iso R (shiftFunctorZero C ℤ).symm
  | @succ n ih =>
    have := ih
    exact Functor.linear_of_iso R (shiftFunctorAdd C (n : ℤ) 1).symm
  | @pred n ih =>
    have := ih
    exact Functor.linear_of_iso R (shiftFunctorAdd C (-(n : ℤ)) (-1)).symm

private noncomputable def rationalComparison
    (R : Type k) [CommRing R] (C : Type a) [Category.{b} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.induction_on with
    | zero => simp only [Limits.zero_comp, map_zero, Limits.zero_comp]
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp only [Limits.comp_zero, map_zero, Limits.comp_zero]
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [ScalarLocalization.composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem scalarLocalization_isLocalization
    (A : Type k) [CommRing A] (E : Type a) [Category.{b} E]
    [Preadditive E] [Linear A E] [HasZeroObject E] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E] [IsTriangulated E]
    [∀ n : ℤ, (shiftFunctor E n).Linear A] (s : A) :
    (ScalarLocalization.localization A E s).IsLocalization
      (Rationalization.W (Submonoid.powers s) E) := by
  classical
  let M := Submonoid.powers s
  let V := rationalComparison A E s
  have : V.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away s) X.obj Y.obj).surjective⟩
  have : V.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away s) X.obj Y.obj).injective⟩
  have : V.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : V.IsEquivalence := {}
  let Q := ScalarLocalization.localization A E s
  have fac : Q ⋙ V ≅ Rationalization.Q M E :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, V, ScalarLocalization.localization, rationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M E)
    (Rationalization.W M E) Q V.asEquivalence.symm
    (Functor.isoWhiskerRight fac.symm V.inv ≪≫ (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft Q V.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

/-- An exact linear transformation descends through raw scalar localization. -/
private theorem scalarCompatibility_of
    {E : Type a} [Category.{b} E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] [IsTriangulated E]
    (F : E ⥤ E) (d : 𝟭 E ⟶ F) [F.CommShift ℤ]
    [F.IsTriangulated] [NatTrans.CommShift d ℤ]
    (A : Type k) [CommRing A] [Linear A E] [F.Additive] [F.Linear A]
    [(shiftFunctor E (1 : ℤ)).Linear A] (s : A)
    [HasZeroObject (ScalarLocalization A E s)] [HasShift (ScalarLocalization A E s) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization A E s) n).Additive]
    [Pretriangulated (ScalarLocalization A E s)]
    [(ScalarLocalization.localization A E s).CommShift ℤ]
    [(ScalarLocalization.localization A E s).IsTriangulated]
    (htriangles : ∀ T : Triangle (ScalarLocalization A E s),
      T ∈ distTriang _ ↔ ∃ T' : Triangle E, T' ∈ distTriang _ ∧
        Nonempty (T ≅ (ScalarLocalization.localization A E s).mapTriangle.obj T')) :
    ScalarCompatibility F d A s := by
  classical
  have : ∀ n : ℤ, (shiftFunctor E n).Linear A := all_shift_linear A E
  let Q := ScalarLocalization.localization A E s
  let G := ScalarLocalization.map A E s F
  let W := Rationalization.W (Submonoid.powers s) E
  have : Q.IsLocalization W := scalarLocalization_isLocalization A E s
  let e : Q ⋙ G ≅ F ⋙ Q := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp [Q, G, ScalarLocalization.map, ScalarLocalization.mapHom,
      ScalarLocalization.localization]
    simp)
  let : Localization.Lifting Q W (F ⋙ Q) G := ⟨e⟩
  let : G.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ (F ⋙ Q) G
  have he : NatTrans.CommShift e.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q W ℤ (F ⋙ Q) G
  let := he
  let : Localization.Lifting Q W Q (𝟭 _) := ⟨Q.rightUnitor⟩
  let delta : 𝟭 (ScalarLocalization A E s) ⟶ G :=
    Localization.liftNatTrans Q W Q (F ⋙ Q) (𝟭 _) G
      (Q.leftUnitor.inv ≫ Functor.whiskerRight d Q)
  have hd (X : E) : delta.app (Q.obj X) = Q.map (d.app X) := by
    dsimp only [delta]
    rw [Localization.liftNatTrans_app]
    change 𝟙 _ ≫ (𝟙 _ ≫ Q.map (d.app X)) ≫ 𝟙 _ = _
    simp
  have hshift (X : E) (n : ℤ) :
      G.map ((Q.commShiftIso n).hom.app X) ≫
          (G.commShiftIso n).hom.app (Q.obj X) =
        Q.map ((F.commShiftIso n).hom.app X) ≫
          (Q.commShiftIso n).hom.app (F.obj X) := by
    have h := NatTrans.shift_app_comm e.hom n X
    simp only [Functor.commShiftIso_comp_hom_app] at h
    change (G.map _ ≫ _) ≫ (shiftFunctor _ n).map (𝟙 _) = 𝟙 _ ≫ _ at h
    simpa only [Functor.map_id, Category.comp_id, Category.id_comp] using h
  have hdelta : NatTrans.CommShift delta ℤ := by
    have hwhisker : Functor.whiskerLeft Q delta =
        Q.rightUnitor.hom ≫ Q.leftUnitor.inv ≫
          (Functor.whiskerRight d Q) ≫ e.inv := by
      ext X
      change delta.app (Q.obj X) = 𝟙 _ ≫ 𝟙 _ ≫ Q.map (d.app X) ≫ 𝟙 _
      simpa only [Category.id_comp, Category.comp_id] using hd X
    have : NatTrans.CommShift (Functor.whiskerLeft Q delta) ℤ := by
      rw [hwhisker]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft delta Q (fun X ↦ ⟨X.obj, 𝟙 _, by
      dsimp [Q, ScalarLocalization.localization]
      infer_instance⟩)
  let := hdelta
  have hG : G.IsTriangulated := by
    have : (Q ⋙ G).IsTriangulated := (Functor.isTriangulated_iff_of_iso e).mpr inferInstance
    constructor
    intro T hT
    obtain ⟨T', hT', ⟨i⟩⟩ := (htriangles T).mp hT
    exact isomorphic_distinguished _ ((Q ⋙ G).map_distinguished T' hT') _
      (G.mapTriangle.mapIso i ≪≫ (Functor.mapTriangleCompIso Q G).symm.app T')
  let := hG
  refine ⟨inferInstanceAs (G.CommShift ℤ), delta, ?_, hshift, ?_⟩
  · intro X
    exact hd X.obj
  · exact triangleCompatibility_of G delta

end ScalarDescent

section ClosedLinearity
open MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A closed symmetric tensor product is additive on a category with finite biproducts. -/
private theorem coefficientClosed_monoidalPreadditive
    {D : Type a} [Category.{b} D] [Preadditive D]
    [Limits.HasZeroObject D] [Limits.HasBinaryBiproducts D]
    {H : Dᵒᵖ × D ⥤ D} (S : WeilConjectures.CoefficientClosedStructure H)
    (s : @SymmetricCategory D _ S.monoidal) :
    @MonoidalPreadditive D _ _ S.monoidal := by
  let _ := S.monoidal
  let _ := s
  have addR (X : D) : (tensorRight X).Additive := by
    let _ : (tensorRight X).IsLeftAdjoint := (S.adjunction X).isLeftAdjoint
    let _ := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
    exact Functor.additive_of_preservesBinaryBiproducts (tensorRight X)
  let _ : ∀ X : D, (tensorRight X).Additive := addR
  let _ : ∀ X : D, (tensorLeft X).Additive := fun X ↦
    Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight X).symm
  constructor
  · intro X Y Z
    exact (tensorLeft X).map_zero Y Z
  · intro X Y Z
    exact (tensorRight X).map_zero Y Z
  · intro X Y Z f g
    exact (tensorLeft X).map_add
  · intro X Y Z f g
    exact (tensorRight X).map_add

/-- The central tensor-unit action determines linearity of tensoring. -/
private theorem monoidalLinear_of_unitAction
    {D : Type a} [Category.{b} D] [Preadditive D]
    (A : Type k) [CommRing A] [Linear A D]
    [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D]
    (e : A → End (𝟙_ D))
    (h : ∀ (a : A) (X : D),
      a • 𝟙 X = (ρ_ X).inv ≫ X ◁ e a ≫ (ρ_ X).hom) :
    MonoidalLinear A D := by
  have leftLinear (X : D) : (tensorLeft X).Linear A := by
    apply (Functor.linear_iff A (tensorLeft X)).mpr
    intro Y a
    change X ◁ (a • 𝟙 Y) = a • 𝟙 (X ⊗ Y)
    rw [h a Y, h a (X ⊗ Y)]
    simp only [whiskerLeft_comp, whiskerLeft_rightUnitor_inv, whiskerLeft_rightUnitor,
      Category.assoc]
    rw [← associator_naturality_right_assoc]
    simp
  let _ : ∀ X : D, (tensorLeft X).Linear A := leftLinear
  let _ : ∀ X : D, (tensorRight X).Linear A :=
    fun X ↦ Functor.linear_of_iso A (BraidedCategory.tensorLeftIsoTensorRight X)
  constructor
  · intro X Y Z a f
    exact (tensorLeft X).map_smul a f
  · intro a Y Z f X
    exact (tensorRight X).map_smul a f

/-- Contravariant internal Hom is additive and linear when tensor is linear in both variables.
Source: Stacks 0A8X, by transposing natural evaluation. -/
private theorem coefficientClosedDual_linear
    {D : Type a} [Category.{b} D] [Preadditive D]
    (A : Type k) [CommRing A] [Linear A D] {H : Dᵒᵖ × D ⥤ D}
    (S : WeilConjectures.CoefficientClosedStructure H) (O : D)
    (hadd : @MonoidalPreadditive D _ _ S.monoidal)
    (hlin : @MonoidalLinear A _ D _ _ _ S.monoidal hadd) :
    (Prod.sectL Dᵒᵖ O ⋙ H).Additive ∧
      ∀ {X Y : D} (f : X ⟶ Y) (a : A),
        H.map (Prod.mkHom (a • f).op (𝟙 O)) =
          a • H.map (Prod.mkHom f.op (𝟙 O)) := by
  let _ := S.monoidal
  let _ := hadd
  let _ := hlin
  constructor
  · constructor
    intro X Y f g
    apply ((S.adjunction Y.unop).homEquiv (H.obj (X, O)) O).symm.injective
    change ((S.adjunction Y.unop).homEquiv _ _).symm
        (H.map (Prod.mkHom (f + g) (𝟙 O))) =
      ((S.adjunction Y.unop).homEquiv _ _).symm
        (H.map (Prod.mkHom f (𝟙 O)) + H.map (Prod.mkHom g (𝟙 O)))
    simp only [Adjunction.homEquiv_counit, Functor.map_add, Preadditive.add_comp]
    erw [S.evaluation_naturality X.unop Y.unop O (f + g).unop,
      S.evaluation_naturality X.unop Y.unop O f.unop,
      S.evaluation_naturality X.unop Y.unop O g.unop]
    simp
  · intro X Y f a
    apply ((S.adjunction X).homEquiv (H.obj (op Y, O)) O).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]
    erw [S.evaluation_naturality Y X O (a • f),
      S.evaluation_naturality Y X O f]
    simp
end ClosedLinearity

open WeilConjectures MonoidalCategory in
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : Type a} [Category.{b} D] {E : Type c} [Category.{v} E]
  {H : Dᵒᵖ × D ⥤ D} {HU : Eᵒᵖ × E ⥤ E} (F : D ⥤ E)
  (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
  (s : @SymmetricCategory D _ S.monoidal)
  (sU : @SymmetricCategory E _ SU.monoidal)
  (h : H ⋙ F ≅ (F.op.prod F) ⋙ HU)
  (t : S.tensor ⋙ F ≅ (F.prod F) ⋙ SU.tensor)
  (he : ∀ X Y : D, F.map (S.evaluation X Y) =
    t.hom.app (H.obj (op X, Y), X) ≫
      SU.tensor.map (Prod.mkHom (h.hom.app (op X, Y)) (𝟙 _)) ≫
        SU.evaluation (F.obj X) (F.obj Y))

include he in
private theorem transpose_restriction (V X Y : D) (f : S.tensor.obj (V, X) ⟶ Y) :
    SU.transpose (F.obj V) (F.obj X) (F.obj Y)
      (t.inv.app (V, X) ≫ F.map f) =
    F.map (S.transpose V X Y f) ≫ h.hom.app (op X, Y) := by
  let := S.monoidal
  let := SU.monoidal
  let g := S.transpose V X Y f
  have hg : S.tensor.map (g, 𝟙 X) ≫ S.evaluation X Y = f := by
    have hh := (S.transpose V X Y).symm_apply_apply f
    change ((S.adjunction X).homEquiv V Y).symm g = f at hh
    rw [Adjunction.homEquiv_symm_apply] at hh
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      tensor_map, tensorRight, Functor.flip, curriedTensor, tensorHom_id] using hh
  have hn : SU.tensor.map (F.map g, 𝟙 (F.obj X)) ≫
      t.inv.app (H.obj (op X, Y), X) =
      t.inv.app (V, X) ≫ F.map (S.tensor.map (g, 𝟙 X)) := by
    have hh := t.inv.naturality (Prod.mkHom g (𝟙 X))
    simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id] using hh
  apply (SU.transpose _ _ _).symm.injective
  rw [Equiv.symm_apply_apply]
  change t.inv.app (V, X) ≫ F.map f =
    ((SU.adjunction (F.obj X)).homEquiv _ _).symm
      (F.map g ≫ h.hom.app (op X, Y))
  rw [Adjunction.homEquiv_symm_apply]
  change t.inv.app (V, X) ≫ F.map f =
    (F.map g ≫ h.hom.app (op X, Y)) ▷ F.obj X ≫ SU.evaluation (F.obj X) (F.obj Y)
  rw [← tensorHom_id]
  change t.inv.app (V, X) ≫ F.map f =
    SU.tensor.map (Prod.mkHom (F.map g ≫ h.hom.app (op X, Y)) (𝟙 _)) ≫
      SU.evaluation (F.obj X) (F.obj Y)
  have ht : SU.tensor.map (Prod.mkHom (F.map g ≫ h.hom.app (op X, Y)) (𝟙 _)) =
      SU.tensor.map (Prod.mkHom (F.map g) (𝟙 (F.obj X))) ≫
        SU.tensor.map (Prod.mkHom (h.hom.app (op X, Y)) (𝟙 (F.obj X))) := by
    rw [← SU.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [ht, Category.assoc]
  have hh : SU.tensor.map (Prod.mkHom (h.hom.app (op X, Y)) (𝟙 (F.obj X))) ≫
      SU.evaluation (F.obj X) (F.obj Y) =
      t.inv.app (H.obj (op X, Y), X) ≫ F.map (S.evaluation X Y) := by
    rw [he, ← Category.assoc, ← Category.assoc, t.inv_hom_id_app, Category.id_comp]
  rw [hh, ← Category.assoc, hn, Category.assoc, ← F.map_comp, hg]

private theorem transpose_right {V X Y Z : D} (f : S.tensor.obj (V, X) ⟶ Y)
    (g : Y ⟶ Z) :
    S.transpose V X Y f ≫ H.map (Prod.mkHom (𝟙 (op X)) g) =
      S.transpose V X Z (f ≫ g) := by
  exact ((S.adjunction X).homEquiv_naturality_right f g).symm

private theorem bidual_coefficient {O OU : D} (o : O ≅ OU) (X : D) :
    ringedSiteBidual S s O X ≫ H.map
      (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op X)) o.inv)).op o.hom) =
      ringedSiteBidual S s OU X := by
  let := S.monoidal
  let := s
  unfold ringedSiteBidual
  rw [show H.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op X)) o.inv)).op o.hom) =
    H.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op X)) o.inv)).op (𝟙 O)) ≫
      H.map (Prod.mkHom (𝟙 _) o.hom) by
        rw [← H.map_comp]; congr 1; ext <;> simp]
  rw [← Category.assoc, ← ringedSiteTranspose_source, transpose_right]
  congr 1
  dsimp only [CoefficientClosedStructure.tensor]
  simp only [MonoidalCategory.tensor_map, id_tensorHom,
    BraidedCategory.braiding_naturality_right_assoc, Category.assoc]
  have hn := (S.adjunction X).counit.naturality o.inv
  change (H.map (Prod.mkHom (𝟙 (op X)) o.inv) ▷ X) ≫ S.evaluation X O =
    S.evaluation X OU ≫ o.inv at hn
  erw [reassoc_of% hn, Iso.inv_hom_id, Category.comp_id]

include he in
private theorem bidual_restriction_untransported
    (hs : ∀ X Y : D, F.map (s.braiding X Y).hom ≫ t.hom.app (Y, X) =
      t.hom.app (X, Y) ≫ (sU.braiding (F.obj X) (F.obj Y)).hom)
    (O X : D) :
    F.map (ringedSiteBidual S s O X) ≫ h.hom.app (op (H.obj (op X, O)), O) =
    ringedSiteBidual SU sU (F.obj O) (F.obj X) ≫
      HU.map (Prod.mkHom (h.hom.app (op X, O)).op (𝟙 (F.obj O))) := by
  let := S.monoidal
  let := SU.monoidal
  let := sU
  unfold ringedSiteBidual
  rw [← transpose_restriction F S SU h t he]
  rw [← ringedSiteTranspose_source]
  congr 1
  rw [F.map_comp]
  have hb : t.inv.app (X, H.obj (op X, O)) ≫
      F.map (s.braiding X (H.obj (op X, O))).hom =
      (sU.braiding (F.obj X) (F.obj (H.obj (op X, O)))).hom ≫
        t.inv.app (H.obj (op X, O), X) := by
    apply (cancel_mono (t.hom.app (H.obj (op X, O), X))).mp
    simp only [Category.assoc, t.inv_hom_id_app]
    rw [hs, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  rw [← Category.assoc, hb, Category.assoc, he]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  dsimp only [CoefficientClosedStructure.tensor]
  simp only [MonoidalCategory.tensor_map, id_tensorHom]
  erw [tensorHom_id]
  congr 1
  exact (BraidedCategory.braiding_naturality_right (F.obj X)
    (h.hom.app (op X, O))).symm

include he in
private theorem bidual_restriction
    (hs : ∀ X Y : D, F.map (s.braiding X Y).hom ≫ t.hom.app (Y, X) =
      t.hom.app (X, Y) ≫ (sU.braiding (F.obj X) (F.obj Y)).hom)
    {O : D} {OU : E} (o : F.obj O ≅ OU) (X : D) :
    F.map (ringedSiteBidual S s O X) ≫
      h.hom.app (op (H.obj (op X, O)), O) ≫
      HU.map (Prod.mkHom (h.inv.app (op X, O)).op o.hom) ≫
      HU.map (Prod.mkHom (HU.map (Prod.mkHom (𝟙 (op (F.obj X))) o.inv)).op
        (𝟙 OU)) = ringedSiteBidual SU sU OU (F.obj X) := by
  rw [← Category.assoc, ← Category.assoc,
    bidual_restriction_untransported F S SU s sU h t he hs]
  simp only [Category.assoc, ← HU.map_comp]
  have hh :
      Prod.mkHom (h.hom.app (op X, O)).op (𝟙 (F.obj O)) ≫
        (Prod.mkHom (h.inv.app (op X, O)).op o.hom ≫
          Prod.mkHom (HU.map (Prod.mkHom (𝟙 (op (F.obj X))) o.inv)).op (𝟙 OU)) =
      Prod.mkHom (HU.map (Prod.mkHom (𝟙 (op (F.obj X))) o.inv)).op o.hom := by
    ext
    · dsimp
      rw [← Category.assoc, ← op_comp, h.inv_hom_id_app]
      erw [CategoryTheory.op_id, Category.id_comp]
    · simp
  rw [hh]
  exact bidual_coefficient SU sU o (F.obj X)

end

open Pretriangulated.Opposite in
@[instance_reducible] private def dualRightOpCommShift
    {D : Type a} [Category.{b} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : Dᵒᵖ ⥤ D) [T.CommShift ℤ] : T.rightOp.CommShift ℤ :=
  inferInstanceAs (((opOp D) ⋙ T.op).CommShift ℤ)

attribute [local instance] dualRightOpCommShift

open Pretriangulated.Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rightOp_shift_one
    {D : Type a} [Category.{b} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : Dᵒᵖ ⥤ D) [T.CommShift ℤ] (X : D) :
    (T.rightOp.commShiftIso (1 : ℤ)).hom.app X =
      ((T.commShiftIso (-1 : ℤ)).inv.app (op X)).op := by
  change (((opOp D) ⋙ T.op).commShiftIso (1 : ℤ)).hom.app X = _
  rw [Functor.commShiftIso_comp_hom_app,
    commShiftIso_opOp_hom_app X 1 (-1)]
  dsimp only [opOp_obj]
  rw [Functor.op_commShiftIso_hom_app T (op (op X)) 1 (-1) (by decide)]
  simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.op_map]
  erw [Category.comp_id, Quiver.Hom.unop_op, Functor.map_id,
    op_id, Category.id_comp, Category.comp_id]
  exact Category.id_comp _

open Pretriangulated.Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem doubleDualRestriction
    {D : Type a} [Category.{b} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {E : Type c} [Category.{v} E] [Preadditive E] [HasZeroObject E]
    [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (T : Dᵒᵖ ⥤ D) (TU : Eᵒᵖ ⥤ E) (F : D ⥤ E)
    [T.CommShift ℤ] [TU.CommShift ℤ] [F.CommShift ℤ]
    (α : T ⋙ F ≅ F.op ⋙ TU) [NatTrans.CommShift α.hom ℤ] :
    ∃ β : (T.rightOp ⋙ T) ⋙ F ≅ F ⋙ (TU.rightOp ⋙ TU),
      (∀ X : D, β.hom.app X = α.hom.app (op (T.obj (op X))) ≫
        TU.map ((α.inv.app (op X)).op)) ∧ NatTrans.CommShift β.hom ℤ := by
  let α' : T.rightOp ⋙ F.op ≅ F ⋙ TU.rightOp :=
    Functor.isoWhiskerLeft (opOp D) (NatIso.op α).symm
  have : NatTrans.CommShift α'.hom ℤ := by
    apply commShift_of_one
    constructor
    ext X
    dsimp only [α', Functor.isoWhiskerLeft_hom, NatIso.op_inv, Functor.whiskerLeft_app,
      NatTrans.op_app, Iso.symm_hom]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.commShiftIso_comp_hom_app]
    rw [rightOp_shift_one T X, rightOp_shift_one TU (F.obj X)]
    erw [
      Functor.op_commShiftIso_hom_app F (op (T.obj (op X))) 1 (-1) (by decide)]
    simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.op_map]
    simp only [NatIso.op_inv, NatTrans.op_app, opOp_obj,
      Functor.rightOp_map, Quiver.Hom.unop_op]
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    erw [unop_id, Functor.map_id, Category.id_comp, Category.comp_id]
    rw [shiftFunctor_op_map _ 1 (-1)]
    simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, Quiver.Hom.unop_op,
      unop_comp, Category.assoc]
    erw [unop_id, Category.id_comp]
    change (α.inv.app (op X))⟦(-1 : ℤ)⟧' ≫
        (F.commShiftIso (-1 : ℤ)).inv.app (T.obj (op X)) ≫
          F.map ((T.commShiftIso (-1 : ℤ)).inv.app (op X)) =
      (TU.commShiftIso (-1 : ℤ)).inv.app (op (F.obj X)) ≫
        TU.map ((F.commShiftIso (1 : ℤ)).hom.app X).op ≫
          α.inv.app (op (X⟦(1 : ℤ)⟧))
    rw [NatTrans.shift_app α.inv (-1) (op X)]
    simp only [Functor.commShiftIso_comp_hom_app,
      Functor.commShiftIso_comp_inv_app, Category.assoc,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      ]
    rw [Functor.op_commShiftIso_inv_app F (op X) (-1) 1 (by decide)]
    simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, Functor.map_comp, Category.assoc]
    erw [unop_id, F.map_id, op_id, TU.map_id, Category.id_comp, F.map_id,
      Category.comp_id]
    rfl
  let β : (T.rightOp ⋙ T) ⋙ F ≅ F ⋙ (TU.rightOp ⋙ TU) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T.rightOp α ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α' TU ≪≫
        Functor.associator _ _ _
  refine ⟨β, ?_, ?_⟩
  · intro X
    change 𝟙 _ ≫ (α.hom.app (op (T.obj (op X))) ≫
      (𝟙 _ ≫ (TU.map ((α.inv.app (op X)).op) ≫ 𝟙 _))) = _
    simp only [Category.id_comp, Category.comp_id]
  · dsimp [β]
    infer_instance


section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- Coefficient duality is the recorded Hom with target O[0].
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def dual : (D.{c, v, r, w} J R)ᵒᵖ ⥤ D.{c, v, r, w} J R :=
  Prod.sectL _ (ringedSiteDualityUnit.{c, v, r, w} J R) ⋙
    derivedInternalHomOfUniverses.{c, v, r, w} J R

/-- The actual double application of coefficient duality.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def bidual : D.{c, v, r, w} J R ⥤ D.{c, v, r, w} J R :=
  (dual.{c, v, r, w} J R).rightOp ⋙ dual.{c, v, r, w} J R

/-- The evaluation-transpose natural transformation from the dependency, unchanged.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def evaluation (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    𝟭 (D.{c, v, r, w} J R) ⟶ bidual.{c, v, r, w} J R where
  app X := ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R) X
  naturality _ _ f := ringedSiteBidual_naturality M.closed M.symmetric
    (ringedSiteDualityUnit.{c, v, r, w} J R) f

/-- The normalized degree-one comparison, including the leading minus sign of chi.
Source: Stacks 08JC; lem-sf-double-hom-cone-comparison, formula for chi
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def signedShift (X : D.{c, v, r, w} J R) :
    (bidual.{c, v, r, w} J R).obj (X⟦(1 : ℤ)⟧) ⟶ ((bidual.{c, v, r, w} J R).obj X)⟦(1 : ℤ)⟧ :=
  -((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom ((sourceShift.{c, v, r, w} J R X 1).hom.app
          (ringedSiteDualityUnit.{c, v, r, w} J R)).op
        (𝟙 (ringedSiteDualityUnit.{c, v, r, w} J R))) ≫
    (sourceShift.{c, v, r, w} J R ((dual.{c, v, r, w} J R).obj (op X)) (-1)).inv.app
      (ringedSiteDualityUnit.{c, v, r, w} J R))

open Pretriangulated.Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem signed_bidual_normalized
    [(dual.{c, v, r, w} J R).CommShift ℤ]
    (hPlus : ∀ X : D.{c, v, r, w} J R,
      ((dual.{c, v, r, w} J R).commShiftIso (1 : ℤ)).hom.app (op X) =
        -(sourceShift.{c, v, r, w} J R X (-1)).inv.app
          (ringedSiteDualityUnit.{c, v, r, w} J R))
    (hMinus : ∀ X : D.{c, v, r, w} J R,
      ((dual.{c, v, r, w} J R).commShiftIso (-1 : ℤ)).inv.app (op X) =
        (sourceShift.{c, v, r, w} J R X 1).hom.app
          (ringedSiteDualityUnit.{c, v, r, w} J R)) :
    ∀ X : D.{c, v, r, w} J R,
      (((dual.{c, v, r, w} J R).rightOp ⋙ dual.{c, v, r, w} J R).commShiftIso (1 : ℤ)).hom.app X =
        signedShift.{c, v, r, w} J R X := by
  let T := dual.{c, v, r, w} J R
  intro X
  rw [Functor.commShiftIso_comp_hom_app, rightOp_shift_one]
  change T.map (((T.commShiftIso (-1 : ℤ)).inv.app (op X)).op) ≫
    (T.commShiftIso (1 : ℤ)).hom.app (op (T.obj (op X))) = _
  change ∀ X, (T.commShiftIso (-1 : ℤ)).inv.app (op X) = _ at hMinus
  change ∀ X, (T.commShiftIso (1 : ℤ)).hom.app (op X) = _ at hPlus
  rw [hMinus, hPlus]
  simp only [Preadditive.comp_neg]
  rfl

open Pretriangulated.Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exactness and the signed degree-one comparison follow by applying source duality twice. -/
private theorem signed_bidual_exact :
    ∃ S : (bidual.{c, v, r, w} J R).CommShift ℤ,
      (fun [_shiftInst : (bidual.{c, v, r, w} J R).CommShift ℤ] ↦
        (bidual.{c, v, r, w} J R).IsTriangulated ∧
        ∀ X : D.{c, v, r, w} J R,
          ((bidual.{c, v, r, w} J R).commShiftIso (1 : ℤ)).hom.app X =
            signedShift.{c, v, r, w} J R X) (_shiftInst := S) := by
  obtain ⟨S, hExact, hPlus, hMinus⟩ := signedDerivedInternalHom_exact.{c, v, r, w} J R
      (ringedSiteDualityUnit.{c, v, r, w} J R)
  let T := dual.{c, v, r, w} J R
  let : T.CommShift ℤ := S
  have : T.IsTriangulated := hExact
  let : T.rightOp.CommShift ℤ :=
    inferInstanceAs (((opOp (D.{c, v, r, w} J R)) ⋙ T.op).CommShift ℤ)
  have : T.rightOp.IsTriangulated :=
    inferInstanceAs (((opOp (D.{c, v, r, w} J R)) ⋙ T.op).IsTriangulated)
  change ∃ S : (T.rightOp ⋙ T).CommShift ℤ,
    (fun [_shiftInst : (T.rightOp ⋙ T).CommShift ℤ] ↦
      (T.rightOp ⋙ T).IsTriangulated ∧ ∀ X : D.{c, v, r, w} J R,
        ((T.rightOp ⋙ T).commShiftIso (1 : ℤ)).hom.app X =
          signedShift.{c, v, r, w} J R X) (_shiftInst := S)
  refine ⟨inferInstanceAs ((T.rightOp ⋙ T).CommShift ℤ),
    inferInstanceAs ((T.rightOp ⋙ T).IsTriangulated), ?_⟩
  intro X
  change ((T.rightOp ⋙ T).commShiftIso (1 : ℤ)).hom.app X = _
  rw [Functor.commShiftIso_comp_hom_app]
  have hr : (T.rightOp.commShiftIso (1 : ℤ)).hom.app X =
      ((T.commShiftIso (-1 : ℤ)).inv.app (op X)).op := by
    change (((opOp (D.{c, v, r, w} J R)) ⋙ T.op).commShiftIso (1 : ℤ)).hom.app X = _
    rw [Functor.commShiftIso_comp_hom_app,
      commShiftIso_opOp_hom_app X 1 (-1)]
    dsimp only [opOp_obj]
    rw [Functor.op_commShiftIso_hom_app T (op (op X)) 1 (-1) (by decide)]
    simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.op_map]
    erw [Category.comp_id, Quiver.Hom.unop_op, Functor.map_id,
      op_id, Category.id_comp, Category.comp_id]
    exact Category.id_comp _
  rw [hr]
  change T.map (((T.commShiftIso (-1 : ℤ)).inv.app (op X)).op) ≫
    (T.commShiftIso (1 : ℤ)).hom.app (op (T.obj (op X))) = _
  change ∀ X, (T.commShiftIso (-1 : ℤ)).inv.app (op X) = _ at hMinus
  change ∀ X, (T.commShiftIso (1 : ℤ)).hom.app (op X) = _ at hPlus
  rw [hMinus, hPlus]
  simp only [Preadditive.comp_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The bidual map is compatible with the precisely signed exact structure.
Source: Stacks 08JC, 0A97; derived.tex 0144
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: Give the single dual its normalized contravariant exact structure. Its opposite is exact
as well, and composing the two gives a coherent exact structure on bidual. Expanding the
composition comparison in degree one gives exactly signedShift: the minus is the degree-one
normalization of the outer dual. The separate evaluation-transpose calculation gives the shift-one
square. Zero and addition coherence imply the inverse-shift square, and integer induction gives
all shifts. Naturality then supplies the three triangle squares, including the connecting square.
Triangle two-out-of-three and shift faithfulness give all asserted isomorphism-locus properties.
No general reflexivity assumption is used. Slice and scalar descent are stated separately below. -/
theorem compatibility (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    ∃ S : (bidual.{c, v, r, w} J R).CommShift ℤ,
      (∀ X : D.{c, v, r, w} J R,
        (@Functor.commShiftIso _ _ _ _ (bidual.{c, v, r, w} J R) ℤ _ _ _ S 1).hom.app X =
          signedShift.{c, v, r, w} J R X) ∧
      (fun [_shiftInst : (bidual.{c, v, r, w} J R).CommShift ℤ] ↦
        TriangleCompatibility (bidual.{c, v, r, w} J R) (evaluation.{c, v, r, w} J R M))
        (_shiftInst := S) := by
  obtain ⟨S, hExact, hNormalized⟩ := signed_bidual_exact.{c, v, r, w} J R
  let : (bidual.{c, v, r, w} J R).CommShift ℤ := S
  have : (bidual.{c, v, r, w} J R).IsTriangulated := hExact
  have hN (X : D.{c, v, r, w} J R) :
      ((bidual.{c, v, r, w} J R).commShiftIso (1 : ℤ)).hom.app X =
        signedShift.{c, v, r, w} J R X := hNormalized X
  have hd : NatTrans.CommShiftCore (evaluation.{c, v, r, w} J R M) (1 : ℤ) := by
    constructor
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, hN]
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
    exact (coefficientBidualEvaluation_shift_one.{c, v, r, w} J R M X).symm
  have : NatTrans.CommShift (evaluation.{c, v, r, w} J R M) ℤ :=
    commShift_of_one (evaluation.{c, v, r, w} J R M) hd
  exact ⟨S, hN, triangleCompatibility_of _ _⟩

section Slice
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w'} (Modules.{max c v, v, r} (J.over U) (R.over U))]

/-- The existing exact slice restriction, applied to the unbounded derived category.
Source: Stacks 03DJ, 08JB
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def restriction : D.{c, v, r, w} J R ⥤ D.{max c v, v, r, w'} (J.over U) (R.over U) :=
  letI : (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionLimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionColimits.{c, v, r} R U
  Functor.mapDerivedCategory.{w, w'}
    (C₁ := Modules.{c, v, r} J R)
    (C₂ := Modules.{max c v, v, r} (J.over U) (R.over U))
    (SheafOfModules.localizedSystemRestriction.{c, v, r} R U)

/-- The inherited shift comparison of exact slice restriction.
Source: Stacks 03DJ, 08JB
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
instance restrictionCommShift : (restriction.{c, v, r, w, w'} J R U).CommShift ℤ :=
  letI : (SheafOfModules.localizedSystemRestriction.{c, v, r} R U).Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionLimits.{c, v, r} R U
  letI := SheafOfModules.localizedSystemRestrictionColimits.{c, v, r} R U
  inferInstanceAs ((Functor.mapDerivedCategory.{w, w'}
    (C₁ := Modules.{c, v, r} J R)
    (C₂ := Modules.{max c v, v, r} (J.over U) (R.over U))
    (SheafOfModules.localizedSystemRestriction.{c, v, r} R U)).CommShift ℤ)

/-- The double-Hom comparison formed from the restriction comparison and coefficient unit.
Source: Stacks 08JB, 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def restrictionBidualIso
    (h : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙ restriction.{c, v, r, w, w'} J R U ≅
      ((restriction.{c, v, r, w, w'} J R U).op.prod
        (restriction.{c, v, r, w, w'} J R U)) ⋙
          derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
    (o : (restriction.{c, v, r, w, w'} J R U).obj (ringedSiteDualityUnit.{c, v, r, w} J R) ≅
      ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U))
    (X : D.{c, v, r, w} J R) :
    (restriction.{c, v, r, w, w'} J R U).obj ((bidual.{c, v, r, w} J R).obj X) ≅
      (bidual.{max c v, v, r, w'} (J.over U) (R.over U)).obj
        ((restriction.{c, v, r, w, w'} J R U).obj X) :=
  h.app (op ((dual.{c, v, r, w} J R).obj (op X)),
      ringedSiteDualityUnit.{c, v, r, w} J R) ≪≫
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).mapIso
      (((h.app (op X, ringedSiteDualityUnit.{c, v, r, w} J R)).symm.op).prod o) ≪≫
    (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).mapIso
      (((derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).mapIso
        ((Iso.refl (op ((restriction.{c, v, r, w, w'} J R U).obj X))).prod o.symm)).op.prod
          (Iso.refl _))

set_option maxHeartbeats 600000 in
-- The two-site comparison carries independent derived and Hom universe parameters.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Pretriangulated.Opposite in
/-- Exact slice restriction transports the signed bidual triangle morphism. The comparisons are
formed from the evaluation-compatible tensor/Hom restriction comparisons, by the same double-Hom
formula as the dependency's restriction theorem.
Source: Stacks 08JB, 0A97, 08JC
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: (9) On V to U, both restricted Hom complexes consist of the same families of module maps
on C/V, with differential d_I f-(-1)^n f d_E. Products are sectionwise.The exact j_! adjunction
shows j*I is K-injective, so these componentwise identities compute the derived restriction
comparisons. (10) Reindexing and the signs in s, and the leading minus in chi, restrict
unchanged. Change of K-injective target commutes with evaluation and those signs, so this
calculation is independent of the chosen resolutions. The dependency's evaluation-transpose
restriction square is exactly the equation for beta below. Naturality and the shift equation for
beta transport all three triangle squares; the last displayed equation records the connecting
square explicitly. Restriction is exact because termwise restriction preserves kernels and
cokernels and commutes with cones and shifts. -/
theorem slice_compatibility
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U))
    [(bidual.{c, v, r, w} J R).CommShift ℤ]
    [(bidual.{max c v, v, r, w'} (J.over U) (R.over U)).CommShift ℤ]
    (hS : ∀ X : D.{c, v, r, w} J R,
      ((bidual.{c, v, r, w} J R).commShiftIso (1 : ℤ)).hom.app X =
        signedShift.{c, v, r, w} J R X)
    (hSU : ∀ X : D.{max c v, v, r, w'} (J.over U) (R.over U),
      ((bidual.{max c v, v, r, w'} (J.over U) (R.over U)).commShiftIso (1 : ℤ)).hom.app X =
        signedShift.{max c v, v, r, w'} (J.over U) (R.over U) X) :
    ∃ (h : derivedInternalHomOfUniverses.{c, v, r, w} J R ⋙
          restriction.{c, v, r, w, w'} J R U ≅
        ((restriction.{c, v, r, w, w'} J R U).op.prod
          (restriction.{c, v, r, w, w'} J R U)) ⋙
            derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U))
      (o : (restriction.{c, v, r, w, w'} J R U).obj (ringedSiteDualityUnit.{c, v, r, w} J R) ≅
        ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U))
      (t : M.closed.tensor ⋙ restriction.{c, v, r, w, w'} J R U ≅
        ((restriction.{c, v, r, w, w'} J R U).prod
          (restriction.{c, v, r, w, w'} J R U)) ⋙ MU.closed.tensor),
      (∀ X Y : D.{c, v, r, w} J R,
        (restriction.{c, v, r, w, w'} J R U).map (M.closed.evaluation X Y) =
          t.hom.app ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op X, Y), X) ≫
            MU.closed.tensor.map (Prod.mkHom (h.hom.app (op X, Y)) (𝟙 _)) ≫
              MU.closed.evaluation ((restriction.{c, v, r, w, w'} J R U).obj X)
                ((restriction.{c, v, r, w, w'} J R U).obj Y)) ∧
      ∃ beta : bidual.{c, v, r, w} J R ⋙ restriction.{c, v, r, w, w'} J R U ≅
          restriction.{c, v, r, w, w'} J R U ⋙
            bidual.{max c v, v, r, w'} (J.over U) (R.over U),
        (∀ X : D.{c, v, r, w} J R, beta.app X =
          restrictionBidualIso.{c, v, r, w, w'} J R U h o X) ∧
        NatTrans.CommShift beta.hom ℤ ∧
        (∀ X : D.{c, v, r, w} J R,
          (restriction.{c, v, r, w, w'} J R U).map ((evaluation.{c, v, r, w} J R M).app X) ≫
            beta.hom.app X =
              (evaluation.{max c v, v, r, w'} (J.over U) (R.over U) MU).app
                ((restriction.{c, v, r, w, w'} J R U).obj X)) ∧
        (∀ T : Triangle (D.{c, v, r, w} J R), T ∈ distTriang _ →
          (restriction.{c, v, r, w, w'} J R U).map
              ((evaluation.{c, v, r, w} J R M).app T.obj₃ ≫
                (bidual.{c, v, r, w} J R).map T.mor₃ ≫
                  signedShift.{c, v, r, w} J R T.obj₁) ≫
            ((restriction.{c, v, r, w, w'} J R U).commShiftIso (1 : ℤ)).hom.app
              ((bidual.{c, v, r, w} J R).obj T.obj₁) ≫ (beta.hom.app T.obj₁)⟦(1 : ℤ)⟧' =
          (evaluation.{max c v, v, r, w'} (J.over U) (R.over U) MU).app
              ((restriction.{c, v, r, w, w'} J R U).obj T.obj₃) ≫
            (bidual.{max c v, v, r, w'} (J.over U) (R.over U)).map
              (((restriction.{c, v, r, w, w'} J R U).mapTriangle.obj T).mor₃) ≫
            signedShift.{max c v, v, r, w'} (J.over U) (R.over U)
              ((restriction.{c, v, r, w, w'} J R U).obj T.obj₁)) := by
  let T := dual.{c, v, r, w} J R
  let TU := dual.{max c v, v, r, w'} (J.over U) (R.over U)
  let F := restriction.{c, v, r, w, w'} J R U
  obtain ⟨S, _, hPlus, hMinus⟩ := signedDerivedInternalHom_exact.{c, v, r, w} J R
    (ringedSiteDualityUnit.{c, v, r, w} J R)
  obtain ⟨SU, _, hPlusU, hMinusU⟩ :=
    signedDerivedInternalHom_exact.{max c v, v, r, w'} (J.over U) (R.over U)
      (ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U) (R.over U))
  let : T.CommShift ℤ := S
  let : TU.CommShift ℤ := SU
  obtain ⟨h, o, t, he, hs, hr⟩ :=
    ringedSiteSignedDual_restriction.{c, v, r, w, w'} J R U M MU
  let α : T ⋙ F ≅ F.op ⋙ TU := closedDualRestrictionIso h o
  have hd := bidual_restriction F M.closed MU.closed M.symmetric MU.symmetric h t he hs o
  have ha : NatTrans.CommShift α.hom ℤ := by
    apply commShift_of_one
    constructor
    ext X
    obtain ⟨X⟩ := X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [Functor.commShiftIso_comp_hom_app T F,
      Functor.commShiftIso_comp_hom_app F.op TU]
    erw [hPlus X, hPlusU (F.obj X)]
    erw [Functor.op_commShiftIso_hom_app F (op X) 1 (-1) (by decide)]
    simp only [shiftFunctorOpIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app]
    erw [unop_id, Functor.map_id, op_id, Category.id_comp, Category.comp_id]
    have : F.Additive := by dsimp only [F, restriction]; infer_instance
    simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
      Category.assoc, neg_inj]
    change F.map ((sourceShift J R X (-1)).inv.app (ringedSiteDualityUnit J R)) ≫
        (F.commShiftIso (1 : ℤ)).hom.app (T.obj (op X)) ≫
          (α.hom.app (op X))⟦(1 : ℤ)⟧' =
      α.hom.app (op (X⟦(-1 : ℤ)⟧)) ≫
        TU.map (((F.commShiftIso (-1 : ℤ)).inv.app X).op) ≫
          (sourceShift (J.over U) (R.over U) (F.obj X) (-1)).inv.app
            (ringedSiteDualityUnit (J.over U) (R.over U))
    have hh := hr X (-1)
    change F.map ((sourceShift J R X (-1)).hom.app (ringedSiteDualityUnit J R)) ≫
        α.hom.app (op (X⟦(-1 : ℤ)⟧)) =
      (F.commShiftIso (1 : ℤ)).hom.app (T.obj (op X)) ≫
        (α.hom.app (op X))⟦(1 : ℤ)⟧' ≫
        (sourceShift (J.over U) (R.over U) (F.obj X) (-1)).hom.app
          (ringedSiteDualityUnit (J.over U) (R.over U)) ≫
        TU.map (((F.commShiftIso (-1 : ℤ)).hom.app X).op) at hh
    apply (cancel_epi (F.map ((sourceShift J R X (-1)).hom.app
      (ringedSiteDualityUnit J R)))).mp
    simp only [← Category.assoc, ← F.map_comp, Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp]
    rw [hh]
    simp only [Category.assoc, ← TU.map_comp, ← op_comp, Iso.inv_hom_id_app,
      op_id]
    erw [TU.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  let : NatTrans.CommShift α.hom ℤ := ha
  obtain ⟨β, hβ, hβcomm⟩ := doubleDualRestriction T TU F α
  have hn := signed_bidual_normalized.{c, v, r, w} J R hPlus hMinus
  have hnU := signed_bidual_normalized.{max c v, v, r, w'}
    (J.over U) (R.over U) hPlusU hMinusU
  let beta : bidual.{c, v, r, w} J R ⋙ F ≅
      F ⋙ bidual.{max c v, v, r, w'} (J.over U) (R.over U) := β
  have hβshift (X : D.{c, v, r, w} J R) :
      F.map (signedShift.{c, v, r, w} J R X) ≫
          (F.commShiftIso (1 : ℤ)).hom.app ((bidual.{c, v, r, w} J R).obj X) ≫
          (beta.hom.app X)⟦(1 : ℤ)⟧' =
        beta.hom.app (X⟦(1 : ℤ)⟧) ≫
          (bidual.{max c v, v, r, w'} (J.over U) (R.over U)).map
            ((F.commShiftIso (1 : ℤ)).hom.app X) ≫
          signedShift.{max c v, v, r, w'} (J.over U) (R.over U) (F.obj X) := by
    let := hβcomm
    have hh := NatTrans.shift_app_comm β.hom (1 : ℤ) X
    rw [Functor.commShiftIso_comp_hom_app (T.rightOp ⋙ T) F,
      Functor.commShiftIso_comp_hom_app F (TU.rightOp ⋙ TU), hn X, hnU (F.obj X)] at hh
    simpa only [T, TU, bidual, beta, Category.assoc] using hh
  have hβiso (X : D.{c, v, r, w} J R) : beta.app X =
      restrictionBidualIso.{c, v, r, w, w'} J R U h o X := by
    apply Iso.ext
    change β.hom.app X = _
    rw [hβ]
    simp only [α, closedDualRestrictionIso, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.prod_hom, Iso.prod_inv, Iso.refl_hom, Iso.refl_inv,
      restrictionBidualIso]
    dsimp only [TU, dual, Functor.comp_map, Prod.sectL_map]
    simp only [op_comp, Functor.map_comp, Iso.symm_hom, Iso.op_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Category.assoc]
    simp only [← Functor.map_comp]
    congr 2
    ext <;> simp
    rfl
  have hβcompatible : NatTrans.CommShift beta.hom ℤ := by
    apply commShift_of_one
    constructor
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [Functor.commShiftIso_comp_hom_app (bidual.{c, v, r, w} J R) F,
      Functor.commShiftIso_comp_hom_app F
        (bidual.{max c v, v, r, w'} (J.over U) (R.over U)), hS, hSU]
    simpa only [Category.assoc] using hβshift X
  have hdeval (X : D.{c, v, r, w} J R) :
      F.map ((evaluation.{c, v, r, w} J R M).app X) ≫ beta.hom.app X =
        (evaluation.{max c v, v, r, w'} (J.over U) (R.over U) MU).app (F.obj X) := by
    change F.map _ ≫ (beta.app X).hom = _
    rw [hβiso]
    dsimp only [evaluation, restrictionBidualIso, dual, bidual, F, restriction,
      Functor.comp_obj, Prod.sectL, Functor.rightOp_obj]
    simpa only [restrictionBidualIso, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
      Iso.op_hom, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, evaluation,
      Iso.app_hom, Iso.app_inv, F, restriction, dual, bidual, Functor.comp_obj,
      Prod.sectL_obj, Functor.id_obj, Functor.rightOp_obj, Category.assoc] using hd X
  refine ⟨h, o, t, he, beta, hβiso, hβcompatible, hdeval, ?_⟩
  intro V _
  let B := bidual.{c, v, r, w} J R
  let BU := bidual.{max c v, v, r, w'} (J.over U) (R.over U)
  change F.map ((evaluation J R M).app V.obj₃ ≫ B.map V.mor₃ ≫
      signedShift J R V.obj₁) ≫
      (F.commShiftIso (1 : ℤ)).hom.app (B.obj V.obj₁) ≫
      (beta.hom.app V.obj₁)⟦(1 : ℤ)⟧' =
    (evaluation (J.over U) (R.over U) MU).app (F.obj V.obj₃) ≫
      BU.map (F.map V.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app V.obj₁) ≫
        signedShift (J.over U) (R.over U) (F.obj V.obj₁)
  simp only [Functor.map_comp, Category.assoc]
  erw [hβshift V.obj₁]
  have hnat := beta.hom.naturality V.mor₃
  change F.map (B.map V.mor₃) ≫ beta.hom.app _ = beta.hom.app _ ≫ BU.map (F.map V.mor₃) at hnat
  rw [reassoc_of% hnat, ← Category.assoc, hdeval]
end Slice

/-- The induced action of a coefficient endomorphism, through the tensor unit.Endomorphisms of O[0]
are global coefficient sections, so a ring map into this endomorphism ring is the central
coefficient action in the statement.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def coefficientScalar (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (e : End (ringedSiteDualityUnit.{c, v, r, w} J R)) (X : D.{c, v, r, w} J R) : X ⟶ X :=
  (M.closed.monoidal.rightUnitor X).inv ≫
    M.closed.tensor.map (Prod.mkHom (𝟙 X) (M.unitIso.hom ≫ e ≫ M.unitIso.inv)) ≫
      (M.closed.monoidal.rightUnitor X).hom

section Subcategory
variable (P : ObjectProperty (D.{c, v, r, w} J R))
  (hdual : ∀ X : D.{c, v, r, w} J R, P X → P ((dual.{c, v, r, w} J R).obj (op X)))

/-- Restriction of the actual double dual to a full dual-stable subcategory.
Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 3
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def subcategoryBidual : P.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.ι ⋙ bidual.{c, v, r, w} J R)
    (fun X ↦ hdual _ (hdual X.obj X.property))

/-- The same evaluation map, viewed in the full subcategory.
Source: Stacks 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility). -/
def subcategoryEvaluation (M : RingedSiteDualityModel.{c, v, r, w} J R) :
    𝟭 P.FullSubcategory ⟶ subcategoryBidual.{c, v, r, w} J R P hdual where
  app X := ObjectProperty.homMk ((evaluation.{c, v, r, w} J R M).app X.obj)
  naturality _ _ f := ObjectProperty.hom_ext _
    ((evaluation.{c, v, r, w} J R M).naturality f.hom)

/-- The ambient coefficient bidual is additive and linear under a central scalar action.
Source: Stacks 0A8X and 0A97.
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: on Hom complexes, precomposition is additive and commutes with the central scalar
action by transposing evaluation; tensor additivity follows from adjunction, and tensor
linearity from the central unit action. Apply this calculation twice. -/
private theorem ambient_bidual_linearity (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (A : Type k) [CommRing A] [Linear A (D.{c, v, r, w} J R)]
    (rho : A →+* End (ringedSiteDualityUnit.{c, v, r, w} J R))
    (hcentral : ∀ (a : A) (X : D.{c, v, r, w} J R),
      a • 𝟙 X = coefficientScalar.{c, v, r, w} J R M (rho a) X) :
    ∃ add : (bidual.{c, v, r, w} J R).Additive,
      (fun [_addInst : (bidual.{c, v, r, w} J R).Additive] ↦
        (bidual.{c, v, r, w} J R).Linear A) (_addInst := add) := by
  let _ := M.closed.monoidal
  let _ := M.symmetric
  let _ : MonoidalPreadditive (D.{c, v, r, w} J R) :=
    coefficientClosed_monoidalPreadditive M.closed M.symmetric
  let _ : MonoidalLinear A (D.{c, v, r, w} J R) :=
    monoidalLinear_of_unitAction A
      (fun a ↦ M.unitIso.hom ≫ rho a ≫ M.unitIso.inv) (by
        intro a X
        simpa only [coefficientScalar,
          WeilConjectures.CoefficientClosedStructure.tensor,
          MonoidalCategory.tensor_map, MonoidalCategory.id_tensorHom] using hcentral a X)
  obtain ⟨hadd, hsmul⟩ := coefficientClosedDual_linear A M.closed
    (ringedSiteDualityUnit.{c, v, r, w} J R) inferInstance inferInstance
  let _ : (dual.{c, v, r, w} J R).Additive := hadd
  refine ⟨inferInstanceAs ((dual.{c, v, r, w} J R).rightOp ⋙
    dual.{c, v, r, w} J R).Additive, ?_⟩
  constructor
  intro X Y f a
  change (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (a • f).op (𝟙 _))).op (𝟙 _)) = _
  rw [hsmul, hsmul]
  rfl

set_option linter.unusedVariables false in
/-- Central coefficient scalars make the actual restricted double dual linear.
Source: Stacks 0A8X, 0A97
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: Step 11 of the node. Precomposition on Hom complexes is additive and commutes with the
central coefficient action. Apply this twice. The identities descend to homotopy classes and to
quasi-isomorphism fractions; sums are computed using common denominators. Restrict to the full
dual-stable subcategory, whose Hom modules and scalar action are inherited from the ambient
category. -/
theorem subcategory_linearity (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (A : Type k) [CommRing A] [Linear A (D.{c, v, r, w} J R)]
    (rho : A →+* End (ringedSiteDualityUnit.{c, v, r, w} J R))
    (hcentral : ∀ (a : A) (X : D.{c, v, r, w} J R),
      a • 𝟙 X = coefficientScalar.{c, v, r, w} J R M (rho a) X) :
    ∃ add : (subcategoryBidual.{c, v, r, w} J R P hdual).Additive,
      (fun [addInst : (subcategoryBidual.{c, v, r, w} J R P hdual).Additive] ↦
        (subcategoryBidual.{c, v, r, w} J R P hdual).Linear A) (addInst := add) := by
  obtain ⟨ambientAdd, ambientLinear⟩ := ambient_bidual_linearity
    (J := J) (R := R) M A rho hcentral
  let _ : (bidual.{c, v, r, w} J R).Additive := ambientAdd
  let _ : (bidual.{c, v, r, w} J R).Linear A := ambientLinear
  let subAdd : (subcategoryBidual.{c, v, r, w} J R P hdual).Additive := by
    constructor
    intro X Y f g
    apply P.hom_ext
    exact Functor.Additive.map_add (F := bidual.{c, v, r, w} J R)
  refine ⟨subAdd, ?_⟩
  let _ : (subcategoryBidual.{c, v, r, w} J R P hdual).Additive := subAdd
  constructor
  intro X Y f a
  apply P.hom_ext
  exact Functor.Linear.map_smul (F := bidual.{c, v, r, w} J R) f.hom a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Descent through the raw scalar localization with precisely its induced shift and image
distinguished triangles. The structural parameters describe the triangulation supplied by
exists_triangulated_scalarLocalization, rather than additional assumptions on the site or on
objects. Linearity is supplied by subcategory_linearity.
Source: Stacks 08JC, 0A97; blueprint lem-coef-rational-retract-evaluation, paragraph 3
(blueprint: lem-coef-rational-bidual-triangle-compatibility).
Proof: Restrict the exact signed structure of compatibility to the full subcategory. Step 12
extends its functor by f tensor a ↦ F(f) tensor a, its evaluation by tensoring with 1, and its
shift comparison by tensoring with 1 and using Q's shift comparison. Balancing follows from
subcategory_linearity. Naturality holds on pure tensors and then on sums. Every localized
distinguished triangle is isomorphic to an image triangle, by the scalar-localization
triangulated lemma. Thus exactness and all three squares descend, including the connecting
square for triangles with fractional arrows. Step 13 applies triangle two-out-of-three to id and
the descended exact functor. The invertibility locus is shift-closed by compatibility and its
inverse. The inclusion equation below pins the original signed comparison, and the Q equation
pins its scalar extension at every integer shift. No individual bidual map is assumed
invertible, and no idempotent completion is taken. -/
theorem scalar_compatibility (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (A : Type k) [CommRing A] [Linear A (D.{c, v, r, w} J R)]
    [P.IsTriangulated] [(shiftFunctor P.FullSubcategory (1 : ℤ)).Linear A] (s : A)
    [(subcategoryBidual.{c, v, r, w} J R P hdual).Additive]
    [(subcategoryBidual.{c, v, r, w} J R P hdual).Linear A]
    [HasZeroObject (ScalarLocalization A P.FullSubcategory s)]
    [HasShift (ScalarLocalization A P.FullSubcategory s) ℤ]
    [∀ n : ℤ, (shiftFunctor (ScalarLocalization A P.FullSubcategory s) n).Additive]
    [(ScalarLocalization.localization A P.FullSubcategory s).CommShift ℤ]
    [Pretriangulated (ScalarLocalization A P.FullSubcategory s)]
    [IsTriangulated (ScalarLocalization A P.FullSubcategory s)]
    [(ScalarLocalization.localization A P.FullSubcategory s).IsTriangulated]
    (hshift : shiftFunctor (ScalarLocalization A P.FullSubcategory s) (1 : ℤ) =
      ScalarLocalization.map A P.FullSubcategory s (shiftFunctor P.FullSubcategory (1 : ℤ)))
    (hQ : ∀ X : P.FullSubcategory,
      HEq (((ScalarLocalization.localization A P.FullSubcategory s).commShiftIso (1 : ℤ)).hom.app X)
        (𝟙 ((ScalarLocalization.localization A P.FullSubcategory s).obj (X⟦(1 : ℤ)⟧))))
    (htriangles : ∀ T : Triangle (ScalarLocalization A P.FullSubcategory s),
      T ∈ distTriang _ ↔ ∃ T' : Triangle P.FullSubcategory,
        T' ∈ distTriang _ ∧
          Nonempty (T ≅
            (ScalarLocalization.localization A P.FullSubcategory s).mapTriangle.obj T')) :
    ∃ subShift : (subcategoryBidual.{c, v, r, w} J R P hdual).CommShift ℤ,
      (fun [subShiftInst : (subcategoryBidual.{c, v, r, w} J R P hdual).CommShift ℤ] ↦
        (∀ X : P.FullSubcategory,
          P.ι.map (((subcategoryBidual.{c, v, r, w} J R P hdual).commShiftIso (1 : ℤ)).hom.app X) ≫
            (P.ι.commShiftIso (1 : ℤ)).hom.app
              ((subcategoryBidual.{c, v, r, w} J R P hdual).obj X) =
            (bidual.{c, v, r, w} J R).map ((P.ι.commShiftIso (1 : ℤ)).hom.app X) ≫
              signedShift.{c, v, r, w} J R X.obj) ∧
        TriangleCompatibility (subcategoryBidual.{c, v, r, w} J R P hdual)
          (subcategoryEvaluation.{c, v, r, w} J R P hdual M) ∧
        ScalarCompatibility (subcategoryBidual.{c, v, r, w} J R P hdual)
          (subcategoryEvaluation.{c, v, r, w} J R P hdual M) A s)
        (subShiftInst := subShift) := by
  obtain ⟨ambientShift, hnormalized, hcompatible⟩ := compatibility.{c, v, r, w} J R M
  let : (bidual.{c, v, r, w} J R).CommShift ℤ := ambientShift
  have : (bidual.{c, v, r, w} J R).IsTriangulated := hcompatible.1
  have : NatTrans.CommShift (evaluation.{c, v, r, w} J R M) ℤ := hcompatible.2.1
  let G := subcategoryBidual.{c, v, r, w} J R P hdual
  let d := subcategoryEvaluation.{c, v, r, w} J R P hdual M
  let hG := fun X : P.FullSubcategory ↦ hdual _ (hdual X.obj X.property)
  let e : G ⋙ P.ι ≅ P.ι ⋙ bidual.{c, v, r, w} J R :=
    P.liftCompιIso (P.ι ⋙ bidual.{c, v, r, w} J R) hG
  let subShift : G.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  have hd : Functor.whiskerRight d P.ι =
      P.ι.leftUnitor.hom ≫ P.ι.rightUnitor.inv ≫
        Functor.whiskerLeft P.ι (evaluation.{c, v, r, w} J R M) ≫
        e.inv := by
    ext X
    change (evaluation.{c, v, r, w} J R M).app X.obj =
      𝟙 _ ≫ 𝟙 _ ≫ (evaluation.{c, v, r, w} J R M).app X.obj ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift d ℤ := by
    have : NatTrans.CommShift (Functor.whiskerRight d P.ι) ℤ := by
      rw [hd]
      infer_instance
    exact NatTrans.CommShift.of_whiskerRight d P.ι
  have : G.IsTriangulated := (Functor.isTriangulated_iff_comp_right e).mpr inferInstance
  refine ⟨subShift, ?_, triangleCompatibility_of G d, ?_⟩
  · intro X
    have h := NatTrans.shift_app_comm e.hom (1 : ℤ) X
    simp only [Functor.commShiftIso_comp_hom_app] at h
    change (P.ι.map _ ≫ _) ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
      𝟙 _ ≫ _ ≫ _ at h
    simp only [Functor.map_id, Category.comp_id, Category.id_comp, hnormalized] at h
    convert h using 1 <;> rfl
  · exact scalarCompatibility_of G d A s htriangles


end Subcategory
end Site
end CategoryTheory.CoefficientBidual
