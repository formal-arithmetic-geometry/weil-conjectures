module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomology
public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import Sheaf.Paper.HypercoverCohomologyModule

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.HypercoverCohomology` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# Blueprint statements

thm-weil-pbc-hypercover-cohomology.

The module-coefficient comparison for `ULift ℤ` supplies the abelian comparison via the
coefficient and sheaf equivalences. The cocone, its refinement compatibility, and its
universal property are transported explicitly. Homotopy invariance is proved directly
from Mathlib's simplicial prism homotopy.
-/

@[expose] public section

universe u₁ u v w z t t' ux uc vc ud vd

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicTopology
open AlgebraicGeometry.FiniteSplitEtaleHypercover
open scoped Simplicial

namespace AlgebraicGeometry.HypercoverCohomologyProof

private abbrev ModuleCoeff := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
private abbrev AbCoeff := AddCommGrpCat.{u + 1}
private abbrev coeffForget : ModuleCoeff.{u} ⥤ AbCoeff.{u} := forget₂ _ _

/- Contravariant sections turn the simplicial prism homotopy into a cochain homotopy. -/
section Homotopy
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Abelian A]
variable {U V : SimplicialObject C} {f g : U ⟶ V}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionComplexIso (S : SimplicialObject C) (F : Cᵒᵖ ⥤ A) :
    (HomologicalComplex.unopFunctor A (.down ℕ)).obj
      (op ((alternatingFaceMapComplex Aᵒᵖ).obj (S ⋙ F.rightOp))) ≅
      (alternatingCofaceMapComplex A).obj (S.rightOp ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    change 𝟙 _ ≫ _ = (((alternatingFaceMapComplex Aᵒᵖ).obj
      (S ⋙ F.rightOp)).d (i + 1) i).unop ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, alternatingFaceMapComplex_obj_d]
    change (AlternatingCofaceMapComplex.obj (S.rightOp ⋙ F)).d i (i + 1) = _
    unfold AlternatingCofaceMapComplex.obj
    dsimp only [CochainComplex.of]
    rw [CochainComplex.of_d]
    change (∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.map (S.map (SimplexCategory.δ k).op).op) =
      (∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) •
        (F.map (S.map (SimplexCategory.δ k).op).op).op).unop
    simp only [unop_sum, unop_zsmul, Quiver.Hom.unop_op])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionHomotopy (H : SimplicialObject.Homotopy f g) (F : Cᵒᵖ ⥤ A) :
    Homotopy ((alternatingCofaceMapComplex A).map (whiskerRight f.rightOp F))
      ((alternatingCofaceMapComplex A).map (whiskerRight g.rightOp F)) := by
  let h := (H.whiskerRight F.rightOp).toChainHomotopy.unop
  let h' := (h.compLeft (sectionComplexIso V F).inv).compRight
    (sectionComplexIso U F).hom
  have hf : (sectionComplexIso V F).inv ≫
      (HomologicalComplex.unopFunctor A (.down ℕ)).map
        ((alternatingFaceMapComplex Aᵒᵖ).map (whiskerRight f F.rightOp)).op ≫
      (sectionComplexIso U F).hom =
      (alternatingCofaceMapComplex A).map (whiskerRight f.rightOp F) := by
    ext n
    change 𝟙 _ ≫ F.map (f.app (op ⦋n⦌)).op ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
    rfl
  have hg : (sectionComplexIso V F).inv ≫
      (HomologicalComplex.unopFunctor A (.down ℕ)).map
        ((alternatingFaceMapComplex Aᵒᵖ).map (whiskerRight g F.rightOp)).op ≫
      (sectionComplexIso U F).hom =
      (alternatingCofaceMapComplex A).map (whiskerRight g.rightOp F) := by
    ext n
    change 𝟙 _ ≫ F.map (g.app (op ⦋n⦌)).op ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
    rfl
  rw [← hf, ← hg]
  refine { hom := h'.hom, zero := h'.zero, comm := ?_ }
  intro i
  have hh := h'.comm i
  dsimp only [dNext, prevD, AddMonoidHom.mk'_apply] at hh ⊢
  have hn : (ComplexShape.down ℕ).symm.next i = (ComplexShape.up ℕ).next i := rfl
  have hp : (ComplexShape.down ℕ).symm.prev i = (ComplexShape.up ℕ).prev i := rfl
  rw [hn, hp] at hh
  simpa only [HomologicalComplex.comp_f, Category.assoc, SimplicialObject.whiskering,
    Functor.whiskeringRight_obj_map] using hh

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
private theorem refinementHomotopy_eq (q : ℕ) (U V : FiniteSplitEtaleHypercover X)
    (f g : U.Refinement V) (h : isRefinementHomotopic f g) :
    cohomologyRefinement A f q = cohomologyRefinement A g q := by
  induction h with
  | rel f g h =>
      obtain ⟨H⟩ := h
      ext F
      exact (sectionHomotopy H F.obj).homologyMap_eq q
  | refl f => rfl
  | symm f g h ih => exact ih.symm
  | trans f g k h h' ih ih' => exact ih.trans ih'

end Homotopy

/- Pointwise cocone universal properties transport through a coefficient equivalence. -/
section Transport
variable {A : Type u} [Category.{v} A] {B : Type w} [Category.{z} B]
  {I : Type t} (R : I → I → Type t') (K : I → A)
  (r : ∀ {i j}, R i j → (K j ⟶ K i)) (H : A) (c : ∀ i, K i ⟶ H)
  (E : A ⥤ B) [E.Full] [E.Faithful] [E.EssSurj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem transportUP
    (hc : ∀ (T : A) (d : ∀ i, K i ⟶ T),
      (∀ i j (f : R i j), r f ≫ d i = d j) →
      ∃! e : H ⟶ T, ∀ i, c i ≫ e = d i)
    (T : B) (d : ∀ i, E.obj (K i) ⟶ T)
    (hd : ∀ i j (f : R i j), E.map (r f) ≫ d i = d j) :
    ∃! e : E.obj H ⟶ T, ∀ i, E.map (c i) ≫ e = d i := by
  let T' := E.objPreimage T
  let eT := E.objObjPreimageIso T
  let d' i : K i ⟶ T' := E.preimage (d i ≫ eT.inv)
  have hd' : ∀ i j (f : R i j), r f ≫ d' i = d' j := by
    intro i j f
    apply E.map_injective
    simp only [Functor.map_comp, d', Functor.map_preimage, ← Category.assoc, hd]
  obtain ⟨e, he, hu⟩ := hc T' d' hd'
  refine ⟨E.map e ≫ eT.hom, ?_, ?_⟩
  · intro i
    rw [← Category.assoc, ← E.map_comp, he]
    dsimp only [d']
    rw [E.map_preimage]
    simp
  · intro g hg
    have hpre : ∀ i, c i ≫ E.preimage (g ≫ eT.inv) = d' i := by
      intro i
      apply E.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, d', ← Category.assoc, hg]
    have h := congrArg E.map (hu (E.preimage (g ≫ eT.inv)) hpre)
    rw [E.map_preimage] at h
    rw [← h]
    simp

section Functorial
variable {C : Type uc} [Category.{vc} C] {D : Type ud} [Category.{vd} D]
variable (S : D ⥤ C) (F : I → C ⥤ A) (G : I → D ⥤ B)
  (a : ∀ {i j}, R i j → (F j ⟶ F i))
  (b : ∀ {i j}, R i j → (G j ⟶ G i))
  (HC : C ⥤ A) (HD : D ⥤ B)
  (eF : ∀ i, (S ⋙ F i) ⋙ E ≅ G i) (eH : (S ⋙ HC) ⋙ E ≅ HD)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include eH in
private theorem transferCocone
    (ha : ∀ i j (f : R i j) (P : D),
      E.map ((a f).app (S.obj P)) ≫ (eF i).hom.app P =
        (eF j).hom.app P ≫ (b f).app P)
    (hC : ∃ c : ∀ i, F i ⟶ HC,
      (∀ i j (f : R i j), a f ≫ c i = c j) ∧
      ∀ (P : C) (T : A) (d : ∀ i, (F i).obj P ⟶ T),
        (∀ i j (f : R i j), (a f).app P ≫ d i = d j) →
        ∃! e : HC.obj P ⟶ T, ∀ i, (c i).app P ≫ e = d i) :
    ∃ c : ∀ i, G i ⟶ HD,
      (∀ i j (f : R i j), b f ≫ c i = c j) ∧
      ∀ (P : D) (T : B) (d : ∀ i, (G i).obj P ⟶ T),
        (∀ i j (f : R i j), (b f).app P ≫ d i = d j) →
        ∃! e : HD.obj P ⟶ T, ∀ i, (c i).app P ≫ e = d i := by
  obtain ⟨c, hc, hu⟩ := hC
  let c' i : G i ⟶ HD := (eF i).inv ≫
    Functor.whiskerRight (Functor.whiskerLeft S (c i)) E ≫ eH.hom
  have hc' (i) (P : D) : (eF i).hom.app P ≫ (c' i).app P =
      E.map ((c i).app (S.obj P)) ≫ eH.hom.app P := by
    dsimp [c']
    simp only [Iso.hom_inv_id_app_assoc]
  refine ⟨c', ?_, ?_⟩
  · intro i j f
    ext P
    apply (cancel_epi ((eF j).hom.app P)).1
    simp only [NatTrans.comp_app]
    rw [← Category.assoc, ← ha, Category.assoc, hc', hc', ← Category.assoc,
      ← E.map_comp, ← NatTrans.comp_app, hc]
  · intro P T d hd
    let d' i := (eF i).hom.app P ≫ d i
    have hd' : ∀ i j (f : R i j), E.map ((a f).app (S.obj P)) ≫ d' i = d' j := by
      intro i j f
      dsimp [d']
      rw [← Category.assoc, ha, Category.assoc, hd]
    obtain ⟨e, he, heuniq⟩ := transportUP R (fun i ↦ (F i).obj (S.obj P))
      (fun f ↦ (a f).app (S.obj P)) (HC.obj (S.obj P))
      (fun i ↦ (c i).app (S.obj P)) E (hu (S.obj P)) T d' hd'
    refine ⟨eH.inv.app P ≫ e, ?_, ?_⟩
    · intro i
      apply (cancel_epi ((eF i).hom.app P)).1
      rw [← Category.assoc, hc', Category.assoc, Iso.hom_inv_id_app_assoc, he]
    · intro e' he'
      have h : eH.hom.app P ≫ e' = e := by
        apply heuniq
        intro i
        rw [← Category.assoc, ← hc', Category.assoc, he']
      rw [← h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
end Functorial

section Inverse
variable {C : Type uc} [Category.{vc} C] {D : Type ud} [Category.{vd} D]
  (S : C ⥤ D) [S.IsEquivalence] (F : C ⥤ A) (G : D ⥤ B)
  (E : A ⥤ B) (e : F ⋙ E ≅ S ⋙ G)
private noncomputable def inverseComparison : (S.inv ⋙ F) ⋙ E ≅ G :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft S.inv e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight S.asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem inverseComparison_hom_app (P : D) :
    (inverseComparison S F G E e).hom.app P =
      e.hom.app (S.inv.obj P) ≫ G.map (S.asEquivalence.counitIso.hom.app P) := by
  simp only [inverseComparison, Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  change e.hom.app _ ≫ (G.map _ ≫ 𝟙 _) = _
  rw [Category.comp_id]
end Inverse

end Transport

/- Additive change of coefficients commutes with alternating cochains and their homology. -/
section Cochains
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type w} [Category.{z} B] [Abelian B] (E : A ⥤ B) [E.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def alternatingCofaceCompIso :
    alternatingCofaceMapComplex A ⋙ E.mapHomologicalComplex (.up ℕ) ≅
      (whiskeringRight SimplexCategory A B).obj E ⋙ alternatingCofaceMapComplex B :=
  NatIso.ofComponents
    (fun F ↦ HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      dsimp only [Functor.comp_obj]
      change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      change ((alternatingCofaceMapComplex B).obj (F ⋙ E)).d i (i + 1) =
        E.map (((alternatingCofaceMapComplex A).obj F).d i (i + 1))
      dsimp only [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
        CochainComplex.of]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
      rfl)) (by
      intro F G f
      ext n
      change E.map (f.app _) ≫ 𝟙 _ = 𝟙 _ ≫ E.map (f.app _)
      simp)

variable {X : Scheme.{ux}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [X.smallEtaleTopology.HasSheafCompose E]

private noncomputable def sectionComplex (U : FiniteSplitEtaleHypercover X) :
    Sheaf X.smallEtaleTopology A ⥤ CochainComplex A ℕ :=
  sheafToPresheaf X.smallEtaleTopology A ⋙
    (whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).obj U.simplicial.rightOp ⋙
    alternatingCofaceMapComplex A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionComplexCompIso (U : FiniteSplitEtaleHypercover X) :
    sectionComplex (A := A) U ⋙ E.mapHomologicalComplex (.up ℕ) ≅
      sheafCompose X.smallEtaleTopology E ⋙ sectionComplex (A := B) U :=
  NatIso.ofComponents
    (fun F ↦ (alternatingCofaceCompIso E).app (U.simplicial.rightOp ⋙ F.obj)) (by
      intro F G f
      ext n
      change E.map (f.hom.app _) ≫ 𝟙 _ = 𝟙 _ ≫ E.map (f.hom.app _)
      simp)

variable [E.PreservesHomology]
private noncomputable def sectionCohomologyCompIso (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    cohomologyFunctor A U q ⋙ E ≅
      sheafCompose X.smallEtaleTopology E ⋙ cohomologyFunctor B U q := by
  change (sectionComplex (A := A) U ⋙ HomologicalComplex.homologyFunctor A (.up ℕ) q) ⋙ E ≅
    sheafCompose X.smallEtaleTopology E ⋙
      (sectionComplex (A := B) U ⋙ HomologicalComplex.homologyFunctor B (.up ℕ) q)
  exact Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (E.mapHomologicalComplexHomologyIso (.up ℕ) q).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sectionComplexCompIso E U) _ ≪≫ Functor.associator _ _ _

private noncomputable def sectionComplexRefinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V) : sectionComplex (A := A) V ⟶ sectionComplex (A := A) U :=
  whiskerRight
    (whiskerLeft (sheafToPresheaf X.smallEtaleTopology A)
      ((whiskeringLeft SimplexCategory X.Etaleᵒᵖ A).map f.rightOp))
    (alternatingCofaceMapComplex A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [E.PreservesHomology] in
private theorem sectionComplexCompIso_refinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V) (F : Sheaf X.smallEtaleTopology A) :
    (E.mapHomologicalComplex (.up ℕ)).map ((sectionComplexRefinement f).app F) ≫
        (sectionComplexCompIso E U).hom.app F =
      (sectionComplexCompIso E V).hom.app F ≫
        (sectionComplexRefinement f).app ((sheafCompose X.smallEtaleTopology E).obj F) := by
  ext n
  change E.map (F.obj.map (f.app _).op) ≫ 𝟙 _ =
    𝟙 _ ≫ E.map (F.obj.map (f.app _).op)
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem sectionCohomologyCompIso_refinement {U V : FiniteSplitEtaleHypercover X}
    (f : U.Refinement V) (q : ℕ) (F : Sheaf X.smallEtaleTopology A) :
    E.map ((cohomologyRefinement A f q).app F) ≫
        (sectionCohomologyCompIso E U q).hom.app F =
      (sectionCohomologyCompIso E V q).hom.app F ≫
        (cohomologyRefinement B f q).app ((sheafCompose X.smallEtaleTopology E).obj F) := by
  let HA := HomologicalComplex.homologyFunctor A (.up ℕ) q
  let HB := HomologicalComplex.homologyFunctor B (.up ℕ) q
  let t := E.mapHomologicalComplexHomologyIso (.up ℕ) q
  simp only [sectionCohomologyCompIso, id_eq, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app, isoWhiskerRight_hom,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  change E.map (HA.map ((sectionComplexRefinement f).app F)) ≫
      (𝟙 _ ≫ t.inv.app _ ≫ HB.map ((sectionComplexCompIso E U).hom.app F)) =
    (𝟙 _ ≫ t.inv.app _ ≫ HB.map ((sectionComplexCompIso E V).hom.app F)) ≫
      HB.map ((sectionComplexRefinement f).app _)
  simp only [Category.id_comp]
  have ht : E.map (HA.map ((sectionComplexRefinement f).app F)) ≫ t.inv.app _ =
      t.inv.app _ ≫ HB.map ((E.mapHomologicalComplex (.up ℕ)).map
        ((sectionComplexRefinement f).app F)) :=
    t.inv.naturality ((sectionComplexRefinement f).app F)
  rw [← Category.assoc, ht, Category.assoc, Category.assoc,
    ← HB.map_comp, sectionComplexCompIso_refinement E, HB.map_comp]

end Cochains

private abbrev coeffSheafForget (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology coeffForget.{u}

/- Exact coefficient equivalences commute with global sections and right derivation. -/
section Derived
private theorem coeffFiniteColimits : Limits.PreservesFiniteColimits coeffForget.{u} := by
  let : Limits.PreservesColimitsOfSize.{0, 0} coeffForget.{u} :=
    Adjunction.isEquivalence_preservesColimits _
  exact Limits.PreservesColimitsOfSize0.preservesFiniteColimits _

private noncomputable def gammaForgetIso (X : Scheme.{u}) :
    Sheaf.Γ X.smallEtaleTopology ModuleCoeff.{u} ⋙ coeffForget.{u} ≅
      (coeffSheafForget X) ⋙ Sheaf.Γ X.smallEtaleTopology AbCoeff.{u} :=
  isoWhiskerRight (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal) coeffForget.{u} ≪≫
    Iso.refl _ ≪≫
    isoWhiskerLeft (coeffSheafForget X) (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm

private noncomputable def cohomologyForgetIso (X : Scheme.{u}) (q : ℤ) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology ModuleCoeff.{u}) 0 ⋙
      Etale.cohomology ModuleCoeff.{u} X q) ⋙ coeffForget.{u} ≅
    (coeffSheafForget X) ⋙
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AbCoeff.{u}) 0 ⋙
        Etale.cohomology AbCoeff.{u} X q) := by
  letI := coeffFiniteColimits.{u}
  let GM := Sheaf.Γ X.smallEtaleTopology ModuleCoeff.{u}
  let GB := Sheaf.Γ X.smallEtaleTopology AbCoeff.{u}
  let sM := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology ModuleCoeff.{u}) 0
  let sB := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AbCoeff.{u}) 0
  let HM := DerivedCategory.homologyFunctor ModuleCoeff.{u} q
  let HB := DerivedCategory.homologyFunctor AbCoeff.{u} q
  change (sM ⋙ (GM.rightDerivedFunctor ⋙ HM)) ⋙ coeffForget.{u} ≅
    (coeffSheafForget X) ⋙ (sB ⋙ (GB.rightDerivedFunctor ⋙ HB))
  calc
    _ ≅ sM ⋙ (GM.rightDerivedFunctor ⋙ (HM ⋙ coeffForget.{u})) :=
      (Functor.associator _ _ _) ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _)
    _ ≅ sM ⋙ (GM.rightDerivedFunctor ⋙ ((coeffForget.{u}).mapDerivedCategory ⋙ HB)) :=
      isoWhiskerLeft _ (isoWhiskerLeft _ ((coeffForget.{u}).mapDerivedCategoryHomologyFunctorIso q))
    _ ≅ sM ⋙ ((GM.rightDerivedFunctor ⋙ (coeffForget.{u}).mapDerivedCategory) ⋙ HB) :=
      isoWhiskerLeft _ (Functor.associator _ _ _).symm
    _ ≅ sM ⋙ ((GM ⋙ coeffForget.{u}).rightDerivedFunctor ⋙ HB) :=
      isoWhiskerLeft _ (isoWhiskerRight
        (rightDerivedFunctorCompMapDerivedCategoryIso GM coeffForget.{u}).symm _)
    _ ≅ sM ⋙ (((coeffSheafForget X) ⋙ GB).rightDerivedFunctor ⋙ HB) :=
      isoWhiskerLeft _ (isoWhiskerRight (rightDerivedFunctorNatIso (gammaForgetIso X)) _)
    _ ≅ sM ⋙ (((coeffSheafForget X).rightDerivedFunctor ⋙ GB.rightDerivedFunctor) ⋙ HB) :=
      isoWhiskerLeft _ (isoWhiskerRight (rightDerivedFunctorCompIso (coeffSheafForget X) GB) _)
    _ ≅ (sM ⋙ (coeffSheafForget X).rightDerivedFunctor) ⋙ (GB.rightDerivedFunctor ⋙ HB) :=
      isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ (Functor.associator _ _ _).symm
    _ ≅ ((coeffSheafForget X) ⋙ sB) ⋙ (GB.rightDerivedFunctor ⋙ HB) :=
      isoWhiskerRight (coeffSheafForget X).singleFunctorCompRightDerivedFunctorIso _
    _ ≅ _ := Functor.associator _ _ _

end Derived

end AlgebraicGeometry.HypercoverCohomologyProof

namespace AlgebraicGeometry

end AlgebraicGeometry
