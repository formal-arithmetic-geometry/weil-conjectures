/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModelData
import WeilConjectures.CategoryTheory.Constant.ConstantModuleKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Adjunction.Unique

/-! Derived comparison for the terminal scalar realization.

The proof chooses K-flat resolutions, compares the fixed change-of-rings model on
those resolutions with the sheafified scalar-extension model, and descends the
comparison through the derived localization using the universal left-derived
property. Naturality in the resolutions gives the displayed natural isomorphism.
(blueprint: lem-zl-contractible-realization-underived-model-derived-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

/-- Any additive left adjoint to terminal sections with the specified preservation
properties has total left derivative isomorphic to the fixed realization.

Source: Hemo--Richarz--Scholbach, Section 3, Remark 3.2; Stacks Project, Tags 06YY
and 06XN.
(blueprint: lem-zl-contractible-realization-underived-model-derived-comparison).

Proof: let L₀ be constant module realization followed by the ordinary extension E
in the fixed extensionModel and inverse section reconstruction. Tensor adjunction
and sheafification identify maps from L₀(M) to N with A-linear maps M → N(U).
Uniqueness of left adjoints therefore gives L ≅ L₀, naturally in M; no compatibility
of a chosen braided structure with this isomorphism is required. Resolve each
A-complex by a flat-term K-flat complex P. Exact constant realization takes P to a
flat-term K-flat complex over constant A. The canonical extension-model counit is
invertible on this complex. Exact section reconstruction commutes with localization,
so this counit identifies F(Q(P)) with Q(L₀(P)), and the ordinary isomorphism with
Q(L(P)). The comparisons respect maps of resolutions. The universal left-derived
property, or equivalently the resolving-class localization theorem, now gives the
natural isomorphism on all derived objects. No exactness of terminal sections is
used. Zero rings and degenerate topologies are covered by the same universal
properties. -/
theorem contractible_realization_derived_comparison
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U)
    (L : ModuleCat.{u + 1} (A J O U) ⥤ Mod (Sheaf J Ab.{u + 1}) O)
    [L.Additive] [L.PreservesKFlatQuasiIso]
    (hadj : Nonempty (L ⊣ sections J O U)) :
    Nonempty (L.leftDerivedFunctor ≅ F J O U hU) := by
  classical
  -- Identify the fixed ordinary extension with the left adjoint in the statement.
  let c := commutativeSiteConstantModuleFunctor J (A J O U)
  let m := extensionModel J O U hU
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let : e.inverse.Additive := Functor.additive_of_preserves_binary_products e.inverse
  let E := SheafOfModules.flatScalarExtension J (scalarMap J O U hU)
  let t : m.E ≅ E := NatIso.ofComponents (fun M ↦ eqToIso (m.obj_eq M)) (by
    intro M N f
    dsimp [E]
    rw [m.map_eq]
    simp
    rfl)
  let R := c ⋙ m.E ⋙ e.inverse
  let : R.Additive := inferInstance
  let r : R ≅ terminalScalarRealization J O U hU :=
    Functor.isoWhiskerLeft c (Functor.isoWhiskerRight t e.inverse) ≪≫
      (Functor.associator c E e.inverse).symm
  obtain ⟨_, _, ⟨a⟩⟩ := contractible_realization_underived_data J O U hU
  let i : R ≅ L := r ≪≫ a.leftAdjointUniq hadj.some
  let qc := DerivedCategory.Q (C := ModuleCat.{u + 1} (A J O U))
  let qs := DerivedCategory.Q (C := realizationModules J (A J O U))
  let qt := DerivedCategory.Q (C := Mod (Sheaf J Ab.{u + 1}) O)
  let cc := c.mapHomologicalComplex (.up ℤ)
  let ec := m.E.mapHomologicalComplex (.up ℤ)
  let ic := e.inverse.mapHomologicalComplex (.up ℤ)
  let rc := R.mapHomologicalComplex (.up ℤ)
  let lc := L.mapHomologicalComplex (.up ℤ)
  let j : cc ⋙ ec ⋙ ic ≅ rc :=
    Functor.mapHomologicalComplexCompIso (Iso.refl R) (.up ℤ)
  let k : rc ≅ lc := NatIso.mapHomologicalComplex i (.up ℤ)
  -- Assemble the comparison on complexes from the fixed extension-model counit.
  let b : qc ⋙ F J O U hU ⟶ lc ⋙ qt :=
    (Functor.associator qc c.mapDerivedCategory
      (m.T ⋙ e.inverse.mapDerivedCategory)).inv ≫
    Functor.whiskerRight c.mapDerivedCategoryFactors.hom
      (m.T ⋙ e.inverse.mapDerivedCategory) ≫
    (Functor.associator cc qs (m.T ⋙ e.inverse.mapDerivedCategory)).hom ≫
    Functor.whiskerLeft cc ((Functor.associator qs m.T e.inverse.mapDerivedCategory).inv ≫
      Functor.whiskerRight m.ε e.inverse.mapDerivedCategory ≫
      (Functor.associator ec _ e.inverse.mapDerivedCategory).hom ≫
      Functor.whiskerLeft ec e.inverse.mapDerivedCategoryFactors.hom) ≫
    (Functor.associator cc ec (ic ⋙ qt)).inv ≫
    (Functor.associator (cc ⋙ ec) ic qt).inv ≫
    Functor.whiskerRight j.hom qt ≫ Functor.whiskerRight k.hom qt
  -- Descend through the full homotopy quotient and use the universal derived lift.
  let q := HomotopyCategory.quotient (ModuleCat.{u + 1} (A J O U)) (.up ℤ)
  let qh := DerivedCategory.Qh (C := ModuleCat.{u + 1} (A J O U))
  let lh := L.mapHomotopyCategory (.up ℤ)
  let qth := DerivedCategory.Qh (C := Mod (Sheaf J Ab.{u + 1}) O)
  let iq : q ⋙ qh ≅ qc := DerivedCategory.quotientCompQhIso _
  let jq : q ⋙ (lh ⋙ qth) ≅ lc ⋙ qt :=
    (Functor.associator q lh qth).symm ≪≫
      Functor.isoWhiskerRight (L.mapHomotopyCategoryFactors (.up ℤ)) qth ≪≫
      Functor.associator lc _ qth ≪≫
      Functor.isoWhiskerLeft lc (DerivedCategory.quotientCompQhIso _)
  let bq : q ⋙ (qh ⋙ F J O U hU) ⟶ q ⋙ (lh ⋙ qth) :=
    (Functor.associator q qh (F J O U hU)).inv ≫
      (Functor.isoWhiskerRight iq (F J O U hU)).hom ≫ b ≫ jq.inv
  let w := (Functor.whiskeringLeft
    (CochainComplex (ModuleCat.{u + 1} (A J O U)) ℤ)
    (HomotopyCategory (ModuleCat.{u + 1} (A J O U)) (.up ℤ))
    (DerivedCategory (Mod (Sheaf J Ab.{u + 1}) O))).obj q
  let bh : qh ⋙ F J O U hU ⟶ lh ⋙ qth := w.preimage bq
  have hbh : Functor.whiskerLeft q bh = bq := w.map_preimage bq
  let z : F J O U hU ⟶ L.leftDerivedFunctor :=
    L.leftDerivedFunctor.leftDerivedLift L.leftDerivedFunctorCounit
      (HomotopyCategory.quasiIso _ (.up ℤ)) (F J O U hU) bh
  -- Flat-term K-flat resolutions compute both sides of the comparison.
  have hz (P : CochainComplex (ModuleCat.{u + 1} (A J O U)) ℤ)
      (hp : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
      (hf : ∀ n, ObjectProperty.flat (P.X n)) : IsIso (z.app (qh.obj (q.obj P))) := by
    have hcp := isKFlat_constantModule J (A J O U) P hp
      (fun n ↦ (ModuleCat.flat_iff_flat _).mp (hf n))
    have hm := m.computes (cc.obj P) hcp
    have hb : IsIso (b.app P) := by
      dsimp only [b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    have hbq : IsIso (bq.app P) := by
      dsimp only [bq, NatTrans.comp_app]
      infer_instance
    have hbhP : IsIso (bh.app (q.obj P)) := by
      rw [show bh.app (q.obj P) = bq.app P from congr_app hbh P]
      exact hbq
    have hL := L.isIso_leftDerivedFunctorCounit_app_of_kFlat P hp
    have hzfac := L.leftDerivedFunctor.leftDerived_fac_app L.leftDerivedFunctorCounit
      (HomotopyCategory.quasiIso _ (.up ℤ)) (F J O U hU) bh (q.obj P)
    change z.app (qh.obj (q.obj P)) ≫ L.leftDerivedFunctorCounit.app (q.obj P) =
      bh.app (q.obj P) at hzfac
    exact (isIso_comp_right_iff _ (L.leftDerivedFunctorCounit.app (q.obj P))).mp
      (hzfac ▸ hbhP)
  have hzall (K : DerivedCategory (ModuleCat.{u + 1} (A J O U))) : IsIso (z.app K) := by
    let P := qc.objPreimage K
    obtain ⟨P', f, hf, hflat, hp⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
    let : QuasiIso f := hf
    let d : qh.obj (q.obj P') ≅ K :=
      iq.app P' ≪≫ asIso (qc.map f) ≪≫ qc.objObjPreimageIso K
    exact (NatTrans.isIso_app_iff_of_iso z d).mp (hz P' hp hflat)
  let : IsIso z := NatIso.isIso_of_isIso_app z
  exact ⟨(asIso z).symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
