/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.WfTensorUnitSquareData
import all Sheaf.Paper.FiniteFreeConstructibleScalarTransport
import all Sheaf.Paper.AdicCoefficientDatumCompleted
import all Sheaf.Paper.WeilTensorProduct

/-! # Normalized pullback of completed constant modules

Source: the coefficient-normalization step of the Frobenius tensor-unit argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.WfTensorUnitSquare
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A) (e : Aut X)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory

attribute [local irreducible] pbcCompletedComparison completedCoefficientMap
attribute [local irreducible] HasDerivedCategory.standard

attribute [local instance 40000] AlgebraicGeometry.Scheme.adicDatumModulesAbelian
attribute [local instance 30000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 20000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev direct := proEtaleRingModuleDirectImage e.hom (ring X d) (ring X d)
  (coefficientIso X d e)

private theorem conjugate_adjunct {B : Type*} [Category B]
    (F G : B ⥤ B) (adj : F ⊣ G) {R S : B} (c : R ≅ S)
    (m : F.obj S ⟶ S) :
    (adj.unit.app R ≫ G.map ((F.map c.hom ≫ m) ≫ c.inv)) ≫ G.map c.hom =
      c.hom ≫ (adj.unit.app S ≫ G.map m) := by
  rw [Category.assoc, ← G.map_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, G.map_comp, ← Category.assoc, adj.unit_naturality c.hom,
    Category.assoc]

private theorem directRing_comparison :
    proEtaleRingDirectImageMap e.hom (ring X d) (ring X d) (coefficientIso X d e) ≫
        (proEtaleSheafDirectImage e.hom CommRingCat.{u + 1}).map
          (pbcCompletedComparison X d).hom =
      (pbcCompletedComparison X d).hom ≫ completedCoefficientDirectImageMap e.hom d := by
  exact conjugate_adjunct _ _ (proEtaleSheafAdjunction e.hom CommRingCat.{u + 1})
    (pbcCompletedComparison X d) (completedCoefficientMap e.hom d)

private theorem scalar_conjugate {B : Type*} [Category B] (G : B ⥤ B)
    {R S T : B} (c : R ≅ S) (φ : T ⟶ R) (r : R ⟶ G.obj R)
    (t : T ⟶ G.obj T) (v : S ⟶ G.obj S)
    (hc : r ≫ G.map c.hom = c.hom ≫ v)
    (h : (φ ≫ c.hom) ≫ v = t ≫ G.map (φ ≫ c.hom)) :
    φ ≫ r = t ≫ G.map φ := by
  apply (cancel_mono (G.map c.hom)).mp
  calc
    (φ ≫ r) ≫ G.map c.hom = (φ ≫ c.hom) ≫ v := by
      simpa only [Category.assoc] using congrArg (fun f ↦ φ ≫ f) hc
    _ = _ := h
    _ = _ := by simp only [G.map_comp, Category.assoc]

private theorem scalar_direct :
    adicDatumScalar X (intrinsicPresentationDatum d) ≫
        proEtaleRingDirectImageMap e.hom (ring X d) (ring X d) (coefficientIso X d e) =
      proEtaleConstantDirectImageMap e.hom CommRingCat.{u + 1} (CommRingCat.of A) ≫
        (proEtaleSheafDirectImage e.hom CommRingCat.{u + 1}).map
          (adicDatumScalar X (intrinsicPresentationDatum d)) := by
  exact scalar_conjugate (proEtaleSheafDirectImage e.hom CommRingCat.{u + 1})
    (pbcCompletedComparison X d) (adicDatumScalar X (intrinsicPresentationDatum d))
    _ _ _ (directRing_comparison X d e) (wfCompletedScalar_directImage X d e)

private theorem scalar_section (U : X.ProEtᵒᵖ) (a : A) :
    (proEtaleRingDirectImageMap e.hom (ring X d) (ring X d) (coefficientIso X d e)).hom.app U
        ((adicDatumScalar X (intrinsicPresentationDatum d)).hom.app U
          ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app U a)) =
      (adicDatumScalar X (intrinsicPresentationDatum d)).hom.app
        ((proEtaleBaseChange e.hom).op.obj U)
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app
            ((proEtaleBaseChange e.hom).op.obj U) a) := by
  have h := congrArg (fun f ↦ f.hom.app U
    ((toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app U a))
    (scalar_direct X d e)
  have hc := ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
    ((proEtaleSheafDirectImage e.hom CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of A)))).apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange e.hom).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
  have hcU := congrArg (fun f ↦ f.app U a) hc
  change (proEtaleConstantDirectImageMap e.hom CommRingCat.{u + 1}
    (CommRingCat.of A)).hom.app U _ = _ at hcU
  change _ = (adicDatumScalar X (intrinsicPresentationDatum d)).hom.app
        ((proEtaleBaseChange e.hom).op.obj U) _ at h
  exact h.trans (congrArg
    ((adicDatumScalar X (intrinsicPresentationDatum d)).hom.app
        ((proEtaleBaseChange e.hom).op.obj U)) hcU)

private abbrev global (T : X.ProEt) :=
  SheafOfModules.restrictScalars
    ((adicLisseForget X).map (adicDatumScalar X (intrinsicPresentationDatum d))) ⋙
    constantGlobal X A T

private def constantAdjunction (T : X.ProEt) (hT : IsTerminal T) :
    constants X d ⊣ global X d T :=
  (constantAdj X A T hT).comp
    (adicDatumOrdinaryAdjunction X (adicDatumScalar X (intrinsicPresentationDatum d)))

private theorem constantAdjunction_unit (T : X.ProEt) (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} A) (x : M) :
    ((constantAdjunction X d T hT).unit.app M) x = generator X d M (op T) x := by
  change ((adicDatumOrdinaryAdjunction X
    (adicDatumScalar X (intrinsicPresentationDatum d))).unit.app
    ((adicLisseConstantModules X A).obj M)).val.app (op T)
      (completedConstantGenerator X A M (op T) x) = _
  erw [(adicDatumOrdinaryAdjunction_exists X
    (adicDatumScalar X (intrinsicPresentationDatum d))).choose_spec]
  exact (adicDatumOrdinaryUnit_exists X (adicDatumScalar X (intrinsicPresentationDatum d))
    ((adicLisseConstantModules X A).obj M)).exists.choose_spec (op T) _

private def globalDirectIso (T : X.ProEt) :
    direct X d e ⋙ global X d T ≅
      global X d ((proEtaleBaseChange e.hom).obj T) :=
  NatIso.ofComponents (fun M ↦
    { hom := ModuleCat.ofHom
        (X := (direct X d e ⋙ global X d T).obj M)
        (Y := (global X d ((proEtaleBaseChange e.hom).obj T)).obj M)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            let x' : M.val.obj (op ((proEtaleBaseChange e.hom).obj T)) := x
            change (show (ring X d).obj.obj
              (op ((proEtaleBaseChange e.hom).obj T)) from
              (proEtaleRingDirectImageMap e.hom (ring X d) (ring X d)
                (coefficientIso X d e)).hom.app (op T)
              ((adicDatumScalar X (intrinsicPresentationDatum d)).hom.app (op T)
                ((toSheafify (ProEt.topology X)
                ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app (op T) a))) • x' = _
            rw [scalar_section]
            rfl }
      inv := ModuleCat.ofHom
        (X := (global X d ((proEtaleBaseChange e.hom).obj T)).obj M)
        (Y := (direct X d e ⋙ global X d T).obj M)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            let x' : M.val.obj (op ((proEtaleBaseChange e.hom).obj T)) := x
            change _ = (show (ring X d).obj.obj
              (op ((proEtaleBaseChange e.hom).obj T)) from
              (proEtaleRingDirectImageMap e.hom (ring X d) (ring X d)
                (coefficientIso X d e)).hom.app (op T)
              ((adicDatumScalar X (intrinsicPresentationDatum d)).hom.app (op T)
                ((toSheafify (ProEt.topology X)
                ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app (op T) a))) • x'
            rw [scalar_section]
            rfl }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }) (by intros; ext x; rfl)

private def pullbackConstantAdjunction (T : X.ProEt) (hT : IsTerminal T) :
    constants X d ⋙ transport X d e ⊣
      global X d ((proEtaleBaseChange e.hom).obj T) :=
  ((constantAdjunction X d T hT).comp
    (proEtaleRingModuleAdjunction e.hom (ring X d) (ring X d)
      (coefficientIso X d e))).ofNatIsoRight (globalDirectIso X d e T)

private def constantPullbackIso : constants X d ⋙ transport X d e ≅ constants X d :=
  (pullbackConstantAdjunction X d e (⊤_ X.ProEt) terminalIsTerminal).leftAdjointUniq
    (constantAdjunction X d ((proEtaleBaseChange e.hom).obj (⊤_ X.ProEt))
      (terminalIsTerminal.isTerminalObj (proEtaleBaseChange e.hom)))

private theorem generator_natural (M : ModuleCat.{u + 1} A)
    {U V : X.ProEtᵒᵖ} (f : U ⟶ V) (x : M) :
    ((constants X d).obj M).val.map f (generator X d M U x) =
      generator X d M V x := by
  let η := (adicDatumOrdinaryAdjunction X
    (adicDatumScalar X (intrinsicPresentationDatum d))).unit.app
    ((adicLisseConstantModules X A).obj M)
  have hη (W : X.ProEtᵒᵖ) :
      η.val.app W (completedConstantGenerator X A M W x) = generator X d M W x := by
    dsimp only [η]
    erw [(adicDatumOrdinaryAdjunction_exists X
    (adicDatumScalar X (intrinsicPresentationDatum d))).choose_spec]
    exact (adicDatumOrdinaryUnit_exists X (adicDatumScalar X (intrinsicPresentationDatum d))
      ((adicLisseConstantModules X A).obj M)).exists.choose_spec W _
  rw [← hη U, ← hη V]
  refine (PresheafOfModules.naturality_apply η.val f _).symm.trans ?_
  congr 1
  exact (NatTrans.naturality_apply (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of M))) f x).symm

private theorem constantAdjunction_hom (T : X.ProEt) (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} A) (N : adicDatumModules X (intrinsicPresentationDatum d))
    (f : (constants X d).obj M ⟶ N) (x : M) :
    ((constantAdjunction X d T hT).homEquiv M N f) x =
      f.val.app (op T) (generator X d M (op T) x) := by
  rw [Adjunction.homEquiv_unit]
  change f.val.app (op T) (((constantAdjunction X d T hT).unit.app M) x) = _
  rw [constantAdjunction_unit]

private theorem constantPullbackIso_terminal (M : ModuleCat.{u + 1} A) (x : M) :
    ((constantPullbackIso X d e).hom.app M).val.app
        (op ((proEtaleBaseChange e.hom).obj (⊤_ X.ProEt)))
      (((proEtaleRingModuleAdjunction e.hom (ring X d) (ring X d)
        (coefficientIso X d e)).unit.app ((constants X d).obj M)).val.app
          (op (⊤_ X.ProEt)) (generator X d M (op (⊤_ X.ProEt)) x)) =
      generator X d M (op ((proEtaleBaseChange e.hom).obj (⊤_ X.ProEt))) x := by
  have h := congrArg (fun q ↦ q x)
    (Adjunction.homEquiv_leftAdjointUniq_hom_app
      (pullbackConstantAdjunction X d e (⊤_ X.ProEt) terminalIsTerminal)
      (constantAdjunction X d ((proEtaleBaseChange e.hom).obj (⊤_ X.ProEt))
        (terminalIsTerminal.isTerminalObj (proEtaleBaseChange e.hom))) M)
  dsimp only [pullbackConstantAdjunction] at h
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  change ((constantAdjunction X d (⊤_ X.ProEt) terminalIsTerminal).homEquiv
    M _ ((proEtaleRingModuleAdjunction e.hom (ring X d) (ring X d)
      (coefficientIso X d e)).homEquiv _ _
        ((constantPullbackIso X d e).hom.app M))) x = _ at h
  rw [constantAdjunction_hom, Adjunction.homEquiv_unit] at h
  change _ = ((constantAdjunction X d _ _).unit.app M) x at h
  rw [constantAdjunction_unit] at h
  exact h

private theorem constantPullbackIso_normalized :
    NormalizedConstants X d e (constantPullbackIso X d e) := by
  intro M U x
  let k := constantPullbackIso X d e
  let η := (proEtaleRingModuleAdjunction e.hom (ring X d) (ring X d)
    (coefficientIso X d e)).unit.app ((constants X d).obj M)
  let f := η ≫ (direct X d e).map (k.hom.app M)
  have h := (PresheafOfModules.naturality_apply f.val
    (terminal.from U).op (generator X d M (op (⊤_ X.ProEt)) x)).symm
  change ((constants X d).obj M).val.map
    ((proEtaleBaseChange e.hom).map (terminal.from U)).op
    ((k.hom.app M).val.app (op ((proEtaleBaseChange e.hom).obj (⊤_ X.ProEt)))
      (η.val.app (op (⊤_ X.ProEt)) (generator X d M (op (⊤_ X.ProEt)) x))) =
    (k.hom.app M).val.app (op ((proEtaleBaseChange e.hom).obj U)) (η.val.app (op U)
      (((constants X d).obj M).val.map (terminal.from U).op
        (generator X d M (op (⊤_ X.ProEt)) x))) at h
  rw [generator_natural] at h
  change _ = (k.hom.app M).val.app _ (η.val.app _ (generator X d M (op U) x)) at h
  rw [constantPullbackIso_terminal] at h
  exact h.symm.trans (generator_natural X d M
    ((proEtaleBaseChange e.hom).map (terminal.from U)).op x)

private theorem normalizedConstants_unique
    (k l : constants X d ⋙ transport X d e ≅ constants X d)
    (hk : NormalizedConstants X d e k) (hl : NormalizedConstants X d e l) : k = l := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (proEtaleRingModuleAdjunction e.hom (ring X d) (ring X d)
    (coefficientIso X d e)).homEquiv _ _ |>.injective
  apply (constantAdjunction X d (⊤_ X.ProEt) terminalIsTerminal).homEquiv _ _ |>.injective
  ext x
  rw [constantAdjunction_hom, constantAdjunction_hom, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  exact (hk M (⊤_ X.ProEt) x).trans (hl M (⊤_ X.ProEt) x).symm

/-- Completed constant modules have a uniquely generator-normalized pullback comparison.
Source: blueprint, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, penultimate sentence; the coefficient
normalization in step 2 of lem-wf-tensor-pullback-completion-unit-square.
(blueprint: lem-wf-completed-constant-pullback-normalization).

Proof: conjugate the completed scalar direct-image square by pbcCompletedComparison.
Compose the constant-module/global-sections adjunction with scalar extension.
Its unit sends x to the actual generator 1 tensor x. Direct image followed by
constant-scalar global sections is global sections on the base-changed object:
the scalar square makes the identity on section groups linear. Transport the
composite pullback adjunction by this identity, and use uniqueness of left
adjoints. Its unit equation gives the displayed generator formula at the terminal
object. Naturality along the terminal map gives the formula at every site object.
Conversely these formulas at the terminal object determine every component by
both adjunction bijections, proving uniqueness. This works for the zero ring and
zero module, and requires neither finite freeness nor flatness. -/
theorem completedConstantPullback_normalized :
    ∃! k : constants X d ⋙ transport X d e ≅ constants X d,
      NormalizedConstants X d e k := by
  refine ⟨constantPullbackIso X d e, constantPullbackIso_normalized X d e, ?_⟩
  intro k hk
  exact normalizedConstants_unique X d e k _ hk (constantPullbackIso_normalized X d e)

end WeilConjectures.WfTensorUnitSquare
