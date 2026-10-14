/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage
import Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackMate
import all Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso
import Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison
import Sheaf.AlgebraicGeometry.PerfectImpliesQCoh
import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
import Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import all Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange

/-! # Affine global Hom base change out of a proper flat direct image
Source: Stacks Project, Tag 0AA8, right-hand-side computation in case (1).
(blueprint: lem-sc-proper-flat-image-global-hom-base-change-isIso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Construct the tensor-Hom adjunction in the sheaf localization alone. -/
private theorem tensorHom_adjunction (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (P : schemeDerivedCategory S) :
    ∃ b : MonoidalCategory.tensorRight P ⊣ (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology S.toRingedSpace)
          S.toRingedSpace.sheaf)).obj (op P),
      (∀ A K, b.homEquiv A K = (schemeDerivedTensorHomEquiv S A P K).symm) ∧
      ∀ K, b.counit.app K = schemeDerivedTensorHomEquiv S
        ((derivedInternalHom (Opens.grothendieckTopology S.toRingedSpace)
          S.toRingedSpace.sheaf).obj (op P, K))
        P K (𝟙 _) := by
  let e := schemeDerivedTensorHomEquiv S
  have he : IsCanonicalDerivedTensorHom S e :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom S)
  let core : Adjunction.CoreHomEquiv (MonoidalCategory.tensorRight P)
      ((Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology S.toRingedSpace)
          S.toRingedSpace.sheaf)).obj (op P)) :=
    { homEquiv := fun A K ↦ (e A P K).symm
      homEquiv_naturality_left_symm := by
        intro A' A K a h
        change e A' P K (a ≫ h) = (MonoidalCategory.whiskerRight a P) ≫ e A P K h
        have hn := he.1 A A' P P K K a (𝟙 P) (𝟙 K) h
        erw [op_id, ← CategoryTheory.prod_id', CategoryTheory.Functor.map_id,
          Category.comp_id, MonoidalCategory.tensorHom_id, Category.comp_id] at hn
        exact hn
      homEquiv_naturality_right := by
        intro A K K' h c
        apply (e A P K').injective
        change e A P K' ((e A P K').symm (h ≫ c)) =
          e A P K' ((e A P K).symm h ≫
            (derivedInternalHom (Opens.grothendieckTopology S.toRingedSpace)
          S.toRingedSpace.sheaf).map (𝟙 (op P), c))
        simpa only [op_id, MonoidalCategory.id_tensorHom_id, Category.comp_id,
          Category.id_comp, Equiv.apply_symm_apply] using
          (he.1 A A P P K K' (𝟙 A) (𝟙 P) c ((e A P K).symm h)).symm }
  let b := Adjunction.mkOfHomEquiv core
  have hb (A K : schemeDerivedCategory S) : b.homEquiv A K = (e A P K).symm := by
    simp only [b, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  refine ⟨b, hb, ?_⟩
  intro K
  exact (b.homEquiv_symm_id K).symm.trans
    (congrArg (fun q ↦ q (𝟙 _)) (congrArg Equiv.symm (hb _ K)))

set_option maxHeartbeats 1600000 in
-- Transporting the derived tensor instances requires additional elaboration heartbeats.
/-- Base change on affine global Hom out of a proper flat direct image is invertible.
This map only involves derived pullback on the base and scalar extension; there are
no right adjoints or right-adjoint base-change maps in its statement.
Source: Stacks Project, Tag 0AA8, right-hand-side computation, case (1);
Tags 0A1H, 0B91 and 0A6A.
(blueprint: lem-sc-proper-flat-image-global-hom-base-change-isIso).

Proof: compute with the standard K-injective localizations, and transport to the
supplied derived categories by localization equivalences. Apply proper-support
perfect direct image to M and O_X in degree zero. Flatness makes O_X relatively
flat, finite presentation gives its finite presentation, and properness gives proper
support; the tensor unitor identifies the resulting complex with Rf_*M. Thus Rf_*M
is perfect. On the affine bases identify it with a bounded finite-projective complex
P over the global ring A; identify K with an arbitrary complex Q. Derived scalar
extension of Hom(P,Q) is Hom(A' tensor P,A' tensor Q), by perfect RHom base change.
The affine equivalences identify pullback with derived scalar extension. The
K-flat tensorator equations, evaluation mate equation and Leray derived-unit equations
identify the transpose of this algebraic map with mixedGlobalHomPullbackComparison.
The displayed map is therefore this isomorphism. No flatness of g or boundedness
of K is needed. The argument applies to zero M and to empty schemes. -/
theorem properFlatImage_globalHomBaseChange_isIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M : schemeDerivedQCohCategory X) (hM : Scheme.IsPerfect X M.obj)
    (K : schemeDerivedQCohCategory Y) :
    IsIso (((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
      (mixedGlobalHomPullbackComparison g ((schemeDerivedDirectImage f).obj M.obj) K.obj)) :=
  by
    classical
    let : Zero (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
      HasZeroObject.zero' (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let hD : ∀ Z : Scheme.{u},
        HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
      inferInstance
    let hX : ∀ U : X.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance
    have hopen (Z : Scheme.{u}) (U : Z.Opens) :
        Nonempty (HasDerivedCategory.{w}
          (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))) :=
      by
        let : HasDerivedCategory.{w}
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := hD U.toScheme
        exact hasDerivedCategory_of_equivalence
          (show SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U) ≌
            SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) from
              Scheme.Modules.overEquiv U)
    let hOpen : ∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U)) :=
      Function.update (fun Z U ↦ Classical.choice (hopen Z U)) X hX
    have hh : hOpen X = hX := Function.update_self _ _ _
    let : ∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U)) := hOpen
    have hM' : @Scheme.IsPerfect X _ (hOpen X) M.obj := by
      rw [hh]
      exact hM
    let G := (HomologicalComplex.single
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj
        (SheafOfModules.unit (moduleRings X.toRingedSpace))
    have hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n) := by
      refine ⟨0, 0, ?_⟩
      intro n hn
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    have hGfp : ∀ n : ℤ, (G.X n).IsFinitePresentation := by
      intro n
      dsimp [G, HomologicalComplex.single]
      split_ifs
      · infer_instance
      · exact isFinitePresentation_of_isZero X _ (isZero_zero _)
    have hGflat : ∀ n : ℤ, Scheme.Modules.IsFlatOver (G.X n) f := by
      intro n
      dsimp [G, HomologicalComplex.single]
      split_ifs
      · exact Scheme.Modules.isFlatOver_of_isInvertible f _
      · intro V U e
        let F := SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
          PresheafOfModules.evaluation _ (op U.1)
        have hz := Functor.map_isZero F
          (isZero_zero (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
        have : Subsingleton (F.obj
            (0 : SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
          ModuleCat.subsingleton_of_isZero hz
        let : Module Γ(Y, V.1) (F.obj
            (0 : SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
          Module.compHom _ (f.appLE V.1 U.1 e).hom
        change Module.Flat Γ(Y, V.1) (F.obj
          (0 : SheafOfModules.{u} (moduleRings X.toRingedSpace)))
        infer_instance
    have hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n) := by
      intro n
      have hclosed := (Scheme.Modules.finite_type_module_support_closed X (G.X n)).2.2.2
      refine ⟨⟨_, hclosed⟩, rfl, ?_⟩
      change IsProper (_ ≫ f)
      infer_instance
    have hp := (properSupport_perfect_directImage f M.obj hM' G hGb hGflat hGproper).1
    let e : MonoidalCategory.tensorObj M.obj (DerivedCategory.Q.obj G) ≅ M.obj :=
      MonoidalCategory.tensorIso (Iso.refl M.obj)
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
          (SheafOfModules.unit (moduleRings X.toRingedSpace))).symm ≪≫
        MonoidalCategory.rightUnitor M.obj
    have hP : Scheme.IsPerfect Y ((schemeDerivedDirectImage f).obj M.obj) := by
      intro y
      obtain ⟨U, hy, C, hC, ⟨c⟩⟩ := hp y
      exact ⟨U, hy, C, hC, ⟨(SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory.mapIso
          ((schemeDerivedDirectImage f).mapIso e.symm) ≪≫ c⟩⟩
    let P := (schemeDerivedDirectImage f).obj M.obj
    let H := (derivedInternalHom (Opens.grothendieckTopology Y)
      Y.sheaf).obj (op P, K.obj)
    let L := (derivedInternalHom (Opens.grothendieckTopology Y')
      Y'.sheaf).obj (op ((derivedPullback g).obj P), (derivedPullback g).obj K.obj)
    let theta : (derivedPullback g).obj H ⟶ L :=
      ((schemeDerivedTensorHomEquiv Y') ((derivedPullback g).obj H)
        ((derivedPullback g).obj P) ((derivedPullback g).obj K.obj)).symm
        ((mixedHomTensorPullbackIso g).inv.app (H, P) ≫
          (derivedPullback g).map
            ((schemeDerivedTensorHomEquiv Y) H P K.obj (𝟙 _)))
    have : IsIso theta := by
      obtain ⟨adj, _, adj', hadj, _, _, hadj'⟩ := scheme_derivedInternalHom_adjunction Y
      let PP : schemeDerivedQCohCategory Y :=
        ⟨P, schemeDerivedQCohProperty_of_isPerfect Y P hP⟩
      obtain ⟨D, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨p, _, _⟩, _⟩ :=
        perfect_rhom_tensor_comparison Y PP PP hP adj hadj adj' hadj'
      let := p
      let t := mixedHomTensorPullbackIso g
      have ht := Classical.choose_spec (exists_mixedHomTensorPullbackIso g)
      obtain ⟨m, hm⟩ := canonicalPullbackTensor_monoidal_realization g
        (fun A B ↦ t.hom.app (A, B)) ht
      let := m.toMonoidal
      have htensor (A B : schemeDerivedCategory Y) :
          t.inv.app (A, B) = Functor.LaxMonoidal.μ (derivedPullback g) A B := by
        have he : (m.μIso A B).symm = t.app (A, B) := Iso.ext (hm A B)
        exact (congrArg Iso.inv he).symm
      obtain ⟨bS, _, hcS⟩ := tensorHom_adjunction Y P
      obtain ⟨bT, heT, _⟩ := tensorHom_adjunction Y' ((derivedPullback g).obj P)
      change IsIso ((schemeDerivedTensorHomEquiv Y' ((derivedPullback g).obj H)
        ((derivedPullback g).obj P) ((derivedPullback g).obj K.obj)).symm
          (t.inv.app (H, P) ≫ (derivedPullback g).map _))
      rw [← heT, ← hcS, htensor]
      exact monoidal_adjunct_isIso (derivedPullback g) P D.obj K.obj _ _ bS bT
    have hH : schemeDerivedQCohProperty Y H :=
      rhom_supported_quasiCoherent_perfect_part Y P K.obj K.property hP
    obtain ⟨a, ha⟩ := exists_mixedAffineSectionsPullbackMate g H hH
    have hm := ha L theta
    change (((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
      (mixedGlobalHomPullbackComparison g P K.obj)) = _ at hm
    rw [hm]
    infer_instance


end AlgebraicGeometry
