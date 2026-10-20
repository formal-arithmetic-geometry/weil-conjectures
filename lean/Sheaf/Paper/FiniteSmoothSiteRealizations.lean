/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData
import Sheaf.AlgebraicGeometry.CartierReductionSiteComparison

/-! # The normalized finite-root site realization

Source: main-20261015, sk-thm-smooth-purity, finite roots and final site transport
(blueprint: lem-pur-finite-smooth-site-realizations).
The private abelian comparison repeats the canonical Kan/sheafification construction of
SheafPullbackForgetComparison with abelian target coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
universe u₁ v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]
  {E : Type w} [Category.{max u₁ v} E] (U : E ⥤ AddCommGrpCat.{max u₁ v})
  [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K E] [J.HasSheafCompose U] [K.HasSheafCompose U]
  [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op]
/-- The comparison obtained by commuting forgetting past sheafification and left Kan
extension. Both comparisons are the canonical ones, so they respect the units.
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-weil-pbc-sheaf-pullback-forget-comparison). -/
private noncomputable def pullbackAbIso :
    sheafPullback F E J K ⋙ sheafCompose K U ≅
      sheafCompose J U ⋙ sheafPullback F (AddCommGrpCat.{max u₁ v}) J K :=
  NatIso.ofComponents (fun S ↦
    ((sheafComposeNatIso K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v}))).app (F.op.lan.obj S.obj)).symm ≪≫
    (presheafToSheaf K (AddCommGrpCat.{max u₁ v})).mapIso
      ((U.lanCompIsoOfPreserves F.op).app S.obj))
    (by
      intro S T g
      change (presheafToSheaf K E ⋙ sheafCompose K U).map (F.op.lan.map g.hom) ≫
          (sheafComposeNatIso K U (sheafificationAdjunction K E)
            (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v}))).inv.app _ ≫ _ = _
      rw [(sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v}))).inv.naturality_assoc]
      change _ ≫ (presheafToSheaf K (AddCommGrpCat.{max u₁ v})).map _ ≫
        (presheafToSheaf K (AddCommGrpCat.{max u₁ v})).map _ = _ ≫
        (presheafToSheaf K (AddCommGrpCat.{max u₁ v})).map _ ≫
          (presheafToSheaf K (AddCommGrpCat.{max u₁ v})).map _
      simp only [← Functor.map_comp]
      congr 2
      exact (U.lanCompIsoOfPreserves F.op).hom.naturality g.hom)
/-- The underlying comparison sends the algebraic inverse-image unit to the abelian unit.
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-weil-pbc-sheaf-pullback-forget-comparison).
Proof: expand the composite adjunction unit. The sheafification comparison satisfies
its defining unit equation. Naturality of the abelian sheafification unit then moves the
Kan-extension comparison to the left, where its defining unit equation applies. -/
private theorem pullbackAbIso_unit (S : Sheaf J E) :
    (sheafCompose J U).map ((sheafAdjunctionContinuous F E J K).unit.app S) ≫
      (F.sheafPushforwardContinuous (AddCommGrpCat.{max u₁ v}) J K).map
        ((pullbackAbIso J K F U).hom.app S) =
      (sheafAdjunctionContinuous F (AddCommGrpCat.{max u₁ v}) J K).unit.app
        ((sheafCompose J U).obj S) := by
  apply (sheafToPresheaf J (AddCommGrpCat.{max u₁ v})).map_injective
  simp only [Functor.map_comp]
  change Functor.whiskerRight ((sheafToPresheaf J E).map
      ((sheafAdjunctionContinuous F E J K).unit.app S)) U ≫ _ = _
  simp only [sheafAdjunctionContinuous, sheafPullback,
    Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [Functor.comp_obj, Functor.id_obj, Iso.refl_hom, NatTrans.id_app]
  simp only [Functor.map_id, Category.comp_id]
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Category.comp_id]
  change Functor.whiskerRight ((F.op.lanAdjunction E).unit.app S.obj ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K E).unit.app _)) U ≫
      Functor.whiskerLeft F.op
        (((sheafComposeNatIso K U (sheafificationAdjunction K E)
          (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v}))).inv.app _).hom ≫
        ((presheafToSheaf K (AddCommGrpCat.{max u₁ v})).map
          ((U.lanCompIsoOfPreserves F.op).hom.app S.obj)).hom) =
    (F.op.lanAdjunction (AddCommGrpCat.{max u₁ v})).unit.app (S.obj ⋙ U) ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K (AddCommGrpCat.{max u₁ v})).unit.app _)
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  have hs : Functor.whiskerRight
      ((sheafificationAdjunction K E).unit.app (F.op.lan.obj S.obj)) U ≫
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v}))).inv.app _).hom =
      (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v})).unit.app
        (F.op.lan.obj S.obj ⋙ U) := by
    have h := sheafComposeNatTrans_fac K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v})) (F.op.lan.obj S.obj)
    rw [← h]
    simp only [Category.assoc]
    change _ ≫ ((sheafToPresheaf K (AddCommGrpCat.{max u₁ v})).map
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v}))).hom.app _) ≫
      (sheafToPresheaf K (AddCommGrpCat.{max u₁ v})).map _) = _
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hn := (sheafificationAdjunction K (AddCommGrpCat.{max u₁ v})).unit.naturality
    ((U.lanCompIsoOfPreserves F.op).hom.app S.obj)
  have hk := U.leftKanExtensionCompIsoOfPreserves_hom_fac S.obj F.op
  ext V x
  have hs' := congrArg (fun t ↦ t.app (F.op.obj V)) hs
  have hn' := congrArg (fun t ↦ t.app (F.op.obj V)) hn
  have hk' := congrArg (fun t ↦ t.app V) hk
  simp only [Functor.lanAdjunction_unit] at hs' hn' hk' ⊢
  dsimp [Functor.lanCompIsoOfPreserves, Functor.lanUnit] at hs' hn' hk' ⊢
  simp only [Category.id_comp] at hk'
  have hsx := ConcreteCategory.congr_hom hs'
    ((U.map ((F.op.leftKanExtensionUnit S.obj).app V)) x)
  have hnx := ConcreteCategory.congr_hom hn'
    ((U.map ((F.op.leftKanExtensionUnit S.obj).app V)) x)
  have hkx := ConcreteCategory.congr_hom hk' x
  dsimp at hsx hnx hkx
  exact (congrArg (fun y ↦ (((presheafToSheaf K (AddCommGrpCat.{max u₁ v})).map
      (U.leftKanExtensionCompIsoOfPreserves S.obj F.op).hom).hom.app (F.op.obj V)) y)
    hsx).trans (hnx.symm.trans (congrArg (fun y ↦
      ((toSheafify K (F.op.leftKanExtension (S.obj ⋙ U))).app (F.op.obj V)) y) hkx))
end CategoryTheory

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem rootMapIsIso (ell n : ℕ) (T : Scheme.{u}) :
    IsIso (ordinaryFiniteRootMap (coefficient ell n) (ell ^ n)
      (CharP.cast_eq_zero _ _) T) := by
  let A := coefficient.{u} ell n
  let N := ell ^ n
  let e : ZMod N ≃+* A :=
    (ULift.ringEquiv.trans ULift.ringEquiv).symm
  have he : Scheme.finiteEtaleTwistScalar N A (CharP.cast_eq_zero _ _) = e.toRingHom :=
    RingHom.ext_zmod _ _
  let r := Scheme.finiteEtaleTwistScalar N A (CharP.cast_eq_zero _ _)
  have : (ModuleCat.restrictScalars.{u + 1} r).IsEquivalence := by
    dsimp only [r]
    rw [he]
    infer_instance
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} r
  have : (ModuleCat.extendScalars r).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  let F := Scheme.finiteEtaleMuModulePresheaf T N
  have hF : Presheaf.IsSheaf T.smallEtaleTopology F := by
    apply Presheaf.isSheaf_of_isSheaf_comp T.smallEtaleTopology F
      (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})
    exact (T.rootsOfUnitySheaf N).property
  have hE : Presheaf.IsSheaf T.smallEtaleTopology (F ⋙ ModuleCat.extendScalars r) :=
    Presheaf.isSheaf_comp_of_isSheaf T.smallEtaleTopology F (ModuleCat.extendScalars r) hF
  have := isIso_toSheafify T.smallEtaleTopology hE
  have happ : ∀ W, IsIso
      ((ordinaryFiniteRootMap A N (CharP.cast_eq_zero _ _) T).hom.app W) := by
    intro W
    change IsIso (((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map
      (adj.unit.app (F.obj W))) ≫
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).map
          ((toSheafify T.smallEtaleTopology (F ⋙ ModuleCat.extendScalars r)).app W))
    infer_instance
  have : IsIso (ordinaryFiniteRootMap A N (CharP.cast_eq_zero _ _) T).hom :=
    NatIso.isIso_of_isIso_app _
  change IsIso (ordinaryFiniteRootMap A N (CharP.cast_eq_zero _ _) T)
  let g := ordinaryFiniteRootMap A N (CharP.cast_eq_zero _ _) T
  have : IsIso ((sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).map g) := by
    change IsIso g.hom
    exact inferInstanceAs (IsIso (ordinaryFiniteRootMap A N (CharP.cast_eq_zero _ _) T).hom)
  exact isIso_of_reflects_iso g
    (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})

private instance rootForgetLeftAdjoint (A : Type (u + 1)) [CommRing A] :
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  let Z := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom A)
  have : Z.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom A)).isLeftAdjoint
  exact inferInstanceAs
    (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint

private instance rootForgetKan (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (Scheme.toProEt T).op := by
  let U := forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}
  intro F
  have : U.PreservesPointwiseLeftKanExtension F (Scheme.toProEt T).op := by
    intro V
    let : PreservesColimit (CostructuredArrow.proj (Scheme.toProEt T).op V ⋙ F) U :=
      PreservesColimitsOfShape.preservesColimit
    exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F _ V
  exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F _

private noncomputable def rootForgetIso (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        ProEtale.cartierForget A T ≅
      RawModuleScalarComparison.forget A T ⋙
        ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T :=
  CategoryTheory.pullbackAbIso T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rootForgetComparison_eq (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ProEtale.cartierForgetComparison A T M = (rootForgetIso T A).inv.app M := by
  have hu := CategoryTheory.pullbackAbIso_unit T.smallEtaleTopology
    (Scheme.ProEt.topology T) (Scheme.toProEt T)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M
  let R := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
  change (RawModuleScalarComparison.forget A T).map
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M) ≫
      R.map ((rootForgetIso T A).hom.app M) =
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
      ((RawModuleScalarComparison.forget A T).obj M) at hu
  have h : (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).unit.app
      ((RawModuleScalarComparison.forget A T).obj M) ≫
        R.map ((rootForgetIso T A).inv.app M) =
      (RawModuleScalarComparison.forget A T).map
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M) := by
    rw [← hu, Category.assoc, ← R.map_comp]
    rw [(rootForgetIso T A).hom_inv_id_app, R.map_id]
    exact Category.comp_id _
  apply ((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _).injective
  rw [ProEtale.cartierForgetComparison, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rootTransport (ell n : ℕ) (T : Scheme.{u})
    (hN : 0 < ell ^ n) (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))) :
    Nonempty (RootSiteTransport ell n T) := by
  let A := coefficient.{u} ell n
  let N := ell ^ n
  let hA : (N : A) = 0 := CharP.cast_eq_zero _ _
  let M := Scheme.finiteEtaleTateLine T N A hA
  let L := ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T
  let R := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} T
  let a := ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T
  have := rootMapIsIso ell n T
  have hforget : IsIso (ProEtale.cartierForgetComparison A T M) := by
    rw [rootForgetComparison_eq]
    infer_instance
  let m := L.map (ordinaryFiniteRootMap A N hA T) ≫
    ProEtale.cartierForgetComparison A T M
  have : IsIso m := by dsimp only [m]; infer_instance
  let e : proRootUnderlying ell n T ≅ Scheme.proEtaleRootsOfUnitySheaf T N :=
    (asIso m).symm ≪≫ ProEtale.cartierRootsIso T N hN hT
  have hm : m ≫ e.hom ≫ Scheme.proEtaleRootsOfUnityInclusion T N =
      L.map (kernel.ι (N • 𝟙 T.gmSheaf)) ≫ ProEtale.cartierUnitsComparison T := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
      IsIso.hom_inv_id_assoc]
    exact kernel.lift_ι _ _ _
  have hunit := (a.homEquiv T.gmSheaf (Scheme.proEtaleUnitsSheaf T)).apply_symm_apply
    (⟨𝟙 _⟩ : T.gmSheaf ⟶ R.obj (Scheme.proEtaleUnitsSheaf T))
  rw [Adjunction.homEquiv_unit] at hunit
  change a.unit.app T.gmSheaf ≫ R.map (ProEtale.cartierUnitsComparison T) = ⟨𝟙 _⟩ at hunit
  have hroots : a.unit.app (T.rootsOfUnitySheaf N) ≫
      R.map (m ≫ e.hom ≫ Scheme.proEtaleRootsOfUnityInclusion T N) =
      kernel.ι (N • 𝟙 T.gmSheaf) := by
    rw [hm, R.map_comp, ← Category.assoc]
    erw [← a.unit.naturality (kernel.ι (N • 𝟙 T.gmSheaf))]
    change (kernel.ι (N • 𝟙 T.gmSheaf) ≫ a.unit.app T.gmSheaf) ≫ _ = _
    rw [Category.assoc, hunit]
    apply Sheaf.hom_ext
    rfl
  have hmodule : a.unit.app (T.rootsOfUnitySheaf N) ≫ R.map m =
      ordinaryFiniteRootMap A N hA T ≫
        (RawModuleScalarComparison.forget A T).map
          ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M) := by
    rw [R.map_comp, ← Category.assoc]
    erw [← a.unit.naturality]
    change (ordinaryFiniteRootMap A N hA T ≫
      a.unit.app ((RawModuleScalarComparison.forget A T).obj M)) ≫ _ = _
    rw [Category.assoc]
    congr 1
    have hh := (a.homEquiv ((RawModuleScalarComparison.forget A T).obj M)
      ((ProEtale.cartierForget A T).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj M))).apply_symm_apply
      ((RawModuleScalarComparison.forget A T).map
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M))
    rw [Adjunction.homEquiv_unit] at hh
    exact hh
  have hz : ordinaryFiniteRootMap A N hA T ≫
      (RawModuleScalarComparison.forget A T).map
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M) ≫
      R.map (e.hom ≫ Scheme.proEtaleRootsOfUnityInclusion T N) =
        kernel.ι (N • 𝟙 T.gmSheaf) := by
    rw [← Category.assoc, ← hmodule, Category.assoc, ← R.map_comp]
    exact hroots
  refine ⟨⟨e, ?_⟩⟩
  intro U W v z
  have hzU := ConcreteCategory.congr_hom (congrArg (fun g ↦ g.hom.app U) hz) z
  have heNat := ConcreteCategory.congr_hom (e.hom.hom.naturality v.op)
    (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U
      (Scheme.finiteEtaleTateOneGenerator A N T hA U 1 z))
  have hiNat := ConcreteCategory.congr_hom
    ((Scheme.proEtaleRootsOfUnityInclusion T N).hom.naturality v.op)
    (e.hom.hom.app (Opposite.op ((Scheme.toProEt T).obj U.unop))
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U
        (Scheme.finiteEtaleTateOneGenerator A N T hA U 1 z)))
  dsimp only [AddCommGrpCat.comp_apply] at heNat hiNat
  change (Scheme.proEtaleRootsOfUnityInclusion T N).hom.app W
    (e.hom.hom.app W ((proRootLine ell n T).obj.map v.op _)) = _
  erw [heNat, hiNat]
  change (Scheme.proEtaleUnitsSheaf T).obj.map v.op
    ((Scheme.proEtaleRootsOfUnityInclusion T N).hom.app _
      (e.hom.hom.app _
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U
          (Scheme.finiteEtaleTateOneGenerator A N T hA U 1 z)))) = _
  erw [show (Scheme.proEtaleRootsOfUnityInclusion T N).hom.app _
      (e.hom.hom.app _
        (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app M).hom.app U
          (Scheme.finiteEtaleTateOneGenerator A N T hA U 1 z))) =
      (kernel.ι (N • 𝟙 T.gmSheaf)).hom.app U z from hzU]
  rfl

/-- The prescribed finite roots realization, including every comparison-unit generator.
Source: sk-thm-smooth-purity, finite roots and final site transport
(blueprint: lem-pur-finite-smooth-site-realizations).
Proof: the canonical scalar map from Z/(ell^n) to its double universe lift is a ring
isomorphism. Its scalar-extension unit is invertible. The roots presheaf is already a
sheaf, and scalar extension along this equivalence preserves its sheaf condition;
hence its sheafification unit is also invertible. These give the ordinary root map.
Commuting scalar forgetting with Kan extension and sheafification gives a comparison
isomorphism. Its unit identity identifies its inverse with cartierForgetComparison.
Compose this with the canonical Cartier roots isomorphism. Its kernel equation and
the adjunction equation of cartierUnitsComparison identify its value on every
comparison-unit generator. Naturality of the isomorphism and kernel inclusion gives
the required formula after every pro-etale restriction. Invertibility on X follows by
pullback of the global unit on Y. No choice of roots or local generators is made. -/
theorem finiteSmoothSiteRealizations
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    : ∀ n : ℕ, 1 ≤ n →
      Nonempty (RootSiteTransport ell n X) ∧ Nonempty (RootSiteTransport ell n Y) := by
  have hYglobal : IsUnit (ell : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using hY y
  have hXglobal : IsUnit (ell : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hYglobal.map f.appTop.hom
  intro n _
  have hN := pow_pos (Fact.out : ell.Prime).pos n
  exact ⟨rootTransport ell n X hN (by
      simpa only [Nat.cast_pow] using hXglobal.pow n),
    rootTransport ell n Y hN (by
      simpa only [Nat.cast_pow] using hYglobal.pow n)⟩

end AlgebraicGeometry.Etale.FiniteSmoothPurity
