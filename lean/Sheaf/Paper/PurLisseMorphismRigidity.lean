/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Topology.Connected.Basic

import Sheaf.Paper.ProEtaleConstantModuleEncoding
import all Sheaf.AlgebraicGeometry.ProEtaleIntrinsicLisseFixed
import Sheaf.Paper.ProEtaleOriginFromFiniteModels
import WeilConjectures.ConstructibleSheaf.Rigidity
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import all Sheaf.Paper.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all Sheaf.CategoryTheory.SiteConstantModuleHom
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk

/-!
# Rigidity of morphisms between finite lisse sheaves

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-a1-inv/lem-pur-lisse-morphism-rigidity.md,
node `lem-pur-lisse-morphism-rigidity` (blueprint: lem-pur-lisse-morphism-rigidity).

The finite coefficient ring is the canonical constant coefficient ring attached to a
`PurityFiniteSetting`.  Module sheaves are represented in the ringed pro-etale category;
local constancy uses the recorded ringed-site predicate, and geometric stalks use
the recorded colimit construction with its action by the coefficient stalk ring.
-/

@[expose] public section

set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The canonical map on ringed module stalks, obtained by restricting the morphism to
pointed neighbourhoods and applying the existing module-colimit functor.
Source: Stacks Project, Tag 0F6B, and `def-weil-proetale-geometric-stalk`
(blueprint: lem-pur-lisse-morphism-rigidity). -/
noncomputable def purityProEtaleStalkMap (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {F G : proEtaleRingModules T (proEtaleConstantRing T P.Ring)}
    (y : Spec (.of Ω) ⟶ T) (f : F ⟶ G) :
    proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring) F ⟶
      proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring) G :=
  (PresheafOfModules.colimitFunctor
    (colimit.isColimit (proEtaleGeometricStalkRingDiagram y
      (proEtaleConstantRing T P.Ring)))).map
    ((PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
      ((proEtaleConstantRing T P.Ring).obj ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f.val)

/-- Finite lisse means local constancy as a module over the constant ring sheaf, together
with finite underlying sets at every geometric stalk. Both notions use their dependency
declarations directly; no condition of freeness is imposed.
Source: Stacks Project, Tag 099Y, and the finite-stalk convention of the blueprint node
(blueprint: lem-pur-lisse-morphism-rigidity). -/
noncomputable def PurityFiniteLisse (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (F : proEtaleRingModules T (proEtaleConstantRing T P.Ring)) : Prop :=
  IsLocallyConstantProEtaleModuleSheaf T P.Ring F ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ T),
      Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing T P.Ring) F)

/-- Vanishing of a map at one geometric point in the connected component of `x`.
The explicit field structures package the geometric-point quantifiers without changing their
meaning. Source: blueprint node, clause (2), and Stacks Project, Tag 0F6B
(blueprint: lem-pur-lisse-morphism-rigidity). -/
def PurityVanishingAtComponent (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))
    (f : L ⟶ M) (x : T) : Prop :=
  ∃ (Ω : Type u) (hΩ : Field Ω) (hΩalg : @IsAlgClosed Ω hΩ),
    let := hΩ
    let := hΩalg
    ∃ (y : Spec (.of Ω) ⟶ T),
      Set.range (((Scheme.Hom.toLRSHom' y).base : TopCat.Hom _ _).hom) ⊆
          connectedComponent x ∧
        purityProEtaleStalkMap P T y f = 0

private theorem scalarUnit_eq (T : Scheme.{u}) (B : Type u) [CommRing B] :
    homRingUnit (ProEt.topology T) (ULift.{u + 1, u} B) =
      proEtaleModuleScalarUnit T B := by
  exact sheafComposeNatTrans_fac (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1})
    (sheafificationAdjunction (ProEt.topology T) RingCat.{u + 1})
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B)))

private noncomputable def fixedConstantIso (T : Scheme.{u}) (B : Type u) [CommRing B]
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} B)) :
    (constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).obj M ≅
      (proEtaleModuleRestriction T B).obj
        ((constantModuleHomFunctor (ProEt.topology T) (ULift.{u + 1, u} B)).obj M) := by
  let J := ProEt.topology T
  let A := ULift.{u + 1, u} B
  let N := (proEtaleModuleRestriction T B).obj ((constantModuleHomFunctor J A).obj M)
  let η : (Functor.const T.ProEtᵒᵖ).obj M ⟶ N.obj :=
    { app U := ModuleCat.ofHom (Y := N.obj.obj U)
        { toFun := (constantModuleHomUnit J A M).app U
          map_add' x y := ((constantModuleHomUnit J A M).app U).hom.map_add x y
          map_smul' r x := by
            have h := ((homUnitLinear J A M).app U).hom.map_smul r x
            change (constantModuleHomUnit J A M).app U (r • x) =
              (homRingUnit J A).app U r • (constantModuleHomUnit J A M).app U x at h
            rw [scalarUnit_eq T B] at h
            exact h }
      naturality U V f := by
        ext x
        exact ConcreteCategory.congr_hom ((constantModuleHomUnit J A M).naturality f) x }
  let f := ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ N).symm η
  have hi : Presheaf.IsLocallyInjective J η := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (constantModuleHomUnit J A M) (forget AddCommGrpCat))
    infer_instance
  have hs : Presheaf.IsLocallySurjective J η := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (constantModuleHomUnit J A M) (forget AddCommGrpCat))
    infer_instance
  have hf : toSheafify J ((Functor.const T.ProEtᵒᵖ).obj M) ≫ f.hom = η :=
    ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ N).apply_symm_apply η
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso _).mp
    ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac J η hf,
      Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hf⟩
  exact asIso f

private theorem homObj_restrictOver_eq {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u + 1})]
    {R : Sheaf J CommRingCat.{u + 1}}
    (L M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj R)) (U : C) :
    PresheafOfModules.homObj (R := (Over.forget U).op ⋙ R.obj)
      ((PresheafOfModules.restrictOver R.obj U).obj L.val)
      ((PresheafOfModules.restrictOver R.obj U).obj M.val) =
      PresheafOfModules.homObj (R := (R.over U).obj) (L.over U).val (M.over U).val := by
  rfl

private noncomputable def overHomIso {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u + 1})]
    {R : Sheaf J CommRingCat.{u + 1}}
    (L M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj R)) (U : C) :
    (SheafOfModules.homObj (R := R) L M).over U ≅
      SheafOfModules.homObj (R := R.over U) (L.over U) (M.over U) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    (Iso.refl _ : ((SheafOfModules.homObj (R := R) L M).over U).val ≅
      (PresheafOfModules.restrictOver R.obj U).obj
        (SheafOfModules.homObj (R := R) L M).val) ≪≫
      PresheafOfModules.restrictOverHomObjIso (R := R.obj) L.val M.val U ≪≫
      eqToIso (homObj_restrictOver_eq L M U)

private noncomputable def liftModelIso (T : Scheme.{u}) (B : Type u) [CommRing B]
    (L : proEtaleRingModules T (proEtaleConstantRing T B)) (U : T.ProEt)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} B))
    (e : ((proEtaleModuleRestriction T B).obj L).over U ≅
      ((constantSheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).obj M).over U) :
    L.over U ≅ ((constantModuleHomFunctor (ProEt.topology T)
      (ULift.{u + 1, u} B)).obj M).over U := by
  let J := ProEt.topology T
  let A := ULift.{u + 1, u} B
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing T B)
  let a := Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit T B)
  have : Presheaf.IsLocallySurjective (J.over U) a :=
    (proEtaleConstantRingUnit_over_locallyBijective T B U).2
  exact (ConstantScalarComparison.restrictionFullyFaithful
    (J.over U) A (R.over U) a).preimageIso
      (e ≪≫ (J.overPullback (ModuleCat.{u + 1} A) U).mapIso (fixedConstantIso T B M))

private noncomputable def constantPullbackIso
    {X Y : Scheme.{u}} (A : Type (u + 1)) [CommRing A] (g : Y ⟶ X)
    [WeaklyEtale g] (M : ModuleCat.{u + 1} A) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj
      ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M) ≅
        (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M :=
  (ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} A) g inferInstance).app _ ≪≫
    (Functor.pushforwardContinuousSheafificationCompatibility
      (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale g))
        (ModuleCat.{u + 1} A) (ProEt.topology Y) (ProEt.topology X)).symm.app
          ((Functor.const X.ProEtᵒᵖ).obj M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def schemeModelToOver
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) (U : T.ProEt)
    (M : ModuleCat.{u + 1} A)
    (e : (ProEtale.upperStar (ModuleCat.{u + 1} A) U.hom).obj F ≅
      (constantSheaf (ProEt.topology U.left) (ModuleCat.{u + 1} A)).obj M) :
    F.over U ≅ ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} A)).obj M).over U := by
  have : (ProEt.sliceEquiv T U).inverse.IsDenseSubsite
      (ProEt.topology U.left) ((ProEt.topology T).over U) := ProEt.sliceDense T U
  let E := (ProEt.sliceEquiv T U).sheafCongr
    ((ProEt.topology T).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} A)
  let r (G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
      E.functor.obj (G.over U) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} A) U.hom U.prop).obj G :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv T U).constantSheafSheafCongrIso
    ((ProEt.topology T).over U) (ProEt.topology U.left)
    (ModuleCat.{u + 1} A) (Over.mkIdTerminal (X := U))).app M
  exact E.functor.preimageIso (r F ≪≫
    ((ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) U.hom U.prop).app F).symm ≪≫ e ≪≫ c.symm ≪≫
    E.functor.mapIso (constantSheafOverIso (ProEt.topology T) (ModuleCat.{u + 1} A) U M))

private theorem commonFiniteModels
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (hF : ProEtale.IsFiniteLocallyConstant A F)
    (hG : ProEtale.IsFiniteLocallyConstant A G) :
    ∃ (I : Type (u + 1)) (U : I → T.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 T)),
      Presieve.ofArrows U f ∈ ProEt.precoverage T (ProEt.mk (𝟙 T)) ∧
      ∀ i, ∃ P Q : ModuleCat.{u + 1} A, Finite P ∧ Finite Q ∧
        Nonempty (F.over (U i) ≅
          ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} A)).obj P).over (U i)) ∧
        Nonempty (G.over (U i) ≅
          ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} A)).obj Q).over (U i)) := by
  classical
  obtain ⟨I, X, g, hg, hp⟩ := hF
  obtain ⟨K, Y, h, hh, hq⟩ := hG
  choose P hP eP using hp
  choose Q hQ eQ using hq
  have (i : I) : WeaklyEtale (g i) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ hg ⟨i⟩
  have (j : K) : WeaklyEtale (h j) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ hh ⟨j⟩
  let Z (a : Σ _ : I, K) := pullback (h a.2) (g a.1)
  let k (a : Σ _ : I, K) : Z a ⟶ T := pullback.snd (h a.2) (g a.1) ≫ g a.1
  have hk : Presieve.ofArrows Z k ∈ proetalePrecoverage T :=
    Precoverage.comp_mem_coverings g hg (fun i j ↦ pullback.snd (h j) (g i))
      (fun i ↦ Precoverage.mem_coverings_of_isPullback h hh (g i) _ _
        (fun j ↦ (IsPullback.of_hasPullback (h j) (g i)).flip))
  let U (a : Σ _ : I, K) : T.ProEt := ProEt.mk (k a)
  let f (a : Σ _ : I, K) : U a ⟶ ProEt.mk (𝟙 T) :=
    MorphismProperty.Over.homMk (k a) (Category.comp_id _)
  refine ⟨Σ _ : I, K, U, f, ?_, ?_⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hk
  · rintro ⟨i, j⟩
    let p := pullback.fst (h j) (g i)
    let q := pullback.snd (h j) (g i)
    let eF : (ProEtale.upperStar (ModuleCat.{u + 1} A) (k ⟨i, j⟩)).obj F ≅
        (constantSheaf (ProEt.topology (Z ⟨i, j⟩)) (ModuleCat.{u + 1} A)).obj (P i) :=
      (ProEtale.upperStarComp (ModuleCat.{u + 1} A) q (g i)).app F ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} A) q).mapIso (eP i).some ≪≫
      constantPullbackIso A q (P i)
    let eG : (ProEtale.upperStar (ModuleCat.{u + 1} A) (k ⟨i, j⟩)).obj G ≅
        (constantSheaf (ProEt.topology (Z ⟨i, j⟩)) (ModuleCat.{u + 1} A)).obj (Q j) :=
      eqToIso (congrArg (fun k ↦ (ProEtale.upperStar (ModuleCat.{u + 1} A) k).obj G)
        (pullback.condition (f := h j) (g := g i)).symm) ≪≫
      (ProEtale.upperStarComp (ModuleCat.{u + 1} A) p (h j)).app G ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} A) p).mapIso (eQ j).some ≪≫
      constantPullbackIso A p (Q j)
    exact ⟨P i, Q j, hP i, hQ j, ⟨schemeModelToOver T A F (U ⟨i, j⟩) (P i) eF⟩,
      ⟨schemeModelToOver T A G (U ⟨i, j⟩) (Q j) eG⟩⟩

private noncomputable def homCongr {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u + 1})]
    {R : Sheaf J CommRingCat.{u + 1}}
    {L M L' M' : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj R)}
    (eL : L ≅ L') (eM : M ≅ M') :
    SheafOfModules.homObj (R := R) L M ≅ SheafOfModules.homObj (R := R) L' M' where
  hom := SheafOfModules.homObjMap eL.inv eM.hom
  inv := SheafOfModules.homObjMap eL.hom eM.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

private theorem finiteHomLocalModels
    (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (L M : proEtaleRingModules T (proEtaleConstantRing T B))
    (hL : ProEtale.IsFiniteLocallyConstant (ULift.{u + 1, u} B)
      ((proEtaleModuleRestriction T B).obj L))
    (hM : ProEtale.IsFiniteLocallyConstant (ULift.{u + 1, u} B)
      ((proEtaleModuleRestriction T B).obj M)) :
    ∃ (I : Type (u + 1)) (U : I → T.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 T)),
      Presieve.ofArrows U f ∈ ProEt.precoverage T (ProEt.mk (𝟙 T)) ∧
      ∀ i, ∃ V : ModuleCat.{u + 1} (ULift.{u + 1, u} B), Finite V ∧
        Nonempty (((proEtaleModuleRestriction T B).obj
          (SheafOfModules.homObj (R := proEtaleConstantRing T B) L M)).over (U i) ≅
            (constantSheaf ((ProEt.topology T).over (U i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B))).obj V) := by
  let J := ProEt.topology T
  let A := ULift.{u + 1, u} B
  let R := proEtaleModuleRestriction T B
  let C := constantModuleHomFunctor J A
  let O := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing T B)
  obtain ⟨I, U, f, hf, hm⟩ := commonFiniteModels T A (R.obj L) (R.obj M) hL hM
  refine ⟨I, U, f, hf, fun i ↦ ?_⟩
  obtain ⟨P, Q, hP, hQ, ⟨eP⟩, ⟨eQ⟩⟩ := hm i
  have : Finite P := hP
  have : Finite Q := hQ
  have : Module.Finite A P := Module.Finite.of_finite
  have : Module.FinitePresentation A P := Module.finitePresentation_of_finite A P
  let c := homComparison J A P Q
  have : IsIso c := homComparison_isIso J A P Q
  let eL := liftModelIso T B L (U i) P eP
  let eM := liftModelIso T B M (U i) Q eQ
  let V := ModuleCat.of A (P →ₗ[A] Q)
  have hV : Finite V :=
    Finite.of_injective (fun f : P →ₗ[A] Q ↦ (f : P → Q)) DFunLike.coe_injective
  let eH : (SheafOfModules.homObj (R := proEtaleConstantRing T B) L M).over (U i) ≅
      (C.obj V).over (U i) :=
    overHomIso L M (U i) ≪≫ homCongr eL eM ≪≫
      (overHomIso (C.obj P) (C.obj Q) (U i)).symm ≪≫
      (SheafOfModules.overFunctor O (U i)).mapIso (asIso c).symm
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit T B)
  let E := ConstantScalarComparison.restriction (J.over (U i)) A (O.over (U i)) a
  exact ⟨V, hV, ⟨E.mapIso eH ≪≫
    (J.overPullback (ModuleCat.{u + 1} A) (U i)).mapIso (fixedConstantIso T B V).symm ≪≫
    (constantSheafOverIso J (ModuleCat.{u + 1} A) (U i) V).symm⟩⟩

private theorem finiteStalksOfSliceModels
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (hF : ∃ (I : Type (u + 1)) (U : I → T.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 T)),
      Presieve.ofArrows U f ∈ ProEt.precoverage T (ProEt.mk (𝟙 T)) ∧
        ∀ i, ∃ V : ModuleCat.{u + 1} A, Finite V ∧
          Nonempty (F.over (U i) ≅
            (constantSheaf ((ProEt.topology T).over (U i)) (ModuleCat.{u + 1} A)).obj V))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    Finite (proEtaleGeometricFixedModuleStalk x A F) := by
  obtain ⟨I, U, f, hf, hm⟩ := hF
  let Φ := ProEtale.geometricPoint x
  obtain ⟨W, g, hg, w, hw⟩ := Φ.jointly_surjective
    (Sieve.generate (Presieve.ofArrows U f))
    (Precoverage.generate_mem_toGrothendieck hf)
    (ULift.up (Over.homMk x (Category.comp_id x)))
  obtain ⟨_, a, b, ⟨i⟩, hab⟩ := hg
  let v := Φ.fiber.map a w
  obtain ⟨V, hV, ⟨e⟩⟩ := hm i
  let E := ProEtale.geometricStalkIsoFiber x A F ≪≫
    (ProEtale.sheafFiberOverIso Φ v A F).symm ≪≫
    (Φ.over v).sheafFiber.mapIso e ≪≫ (Φ.over v).sheafFiberConstantSheafIso V
  exact Finite.of_equiv V E.toLinearEquiv.toEquiv.symm


set_option backward.isDefEq.respectTransparency false in
private theorem stalk_zero_of_ringed_stalk_zero (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ T)
    {L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring)} (f : L ⟶ M)
    (h : purityProEtaleStalkMap P T y f = 0) :
    colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget y).op
      ((proEtaleModuleRestriction T P.Ring).map f).hom) = 0 := by
  let D := proEtaleGeometricStalkDiagram y ((proEtaleModuleRestriction T P.Ring).obj L)
  let D' := proEtaleGeometricStalkDiagram y ((proEtaleModuleRestriction T P.Ring).obj M)
  let a : D ⟶ D' := Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget y).op
    ((proEtaleModuleRestriction T P.Ring).map f).hom
  let V := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} P.Ring)) AddCommGrpCat.{u + 1}
  apply V.map_injective
  change V.map (colim.map a) = 0
  apply (cancel_mono (preservesColimitIso V D').hom).mp
  rw [zero_comp]
  have hn := (preservesColimitNatIso V).hom.naturality a
  change V.map (colim.map a) ≫ (preservesColimitIso V D').hom =
    (preservesColimitIso V D).hom ≫ _ at hn
  rw [hn]
  have hz : colim.map (Functor.whiskerRight a V) = 0 := by
    have hh := congrArg
      (fun g ↦ (forget₂ (ModuleCat.{u + 1}
        (proEtaleGeometricStalkRing y (proEtaleConstantRing T P.Ring)))
          AddCommGrpCat.{u + 1}).map g) h
    dsimp only [purityProEtaleStalkMap, PresheafOfModules.colimitFunctor] at hh
    exact hh
  change (preservesColimitIso V D).hom ≫ colim.map (Functor.whiskerRight a V) = 0
  rw [hz, comp_zero]

private theorem rigidity_zero (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [Finite P.Ring]
    (L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))
    (hL : PurityFiniteLisse P T L) (hM : PurityFiniteLisse P T M)
    (f : L ⟶ M) (hf : ∀ x, PurityVanishingAtComponent P T L M f x) : f = 0 := by
  let A := ULift.{u + 1, u} P.Ring
  let R := proEtaleModuleRestriction T P.Ring
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  obtain ⟨L₀, hL₀, ⟨eL⟩⟩ := etale_origin_of_finite_models T A (R.obj L)
    ((finiteLocal_iff T P.Ring L).mpr hL)
  obtain ⟨M₀, hM₀, ⟨eM⟩⟩ := etale_origin_of_finite_models T A (R.obj M)
    ((finiteLocal_iff T P.Ring M).mpr hM)
  let f₀ : L₀ ⟶ M₀ := C.preimage (eL.hom ≫ R.map f ≫ eM.inv)
  have hmap : C.map f₀ = eL.hom ≫ R.map f ≫ eM.inv := C.map_preimage _
  have hzero : f₀ = 0 := by
    have := hL₀
    have := hM₀
    apply AlgebraicGeometry.Etale.eq_zero_of_sheafFiber_map_eq_zero f₀
    intro x
    obtain ⟨Ω, hΩ, hΩalg, y, hy, hfy⟩ := hf x
    let := hΩ
    let := hΩalg
    refine ⟨Ω, hΩ, inferInstance, y, hy ⟨IsLocalRing.closedPoint Ω, rfl⟩, ?_⟩
    obtain ⟨c, hc⟩ := (proEtale_comparison_stalk T Ω y).2.2 A
    let S := sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood y)ᵒᵖ T.ProEtᵒᵖ
        (ModuleCat.{u + 1} A)).obj (proEtaleGeometricNeighbourhoodForget y).op ⋙ colim
    have hs : S.map (R.map f) = 0 := stalk_zero_of_ringed_stalk_zero P T y f hfy
    have hn := c.hom.naturality f₀
    change S.map (C.map f₀) ≫ c.hom.app M₀ =
      c.hom.app L₀ ≫ (pointSmallEtale y).sheafFiber.map f₀ at hn
    simp only [hmap, Functor.map_comp, hs, comp_zero, zero_comp] at hn
    exact (cancel_epi (c.hom.app L₀)).mp (by simpa using hn.symm)
  have hr : R.map f = 0 := by
    have h := hmap
    rw [hzero, C.map_zero] at h
    apply (cancel_epi eL.hom).mp
    apply (cancel_mono eM.inv).mp
    simpa only [zero_comp, comp_zero, Category.assoc] using h.symm
  ext U x
  exact congrArg (fun g ↦ g.hom.app U x) hr

/-- The internal Hom of finite lisse pro-etale module sheaves is finite lisse.

Source: Stacks Project, Tag 093T, together with the finite constant-model and stalk
constructions recorded for this item (blueprint: lem-pur-lisse-morphism-rigidity).
The proof descends both sheaves to finite constant models on a common pro-etale cover,
uses the constant-module internal-Hom comparison for finitely presented modules, and
transports the resulting finite models and finite geometric stalks back to the intrinsic
ringed-site encoding. -/
private theorem purityFiniteLisse_homObj (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [Finite P.Ring]
    (L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))
    (hL : PurityFiniteLisse P T L) (hM : PurityFiniteLisse P T M) :
    PurityFiniteLisse P T
      (SheafOfModules.homObj (R := proEtaleConstantRing T P.Ring) L M) := by
  let H := SheafOfModules.homObj (R := proEtaleConstantRing T P.Ring) L M
  let R := proEtaleModuleRestriction T P.Ring
  let A := ULift.{u + 1, u} P.Ring
  have hm := finiteHomLocalModels T P.Ring L M
    ((finiteLocal_iff T P.Ring L).mpr hL) ((finiteLocal_iff T P.Ring M).mpr hM)
  refine ⟨(localConstancy_iff T P.Ring H).mpr ?_, fun Ω _ _ y ↦ ?_⟩
  · obtain ⟨I, U, f, hf, he⟩ := hm
    exact ⟨I, U, f, hf, fun i ↦ ⟨(he i).choose, (he i).choose_spec.2⟩⟩
  · exact (finite_stalk_iff T P.Ring H Ω y).mpr
      (finiteStalksOfSliceModels T A (R.obj H) hm Ω y)

/-- The internal Hom of finite lisse sheaves is finite lisse, and its maps are determined by
one geometric stalk on every connected component.

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-a1-inv/lem-pur-lisse-morphism-rigidity.md, Tags 093T, 093S, 03PR, 03PT, 03Q1 and 03WT
(blueprint: lem-pur-lisse-morphism-rigidity).

Proof plan, following the seven steps of the DAG node:
1. By `lem-sf-proetale-locally-constant-origin`, descend both finite lisse sheaves to the
etale site. The coefficient ring is finite by `def-weil-l-adic-coefficient-extension`.
Use `lem-weil-pbc-finite-locally-constant-module-values` and a fibre-product refinement
of the two trivializing covers to obtain common finite constant module values P_i, Q_i.
2. The comparison inclusion preserves covers. Its pullback commutes with restriction
(`lem-weil-pbc-comparison-pullback`) and preserves constant module sheaves: the comparison
adjunction and constant-sheaf universal property identify maps out of both constructions
with linear maps into global sections. Hence the same cover trivializes L and M on the
pro-etale site. Use `lem-weil-proetale-weakly-etale-localization` to identify slice sites.
3. Internal Hom commutes with localization (`def-pur-sheaf-hom`). A finite module over a
finite ring is finitely presented: take the free module on its finite underlying set;
its kernel is finite and generated by all its elements. Thus `lem-pur-site-constant-module-hom`
identifies the localized Hom with the constant module Hom(P_i,Q_i), a finite set. Lift each
geometric point to the etale cover, restrict the pointed-neighbourhood colimit cofinally,
and apply `lem-weil-proetale-constant-sheaf-stalk` to obtain finite stalks. This proves (1).
4. For (2), descend the morphism by the fully faithful comparison, using the unit
isomorphisms of `prop-weil-pbc-site-comparison-finite-level`. Naturality of the counit and
the triangle identities show that its inverse image is the original morphism.
`lem-cbc-proetale-comparison-stalk` carries the prescribed stalk vanishing to this map.
5. By `lemma-constructible-hom-constant-locally`, refine the common etale cover further
so that this descended map is induced by an actual linear map f_j of constant values.
6. Lift any fixed geometric point through each chart containing its image. The natural
pullback-stalk isomorphism (`lemma-openclosed-stalk-upperstar`) and constant-stalk
comparison identify the stalk map with f_j. Thus the zero locus is the union of chart
images with f_j = 0; its complement is the union with f_j nonzero. They are disjoint
open sets since etale morphisms are open (`lem-weil-pbc-etale-morphism-open-map`).
7. The zero locus meets each connected component, so connectedness makes it all of T.
Every nonempty chart then has f_j = 0; the empty-cover sheaf axiom handles empty charts.
For any etale object and section, the pulled-back covering and sheaf separatedness give
global vanishing of the descended map, hence of the original map. The same empty-cover
argument handles empty T. Apply this to the difference of two maps for the last assertion.
-/
theorem purLisseMorphismRigidity (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (CommRingCat.of P.field.k))]
    [IsSeparated (T ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of P.field.k))]
    (L M : proEtaleRingModules T (proEtaleConstantRing T P.Ring))
    (hL : PurityFiniteLisse P T L) (hM : PurityFiniteLisse P T M) :
    PurityFiniteLisse P T (SheafOfModules.homObj (R := proEtaleConstantRing T P.Ring) L M) ∧
      ((∀ (f : L ⟶ M),
          (∀ (x : T), PurityVanishingAtComponent P T L M f x) → f = 0) ∧
        (ConnectedSpace T →
          ∀ (f g : L ⟶ M) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (y : Spec (.of Ω) ⟶ T),
            purityProEtaleStalkMap P T y f = purityProEtaleStalkMap P T y g →
              f = g)) := by
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  refine ⟨purityFiniteLisse_homObj P T L M hL hM, rigidity_zero P T L M hL hM, ?_⟩
  intro hT f g Ω hΩ hΩalg y hfg
  let := hT
  let := hΩ
  let := hΩalg
  apply sub_eq_zero.mp
  apply rigidity_zero P T L M hL hM (f - g)
  intro x
  refine ⟨Ω, hΩ, hΩalg, y, ?_, ?_⟩
  · rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.subset_univ _
  · change (geometricRingModuleStalkFunctor y (proEtaleConstantRing T P.Ring)).map
      (f - g) = 0
    rw [Functor.map_sub]
    exact sub_eq_zero.mpr hfg

end WeilConjectures
