/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
public import Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison
public import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Open localized pullback and the actual extension counit

Source: Stacks Project, Modules on Sites, Tags 03DI, 0F6Z and 04J0
(blueprint: lem-cbc-open-localized-counit-comparison).

We use the published `proEtaleSiteModel`, which retains every pro-etale object and
only enlarges the Hom universe. Localized sites are its literal Over categories.
The ring maps below are the constant-section maps, transported by precomposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The constant coefficient sheaf on the published small model, by precomposition.
Source: Stacks 04J0 and 0H7J (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenModelCoefficient (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    Sheaf (proEtaleModelTopology X) CommRingCat.{u + 1} :=
  ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of B))

/-- The actual constant-section structural map on the small models. Its adjunct is c_g.
Source: Stacks 04J0 and 0H7J (blueprint: lem-cbc-open-localized-counit-comparison). -/
def cbcOpenModelCoefficientMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] :
    cbcOpenModelCoefficient Y B ⟶
      ((proEtaleModelBaseChange g).sheafPushforwardContinuous CommRingCat.{u + 1}
        (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
          (cbcOpenModelCoefficient X B) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of B)).hom⟩

/-- Tensor pullback in small-model coordinates, along the canonical coefficient map.
`pullbackIso` identifies it with presheaf module pullback followed by sheafification.
Source: Stacks 03D2 and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenFinitePullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] :=
  SheafOfModules.pullback
    (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
      (cbcOpenModelCoefficientMap g B))

/-- The actual sheafified direct-sum extension, without a replacement left adjoint.
Source: Stacks 03DI (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenExtension (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (U : Y.ProEt) :=
  SheafOfModules.localizedSystemExtension.{u + 1, u + 1, u + 1}
    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U)

/-- The target restriction: the open object is precisely base change of U along g.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenTargetRestriction {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
    (cbcOpenModelCoefficient X B) ((proEtaleModelBaseChange g).obj (AsSmall.up.obj U))

/-- H = j'^* g_B^* j_!, with composition in Lean's left-to-right order.
Source: Stacks 03DI and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenLocalizedPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  cbcOpenExtension Y B U ⋙ cbcOpenFinitePullback g B ⋙ cbcOpenTargetRestriction g B U

/-- beta is literally pullback of the actual counit, followed by target restriction.
Source: Stacks 03DI and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
def cbcOpenLocalizedCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :
    (SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
        (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U)) ⋙ cbcOpenLocalizedPullback g B U ⟶
      cbcOpenFinitePullback g B ⋙ cbcOpenTargetRestriction g B U :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
        (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).counit _ ≫
      (Functor.leftUnitor _).hom

/-- Continuity for the literal localized base-change functor, with no extra hypothesis.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
instance cbcOpenSliceContinuous {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.ProEt) :
    (Over.post (X := AsSmall.up.obj U) (proEtaleModelBaseChange g)).IsContinuous
      ((proEtaleModelTopology Y).over (AsSmall.up.obj U))
      ((proEtaleModelTopology X).over
        ((proEtaleModelBaseChange g).obj (AsSmall.up.obj U))) :=
  overPost_isContinuous (proEtaleModelTopology Y) (proEtaleModelTopology X)
    (proEtaleModelBaseChange g) (AsSmall.up.obj U)

/-- The localized tensor pullback g_{U,B}^* in slice coordinates, with the restricted
canonical coefficient map, rather than a separately chosen ring structure.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenSlicePullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  SheafOfModules.pullback
    (SheafOfModules.sliceModuleRingMap (proEtaleModelBaseChange g)
      (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
        (cbcOpenModelCoefficientMap g B)) (AsSmall.up.obj U))

/-- The canonical localized pullback comparison is the inverse mate of the
sectionwise identity direct-image square, as in the recorded ringed localization theorem.
Source: Stacks 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenSliceComparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] (U : Y.ProEt) :=
  SheafOfModules.sliceModulePullbackMap (proEtaleModelBaseChange g)
    (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
      (cbcOpenModelCoefficientMap g B)) (AsSmall.up.obj U)

/-- The sheafification unit on the actual extension presheaf; its values on summands
are the generators used in both adjunction formulas below.
Source: Stacks 03DI (blueprint: lem-cbc-open-localized-counit-comparison). -/
abbrev cbcOpenExtensionGenerator (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (U : Y.ProEt)
    (F : SheafOfModules.{u + 1}
      (((sheafCompose (proEtaleModelTopology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (cbcOpenModelCoefficient Y B)).over (AsSmall.up.obj U))) :=
  (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 _)).unit.app
    ((SheafOfModules.extensionByZeroPresheaf.{u + 1} _ (AsSmall.up.obj U)).obj F)

/-- An inverse-image/tensor generator [V, psi, s] tensor b: the pullback-adjunction
unit gives [V, id, s] tensor 1, restriction gives psi, and scalar multiplication gives b.
This defines sections without asserting that all sheaf sections are global generators.
Source: Stacks 03D2 and 04J0 (blueprint: lem-cbc-open-localized-counit-comparison). -/
def cbcOpenPullbackGenerator {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B]
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (proEtaleModelTopology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (cbcOpenModelCoefficient Y B)))
    (V : proEtaleSiteModel Y) (W : proEtaleSiteModel X)
    (psi : W ⟶ (proEtaleModelBaseChange g).obj V) (s : M.val.obj (op V))
    (b : (cbcOpenModelCoefficient X B).obj.obj (op W)) :
    ((cbcOpenFinitePullback g B).obj M).val.obj (op W) :=
  b • ((cbcOpenFinitePullback g B).obj M).val.map psi.op
    ((SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange g)
        (cbcOpenModelCoefficientMap g B))).unit.app M |>.val.app (op V) <| s)

open Classical in
/-- Open localized finite pullback is the pulled-back extension counit, with its
canonical normalization on every summand. The open immersion is represented by U.hom;
its cartesian inverse image is the object `(proEtaleBaseChange g).obj U`.
Source: Stacks 03DI, 0F6Z and 04J0
(blueprint: lem-cbc-open-localized-counit-comparison).

Proof:
1. Use def-weil-proetale-inverse-image and lem-weil-proetale-weakly-etale-localization
   to identify the sites and their slices. The constant-section structure maps of
   prop-weil-pbc-proetale-constant-ring-map restrict to the same constants on the slice.
   lem-weil-pbc-localize-ringed-site-morphism gives the canonical lambda above.
2. The direct-sum Hom bijection evaluates each summand, and its inverse inserts each
   section into its summand. Compose with def-weil-presheaf-modules-sheafification.
   Applying these transpositions to identities gives exactly the unit and counit formulas.
3. Openness gives at most one arrow into U. Restricting the extension presheaf to U
   therefore leaves precisely F. The unit-compatible comparison of
   lem-cbc-sieve-slice-sheafification identifies the unit with sheafification of F;
   as F is a sheaf, this unit is invertible, including for the empty open.
4. Define alpha_F = lambda_(j_!F)^(-1) followed by g_{U,B}^*(eta_F^(-1)).
   Naturality of lambda at epsilon and j^*(epsilon) eta = id give beta = alpha lambda.
   Hence beta is invertible. Applying pullback to the summand evaluation gives the
   generator formula [V,psi,iota(s)] tensor b |-> [V,psi,s] tensor b, using precisely
   def-pur-sheaf-tensor-product; balancing and sheafification preserve this equality. -/
theorem cbcOpenLocalizedCounitComparison {X Y : Scheme.{u}} (g : X ⟶ Y)
    (B : Type (u + 1)) [CommRing B] [Finite B] (U : Y.ProEt) [IsOpenImmersion U.hom] :
    IsIso (cbcOpenLocalizedCounit g B U) ∧
    IsIso (cbcOpenSliceComparison g B U) ∧
    ∃ alpha : cbcOpenLocalizedPullback g B U ≅ cbcOpenSlicePullback g B U,
      (∀ F, alpha.inv.app F =
        (cbcOpenSlicePullback g B U).map
          (((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).unit.app F) ≫
          (cbcOpenSliceComparison g B U).app ((cbcOpenExtension Y B U).obj F)) ∧
      (∀ M, (cbcOpenLocalizedCounit g B U).app M =
        alpha.hom.app (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M) ≫
          (cbcOpenSliceComparison g B U).app M) ∧
      (∀ (F : SheafOfModules.{u + 1}
          (((sheafCompose (proEtaleModelTopology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (cbcOpenModelCoefficient Y B)).over (AsSmall.up.obj U)))
        (W : Over (AsSmall.up.obj U)) (s : F.val.obj (op W)),
        (((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).unit.app F).val.app (op W) s =
          (cbcOpenExtensionGenerator Y B U F).app (op W.left)
            (DirectSum.lof ((cbcOpenModelCoefficient Y B).obj.obj (op W.left))
              (W.left ⟶ AsSmall.up.obj U) (fun a ↦ F.val.obj (op (Over.mk a))) W.hom s)) ∧
      (∀ (M : SheafOfModules.{u + 1}
          ((sheafCompose (proEtaleModelTopology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (cbcOpenModelCoefficient Y B)))
        (W : Over (AsSmall.up.obj U)) (s : M.val.obj (op W.left)),
        (((SheafOfModules.localizedSystemAdjunction.{u + 1, u + 1, u + 1}
            (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).counit.app M).val.app (op W.left)
          ((cbcOpenExtensionGenerator Y B U
            (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
              (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M)).app
            (op W.left)
              (DirectSum.lof ((cbcOpenModelCoefficient Y B).obj.obj (op W.left))
                (W.left ⟶ AsSmall.up.obj U)
                (fun a ↦ (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M).val.obj
                      (op (Over.mk a)))
                W.hom s)) = s) ∧
      (∀ (M : SheafOfModules.{u + 1}
          ((sheafCompose (proEtaleModelTopology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (cbcOpenModelCoefficient Y B)))
        (V : proEtaleSiteModel Y) (phi : V ⟶ AsSmall.up.obj U)
        (W : Over ((proEtaleModelBaseChange g).obj (AsSmall.up.obj U)))
        (psi : W ⟶ (Over.post (proEtaleModelBaseChange g)).obj (Over.mk phi))
        (s : M.val.obj (op V)) (b : (cbcOpenModelCoefficient X B).obj.obj (op W.left)),
        ((cbcOpenLocalizedCounit g B U).app M).val.app (op W)
          (cbcOpenPullbackGenerator g B
            ((cbcOpenExtension Y B U).obj
              (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M))
            V W.left psi.left
            ((cbcOpenExtensionGenerator Y B U
              (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M)).app
              (op V) (DirectSum.lof ((cbcOpenModelCoefficient Y B).obj.obj (op V))
                (V ⟶ AsSmall.up.obj U)
                (fun a ↦ (((SheafOfModules.localizedSystemRestriction.{u + 1, u + 1, u + 1}
                    (cbcOpenModelCoefficient Y B) (AsSmall.up.obj U))).obj M).val.obj
                      (op (Over.mk a)))
                phi s)) b) =
          cbcOpenPullbackGenerator g B M V W.left psi.left s b) := by
  sorry

end AlgebraicGeometry.Scheme
