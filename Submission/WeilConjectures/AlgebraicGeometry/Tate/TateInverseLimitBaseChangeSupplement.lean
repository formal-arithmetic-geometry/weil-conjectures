/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageHomComparison
import Submission.WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import Submission.WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Submission.WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import Submission.WeilConjectures.Mathlib.CategoryTheory.NatIso
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.NumberTheory.Padics.RingHoms
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import Submission.WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Base change of an inverse-limit tower and its finite tensor reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, final sentence;
Stacks Project, Tags 03DB, 03CO and 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).

The index `op r` denotes the positive level `r + 1`. Scalar extension is the
recorded sheaf tensor construction, with its pure tensors written in the order `a ⊗ x`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingModulePullback proEtaleModuleInverseImage
  proEtaleRingModuleAdjunction

private abbrev tateRestrictedSectionModule
    (T : Scheme.{u}) {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y) ((ModuleCat.restrictScalars
      (((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

attribute [local instance] tateRestrictedSectionModule

private theorem tensorRestriction_tmul
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M).map i
      (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMapMixedUniverses.{u, u + 1, u + 1,
    u + 1} c M i) s m

private noncomputable def tensorToRestriction
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val) : M ⟶
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u
        + 1} RingCat.{u
        + 1})).map c)).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1,
      u + 1}
        (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul T, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (g : M ⟶ (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂
      CommRingCat.{u + 1}
      RingCat.{u + 1})).map c)).obj H) :
      SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (X := M.val.obj Y) (Y := H.val.obj Y) (g.val.app Y)
        ((SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u
        + 1}
        (c.hom.app X).hom (X := M.val.obj X) (Y := H.val.obj X) (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul T, map_one]
    have atOne (W : T.ProEtᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
          W).hom (X := M.val.obj W) (Y := H.val.obj W)).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val) ≃
      (M ⟶ (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂
        CommRingCat.{u + 1}
        RingCat.{u + 1})).map c)).obj H) where
  toFun := tensorToRestriction T c M H
  invFun := restrictionToTensor T c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom (X := M.val.obj W) (Y := H.val.obj W)).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom (X := M.val.obj W) (Y := H.val.obj W)).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H) ≃ (M ⟶
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u
        + 1} RingCat.{u
        + 1})).map c)).obj H) :=
  (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
    (P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M)
    (F := H)).trans (tensorPresheafHomEquiv T c M H)

-- Keep the tensor universal-property inverse folded after establishing its API.
-- Otherwise later equivalence comparisons unfold its sectionwise tensor construction.
attribute [local irreducible] restrictionToTensor

/-- The actual constant-coefficient module category.
Source: Stacks Tag 03DB (blueprint: lem-pur-tate-inverse-limit-base-change). -/
abbrev tateModules (T : Scheme.{u}) (R : Type u) [CommRing R] :=
  proEtaleRingModules T (proEtaleConstantRing T R)

/-- The constant sheaf map induced by a coefficient homomorphism.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateConstantMap (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : proEtaleConstantRing T R ⟶ proEtaleConstantRing T A :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (f.comp ULift.ringEquiv.toRingHom)))

/-- Restriction along the indicated constant coefficient map, with unchanged sections.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateRestrict (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : tateModules T A ⥤ tateModules T R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (tateConstantMap T f))

/-- The sheaf tensor `M ⊗_R A_T`, with its natural A-module structure.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTensor (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : tateModules T R) : tateModules T A :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateConstantMap T f) M

private def tensorUnit {T : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (a : R →+* A) (M : tateModules T R) :
    M ⟶ (tateRestrict T a).obj (tateTensor T a M) :=
  tensorHomEquiv T (tateConstantMap T a) M (tateTensor T a M) (𝟙 _)

attribute [local irreducible] tensorUnit

private def constantUnit (T : Scheme.{u}) (R : Type u) [CommRing R] :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} R)) ⟶
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T R)).obj :=
  adicLisseConstantUnit T (ULift.{u + 1, u} R)

private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallyInjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallyInjective T (ULift.{u + 1, u} R)

private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallySurjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallySurjective T (ULift.{u + 1, u} R)

attribute [local irreducible] tensorHomEquiv tensorPresheafHomEquiv tensorToRestriction

private theorem tateConstantMap_comp (T : Scheme.{u})
    {R Q A : Type u} [CommRing R] [CommRing Q] [CommRing A]
    (q : R →+* Q) (a : Q →+* A) :
    tateConstantMap T (a.comp q) = tateConstantMap T q ≫ tateConstantMap T a := by
  unfold tateConstantMap
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private def reductionUnit {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    L ⟶ (tateRestrict T (a.comp q)).obj (tateTensor T a G) where
  val :=
    { app U := ModuleCat.ofHom
        (X := L.val.obj U)
        (Y := ((tateRestrict T (a.comp q)).obj (tateTensor T a G)).val.obj U)
        { toFun := fun x ↦ (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U x))
          map_add' := by intros; simp only [map_add]
          map_smul' := by
            intro r x
            have hi := (i.inv.val.app U).hom.map_smul r (p.val.app U x)
            have hp := (p.val.app U).hom.map_smul r x
            have ht := ((tensorUnit a G).val.app U).hom.map_smul
              ((tateConstantMap T q).hom.app U r) (i.inv.val.app U (p.val.app U x))
            change (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U (r • x))) =
              (tateConstantMap T (a.comp q)).hom.app U r •
                (show (tateTensor T a G).val.obj U from
                  (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U x)))
            rw [tateConstantMap_comp]
            rw [hp, hi]
            exact ht }
      naturality := by
        intro U V f
        ext x
        exact (congrArg (fun y ↦ (tensorUnit a G).val.app V (i.inv.val.app V y))
          (PresheafOfModules.naturality_apply p.val f x)).trans
          ((congrArg (fun y ↦ (tensorUnit a G).val.app V y)
            (PresheafOfModules.naturality_apply i.inv.val f (p.val.app U x))).trans
            (PresheafOfModules.naturality_apply (tensorUnit a G).val f _)) }

attribute [local irreducible] reductionUnit

end AlgebraicGeometry.Scheme
