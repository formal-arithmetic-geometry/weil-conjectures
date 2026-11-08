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
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all Submission.WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! The normalized scalar-extension comparison. -/
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s h
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.PurScalar
open SheafOfModules
private abbrev ringSheaf {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev restriction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :=
  SheafOfModules.restrictScalars.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map c)

private noncomputable local instance
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A : Sheaf K CommRingCat.{u}} (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((ringSheaf A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c M).map i
        (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  changeOfRingsMap_tmulOfUniverses.{h, s, u, u} c M i s m

private noncomputable def tensorPresheafFunctor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ PresheafOfModules.{u} (ringSheaf S).obj where
  obj M := changeOfRingsPresheafOfUniverses.{h, s, u, u} c M
  map {M N} f :=
    show changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶
      changeOfRingsPresheafOfUniverses.{h, s, u, u} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturalityOfUniverses.{h, s, u, u} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ SheafOfModules.{u} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (f : changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val) :
    M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) :
    changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheafOfUniverses.{h, s, u, u} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    {M N : SheafOfModules.{u} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{u} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A))
    {H H' : SheafOfModules.{u} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

@[irreducible] private noncomputable def tensorAdjunction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

attribute [local irreducible] proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (O O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (α : O ⟶ O')
attribute [local irreducible] SheafOfModules.changeOfRingsOfUniverses

attribute [local semireducible] SheafOfModules.changeOfRingsOfUniverses
  proEtaleModuleInverseImage

end AlgebraicGeometry.Scheme.PurScalar
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
