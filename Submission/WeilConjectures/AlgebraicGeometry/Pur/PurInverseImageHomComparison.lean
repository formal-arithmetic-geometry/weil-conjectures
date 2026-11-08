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
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
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
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! Comparison constructions for inverse image along a scheme isomorphism. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v s h
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
end AlgebraicGeometry.Scheme.PurHom
namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (c : S ⟶ R) (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
private noncomputable abbrev restrict :=
  restrictScalars.{v} (Functor.whiskerRight c (forget₂ CommRingCat RingCat))
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
open PresheafOfModules
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) [B.IsEquivalence] (R : Dᵒᵖ ⥤ CommRingCat.{u}) {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (c : S ⟶ B.op ⋙ R) [IsIso c]
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
private noncomputable def homCongr {C : Type s} [Category.{h} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    {F F' G G' : SheafOfModules.{v} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : F ≅ F') (b : G ≅ G') :
    SheafOfModules.homObj (R := R) F G ≅ SheafOfModules.homObj (R := R) F' G' where
  hom := SheafOfModules.homObjMap (R := R) a.inv b.hom
  inv := SheafOfModules.homObjMap (R := R) a.hom b.inv
  hom_inv_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R),
      a.hom_inv_id, b.hom_inv_id, SheafOfModules.homObjMap_id (R := R)]
  inv_hom_id := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R),
      a.inv_hom_id, b.inv_hom_id, SheafOfModules.homObjMap_id (R := R)]

end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
section GenericAdjunction
variable {C : Type s} [Category.{h} C] {D : Type s} [Category.{h} D]
  (B : C ⥤ D) [B.IsEquivalence]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [B.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf K CommRingCat.{u}) (S : Sheaf J CommRingCat.{u})
  (c : S ⟶ (B.sheafPushforwardContinuous CommRingCat.{u} J K).obj R) [IsIso c]
variable (L : SheafOfModules.{max s h u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{max s h u} ((sheafCompose K
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  (adj : L ⊣ (SheafOfModules.pushforward.{max s h u} (F := B) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩))
  (hunit : ∀ M, IsIso (adj.unit.app M))
  [hreflect : ((SheafOfModules.pushforward.{max s h u} (F := B) (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u} RingCat.{u})⟩)).ReflectsIsomorphisms]
end GenericAdjunction
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme.PurHom
private instance commRingSheafify (Z : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology Z) CommRingCat.{u + 1} := inferInstance
private instance abelianSheafify (Z : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1} := inferInstance
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
end AlgebraicGeometry.Scheme.PurHom

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
