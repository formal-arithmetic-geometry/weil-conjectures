/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
/-!
# Unit comparison for the canonical pro-etale module adjunction

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: new-lem-weil-pbc-proetale-module-canonical-unit)
-/

@[expose] public section
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- A normalized isomorphism identifies the mate with its inverse.
private noncomputable def fromModelHomEquiv {X : Scheme.{u}}
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (P : SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A))
    (N : SheafOfModules.{u + 1} A) :
    ((proEtaleModuleFromModel A).obj P ⟶ N) ≃
      (P ⟶ (proEtaleModuleToModel A).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply h.val (AsSmall.down.op.map i) m } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply g.val (AsSmall.up.op.map i) m } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl


-- Restrict the original abelian adjunction to the model sites, retaining its unit.
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
private abbrev A := (sheafCompose (ProEt.topology Y)
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
private noncomputable abbrev B := (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
private noncomputable abbrev T := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
  (J := ProEt.topology Y) (K := ProEt.topology X) (S := A R) (R := B f R)
  ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
private noncomputable def directEquiv
    (M : SheafOfModules.{u + 1} (A R)) (N : SheafOfModules.{u + 1} (B f R)) :
    ((proEtaleModuleToModel (A R)).obj M ⟶
      (SheafOfModules.pushforward (proEtaleModelRingUnit f R)).obj
        ((proEtaleModuleToModel (B f R)).obj N)) ≃ (M ⟶ (T f R).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply h.val (AsSmall.up.op.map i) m } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply g.val (AsSmall.down.op.map i) m } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
private noncomputable def homEquiv
    (M : SheafOfModules.{u + 1} (A R)) (N : SheafOfModules.{u + 1} (B f R)) :
    ((proEtaleModuleInverseImage f R).obj M ⟶ N) ≃ (M ⟶ (T f R).obj N) :=
  (fromModelHomEquiv _ _ _).trans
    (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).homEquiv
      _ _).trans (directEquiv f R M N))
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
end AlgebraicGeometry.Scheme
