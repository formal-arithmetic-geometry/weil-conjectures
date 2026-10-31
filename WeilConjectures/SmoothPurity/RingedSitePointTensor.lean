/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RingedSitePoint
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import WeilConjectures.SmoothPurity.CochainInverseComparison
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.PUnit
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import WeilConjectures.ProperBaseChange.GeometricModuleTransport
import WeilConjectures.SmoothPurity.CochainTensoratorExistence
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Total tensor products and module stalks at a topos point -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.RingedSitePoint

private abbrev point : (Discrete PUnit.{w + 1})ᵒᵖ := Opposite.op ⟨PUnit.unit⟩

private def constant (A : Type*) [Category A] :
    A ⥤ Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{w + 1})) A :=
  Functor.const _ ⋙ (sheafBotEquivalence A).inverse

private def pointRing (A : CommRingCat.{w}) := (constant CommRingCat.{w}).obj A

private abbrev pointModules (A : CommRingCat.{w}) := SheafOfModules.{w}
  ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj (pointRing A))

private instance (A : CommRingCat.{w}) : (moduleConstant A).Additive where
  map_add := by intros; rfl

private abbrev moduleEval (A : CommRingCat.{w}) : pointModules A ⥤ ModuleCat.{w} A :=
  SheafOfModules.evaluation _ point

private instance (A : CommRingCat.{w}) : (moduleEval A).IsEquivalence :=
  (moduleEquivalence A).isEquivalence_functor

private instance (A : CommRingCat.{w}) : (moduleEval A).Additive where
  map_add := by intros; rfl

private def tensorMap {A : CommRingCat.{w}} (M N : pointModules A) :
    M.val ⊗ N.val ⟶
      (letI := SheafOfModules.monoidalCategory (pointRing A)
       M ⊗ N).val := by
  let := SheafOfModules.monoidalCategory (pointRing A)
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := pointRing A) M N).inv.val

private theorem tensorMap_isIso {A : CommRingCat.{w}} (M N : pointModules A) :
    IsIso (tensorMap M N) := by
  let := SheafOfModules.monoidalCategory (pointRing A)
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙
    ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj (pointRing A)).obj)
  have : IsIso (adj.unit.app (M.val ⊗ N.val)) :=
    adj.isIso_unit_app_of_iso (X := ⟨M.val ⊗ N.val, Presheaf.isSheaf_bot _⟩) (Iso.refl _)
  have : IsIso (SheafOfModules.tensorObjIsoSheafification
      (R := pointRing A) M N).inv.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      (SheafOfModules.tensorObjIsoSheafification (R := pointRing A) M N).inv))
  change IsIso (adj.unit.app (M.val ⊗ N.val) ≫ _)
  infer_instance

private def tensorIso {A : CommRingCat.{w}} (M N : pointModules A) :
    letI := SheafOfModules.monoidalCategory (pointRing A)
    (moduleEval A).obj M ⊗ (moduleEval A).obj N ≅ (moduleEval A).obj (M ⊗ N) := by
  have := tensorMap_isIso M N
  exact (PresheafOfModules.evaluation _ point).mapIso (asIso (tensorMap M N))

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
  {p : GeometricMorphism (Type w) (Sheaf J (Type w))}

end CategoryTheory.RingedSitePoint
