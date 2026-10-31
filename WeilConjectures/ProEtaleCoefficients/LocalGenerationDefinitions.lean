/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Explicit constant-module objects for the local-generation comparison

(blueprint: def-sfb-local-generation-constant-module)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The internal constant module, formed from the constant presheaf of ordinary modules,
then its pointwise tensor action, then monoidal abelian sheafification.

Source: the constant-action construction in the statement of
lem-sfb-constant-module-object-local-generation and the Kernels paragraph of its source.
(blueprint: def-sfb-local-generation-constant-module)
-/
def localGenerationConstantModule (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (P : Type (u + 1)) [AddCommGroup P] [Module B P] :
    Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B) :=
  (Functor.const (Scheme.ProEt Y)ᵒᵖ ⋙ Presheaf.moduleToMod B ⋙
    (presheafToSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).mapMod
      (Presheaf.constRingObj B)).obj (ModuleCat.of B P)

/-- The sectionwise constant module restricted to the slice over a pro-etale object.

Source: the sectionwise restriction in lem-sfb-constant-module-object-local-generation,
using def-sf-site-constant-module-functor and def-pur-localized-ringed-site.
(blueprint: def-sfb-local-generation-constant-module)
-/
def localGenerationRestrictedModule (Y : Scheme.{u}) (V : Y.ProEt)
    (B : Type (u + 1)) [CommRing B] (P : Type (u + 1))
    [AddCommGroup P] [Module B P] :
    SheafOfModules.{u + 1}
      (((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
        (RingCat.of B)).over V) :=
  (SheafOfModules.overFunctor
    ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj (RingCat.of B)) V).obj
      ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B).obj
        (ModuleCat.of B P))

end AlgebraicGeometry.ProEtale
