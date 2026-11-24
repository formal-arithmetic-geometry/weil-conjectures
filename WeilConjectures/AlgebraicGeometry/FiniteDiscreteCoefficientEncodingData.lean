/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ConstantInternalModuleSheafEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteModuleCategories
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing

/-! # A common sectionwise finite-coefficient encoding

The same functor on internal modules in abelian groups is used on every site.
The coefficient-ring identification is pulled back from one fixed profinite point.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme CategoryTheory.ConstantInternalModuleSheafEncoding

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

local instance instHasLimitsOfSizeFiniteDiscreteCoefficientEncodingData :
    HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

/-- Encode coefficient sheaves using a single sectionwise encoding and point ring
(Bhatt--Scholze, Proposition 5.3.2). -/
@[irreducible] noncomputable def finiteDiscreteCoefficientEquivalence (T : Scheme.{u}) :
    FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T := by
  letI : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  exact (sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG).asEquivalence.symm.trans
    (Mod.comapEquivalenceOfIsIso (finiteDiscreteSchemeRingIso B T eR).hom).symm

end AlgebraicGeometry.ProEtale.CondensedRing
