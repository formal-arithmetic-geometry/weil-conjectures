/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import Sheaf.Paper.FiniteDiscreteRealizationFunctor
public import Sheaf.Paper.ConstantInternalModuleSheafEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Sheaf.Paper.FiniteDiscreteSchemeRing

/-! # A common sectionwise finite-coefficient encoding

The same functor on internal modules in abelian groups is used on every site.
The coefficient-ring identification is pulled back from one fixed profinite point.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

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

local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

/-- Encode coefficient sheaves using a single sectionwise encoding and point ring.
Source: Bhatt--Scholze, Proposition 5.3.2; the constructive constant-ring encoding
(blueprint: def-weil-pbc-common-finite-discrete-encoding).

Construction. Invert the sectionwise sheafEncoding for the fixed G, then invert
restriction of scalars along the ring isomorphism pulled back from eR at the point.
Both functors and their equivalence structures are given by proved constructions. -/
@[irreducible] noncomputable def finiteDiscreteCoefficientEquivalence (T : Scheme.{u}) :
    FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T := by
  letI : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  exact (sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG).asEquivalence.symm.trans
    (Mod.comapEquivalenceOfIsIso (finiteDiscreteSchemeRingIso B T eR).hom).symm

/-- This coefficient encoding preserves the underlying abelian sheaf. -/
noncomputable def finiteDiscreteCoefficientEquivalenceForgetIso (T : Scheme.{u}) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).functor ⋙ Mod.forget _ ≅
      sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) := by
  letI : ((ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
    GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})
  let H := sheafEncoding (ProEt.topology T) (ULift.{u + 1} B) G hG
  let U := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  unfold finiteDiscreteCoefficientEquivalence
  change H.inv ⋙ Mod.forget _ ≅ U
  exact Functor.isoWhiskerLeft H.inv
      (sheafEncodingForgetIso (ProEt.topology T) (ULift.{u + 1} B) G hG).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight H.asEquivalence.counitIso U ≪≫ Functor.leftUnitor U

end AlgebraicGeometry.ProEtale.CondensedRing
