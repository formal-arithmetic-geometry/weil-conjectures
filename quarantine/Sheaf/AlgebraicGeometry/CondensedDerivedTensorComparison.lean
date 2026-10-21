/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # The canonical derived finite coefficient tensor comparison

This construction is the comparison already used by the two-colimit cocone, placed
below that cocone so coefficient complex presentations can state its naturality.
The functor and Hom-equivalence names cache the derived constructions, avoiding
repeated elaboration of their resolution and localization data.
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The total derived extension between two finite coefficient fields.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
@[reducible]
noncomputable def finiteCoefficientDerivedExtension {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :=
  (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctor

/-- The total derived extension to the specified condensed algebraic closure.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
@[reducible]
noncomputable def finiteCoefficientDerivedToAlgCl (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) :=
  (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).leftDerivedFunctor

/-- The exact derived restriction between finite coefficient fields.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
noncomputable def finiteCoefficientDerivedRestriction {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
  (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory

/-- The exact derived restriction from the condensed algebraic closure.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
noncomputable def finiteCoefficientDerivedFromAlgCl (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
  (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory

/-- The canonical derived finite extension/restriction adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
noncomputable def finiteCoefficientDerivedAdjunction {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    finiteCoefficientDerivedExtension X ℓ h ⊣ finiteCoefficientDerivedRestriction X ℓ h :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h)

/-- The canonical derived algebraic-closure extension/restriction adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
noncomputable def finiteCoefficientDerivedAlgClAdjunction (E : FiniteIntermediateField ℓ) :
    finiteCoefficientDerivedToAlgCl X ℓ E ⊣ finiteCoefficientDerivedFromAlgCl X ℓ E :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E)

/-- The Hom equivalence of the finite coefficient derived adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
noncomputable def finiteCoefficientDerivedHomEquiv {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F))) :
    ((finiteCoefficientDerivedExtension X ℓ h).obj K ⟶ L) ≃
      (K ⟶ (finiteCoefficientDerivedRestriction X ℓ h).obj L) :=
  (finiteCoefficientDerivedAdjunction X ℓ h).homEquiv K L

/-- The Hom equivalence of the algebraic-closure derived adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison) -/
noncomputable def finiteCoefficientDerivedAlgClHomEquiv (E : FiniteIntermediateField ℓ)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))) :
    ((finiteCoefficientDerivedToAlgCl X ℓ E).obj K ⟶ L) ≃
      (K ⟶ (finiteCoefficientDerivedFromAlgCl X ℓ E).obj L) :=
  (finiteCoefficientDerivedAlgClAdjunction X ℓ E).homEquiv K L

/-- Canonical tensor transitivity from a finite coefficient field through a larger
finite field to the algebraic closure.
Source: upstream ModuleObject/Colimit/TwoColimit.lean, ExtendScalars.
(blueprint: def-weil-pbc-finite-derived-tensor-comparison)
This is the existing exact-derived composite comparison followed by the derivation
of the underived tensor multiplication isomorphism and equality of coefficient maps. -/
noncomputable def finiteCoefficientDerivedTensorCompIso
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) :
    finiteCoefficientDerivedExtension X ℓ h ⋙ finiteCoefficientDerivedToAlgCl X ℓ F ≅
      finiteCoefficientDerivedToAlgCl X ℓ E :=
  haveI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h ≫
      padicSubfieldRingObjToPadicAlgCl X ℓ F)) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h)).symm
  (Functor.leftDerivedFunctorCompIso _ _).symm ≪≫
    Functor.leftDerivedFunctorNatIso _
      ((Mod.extendScalarsComp _ _).symm ≪≫
        Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))


end AlgebraicGeometry.ProEtale
