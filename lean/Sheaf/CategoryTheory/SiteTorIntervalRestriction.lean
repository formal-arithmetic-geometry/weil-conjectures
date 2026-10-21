/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.Paper.WeilTensorProduct
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Tor intervals survive slice restriction

Source: Stacks Project, Cohomology on Sites, Tag 08H5, specialized to slice restriction
(blueprint: lem-sf-site-tor-interval-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction to any localized ringed site preserves the same universal Tor interval.
The tensor is the existing K-flat localization tensor, and module sheaves in degree zero
are inserted by `DerivedCategory.singleFunctor`. The slice test sheaf is arbitrary.

Source: Stacks Project, Cohomology on Sites, Tags 08H5 and 08G1
(blueprint: lem-sf-site-tor-interval-restriction).

Proof:
1. Apply the ringed-site bounded flat model equivalence (Stacks 08G1) to E. It supplies
   a complex P with flat terms, zero outside [a,b], and E ≅ Q(P).
2. Let F be exact slice restriction and B its termwise application to P. The explicit
   site tensor is naturally isomorphic to monoidal tensor. Transport flatness along
   this comparison, apply `SheafOfModules.isFlat_over`, and transport back on the slice.
   Thus B has flat terms. Since F preserves zero objects, B is zero outside [a,b].
3. Exactness gives F.mapDerivedCategory and its comparison with termwise restriction.
   Apply it to E ≅ Q(P). Its comparison at Q.objPreimage E identifies the recorded
   derived restriction with Q(B), independently of the chosen representative.
4. Apply the reverse implication of the same bounded flat model equivalence on the
   slice. It tests against every slice module sheaf, as required.
-/
theorem siteTorIntervalRestriction
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{u}) (U : C)
    [hD : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))]
    [hDU : HasDerivedCategory.{w'} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (O.over U)))]
    (a b : ℤ) (_hab : a ≤ b)
    (E : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)))
    (_hE : ∀ (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))
        (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((SheafOfModules.wfSiteDerivedTensor.{u, u, w} J O).obj
          (E, (DerivedCategory.singleFunctor _ 0).obj F)))) :
    ∀ (G : ringedSiteModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (O.over U)))
        (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((SheafOfModules.wfSiteDerivedTensor.{u, u, w'} (J.over U) (O.over U)).obj
          (@ringedSiteDerivedRestrictionOfUniverses.{u, u, u, u, w, w'} C _ J
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) U
            _ _ _ _ hD hDU E,
            (DerivedCategory.singleFunctor _ 0).obj G))) := by
  classical
  let R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O
  let : HasDerivedCategory.{w'} (SheafOfModules.{u} (R.over U)) := hDU
  let F := SheafOfModules.overFunctor.{u} R U
  have : F.Additive :=
    (SheafOfModules.localizedSystemExact.{u, u, u} O U).2.2.2.1
  have : PreservesFiniteLimits F :=
    (SheafOfModules.localizedSystemExact.{u, u, u} O U).2.2.2.2.1
  have : PreservesFiniteColimits F :=
    (SheafOfModules.localizedSystemExact.{u, u, u} O U).2.2.2.2.2
  obtain ⟨P, hflat, hbound, ⟨e⟩⟩ :=
    (SheafOfModules.torAmplitude_iff_exists_bounded_flat_model J O E a b _hab).1 _hE
  let B := (F.mapHomologicalComplex (.up ℤ)).obj P
  apply (SheafOfModules.torAmplitude_iff_exists_bounded_flat_model
    (J.over U) (O.over U) _ a b _hab).2
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i
    have hf : SheafOfModules.IsFlat (R := O) (P.X i) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso O (P.X i)) (hflat i)
    have hg := SheafOfModules.isFlat_over (P.X i) U hf
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (O.over U) ((P.X i).over U)).symm hg
  · intro i hi
    exact F.map_isZero (hbound i hi)
  · change Nonempty (DerivedCategory.Q.{w'}.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.{w}.objPreimage E)) ≅
        DerivedCategory.Q.{w'}.obj B)
    let Q := DerivedCategory.Q.{w} (C := SheafOfModules.{u} R)
    let e₀ := F.mapDerivedCategory.{w, w'}.mapIso (Q.objObjPreimageIso E) ≪≫
      F.mapDerivedCategory.{w, w'}.mapIso e ≪≫ F.mapDerivedCategoryFactors.{w, w'}.app P
    exact ⟨(F.mapDerivedCategoryFactors.{w, w'}.app (Q.objPreimage E)).symm ≪≫ e₀⟩

end CategoryTheory
