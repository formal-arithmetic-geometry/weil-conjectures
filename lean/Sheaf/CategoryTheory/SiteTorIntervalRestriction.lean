/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.Paper.WeilTensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

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
1. The module category is Grothendieck abelian
   (`lem-pur-ringed-site-grothendieck-abelian`), with additive symmetric closed tensor
   (`lem-pc-sheaf-modules-tensor-closed`). Apply functorial bounded-above flat replacement
   (`lem-pc-kflat-bounded-flat-replacement`) to degree-zero complexes. Evaluation in degree
   zero gives natural flat epimorphisms; iterating on kernels gives functorial flat resolutions.
2. The comparisons and uniqueness in `lem-weil-pbc-site-derived-tensor-descent` identify
   this tensor with the categorical K-flat tensor. Apply
   `lem-sc-source-tor-amplitude-flat-model` to obtain a flat complex P supported in [a,b]
   and an isomorphism Q(P) ≅ E.
3. Exact slice restriction (`lem-pur-site-restriction-module-adjunction-exact`) preserves
   quasi-isomorphisms and the representing isomorphism, giving Q(P|U) ≅ E|U for the recorded
   `def-weil-pbc-ringed-site-derived-restriction`.
4. Each restricted term is flat (`lem-weil-pbc-slice-restriction-flat`); zero terms remain
   zero, so P|U is supported in [a,b]. It is K-flat by
   `lem-pc-bounded-above-flat-kflat-site`. The slice remains small in the same universe.
5. For an arbitrary slice module G, choose a flat-term K-flat resolution T → G[0]
   (`lem-pc-kflat-resolution`). Its cone is acyclic (`lem-pur-quasi-iso-cone-acyclic`).
   K-flatness of P|U and the signed tensor symmetry make tensor with this cone acyclic.
   The tensor-cone comparison (`lem-pc-tensor-mapping-cone-iso`) and the cone criterion show
   Tot(P|U ⊗ T) → Tot(P|U ⊗ G[0]) is a quasi-isomorphism.
6. The representative comparison of `lem-weil-pbc-site-derived-tensor-descent` now identifies
   E|U ⊗ᴸ G with Q(Tot(P|U ⊗ G[0])). This uses no extension of G to a global sheaf.
7. The last ordinary tensor has degree-r term (P|U)^r ⊗ G, zero outside [a,b]. Its cohomology
   therefore vanishes there (`def-pc-tensor-complex-sheaves`, additive tensor, and
   `def-weil-derived-cohomology-sheaves`). Transport vanishing through the isomorphism.
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
  sorry

end CategoryTheory
