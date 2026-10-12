/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso

/-! # Compatibility of stalk comparison with a second open restriction

Source: lem-pc-finite-free-stalk-degreewise-shrink, step 3, expanding
lem-pc-perfect-locus's finite matrix calculation.
(blueprint: lem-pc-stalk-restriction-subopen-compatibility)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk of the restriction of a component map is its original stalk conjugated
by the canonical comparisons. No chain equations or finiteness are required.

Source: lem-pc-finite-free-stalk-degreewise-shrink, step 3, and the comparison
calculation in lem-pc-finite-free-stalk-chain-map-lift-restrict.

Proof: Write j for V -> U and C for the comparison of restriction to V with
restriction first to U and then along j. Replace restrictions by pullbacks using
restrictFunctorIsoPullback. The equality V.fromSpecStalkOfMem >> j =
U.fromSpecStalkOfMem follows by cancelling the open inclusion U -> Y and using
fromSpecStalkOfMem_ι twice. Pullback composition gives a comparison D between
restriction along j followed by stalk pullback and stalk pullback through U.
The associativity law for pullback composition identifies the composite of the
stalk pullback of C with D with E_V followed by E_U inverse. The compatibility
of restriction-to-pullback comparisons with composition follows from their
adjunction units (equivalently uniqueness of left adjoints to the common
pushforward). Apply naturality of D to f and cancel inverse/hom pairs. Taking
the n-th component gives the displayed equation. This also covers U = V,
zero objects, and arbitrary maps between the indicated terms.
(blueprint: lem-pc-stalk-restriction-subopen-compatibility) -/
theorem stalkRestrictionComplexIso_map_subopen
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (y : Y) (U V : Y.Opens) (hyU : y ∈ U) (hyV : y ∈ V) (hVU : V ≤ U)
    (n : ℤ)
    (f : (restrictFunctor U.ι).obj (P.X n) ⟶
      (restrictFunctor U.ι).obj (Q.X n)) :
    let C := NatIso.mapHomologicalComplex
      ((restrictFunctorCongr (Y.homOfLE_ι hVU)).symm ≪≫
        restrictFunctorComp (Y.homOfLE hVU) U.ι) (ComplexShape.up ℤ)
    (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map
      (((C.app P).hom.f n) ≫ (restrictFunctor (Y.homOfLE hVU)).map f ≫
        ((C.app Q).inv.f n)) =
      ((stalkRestrictionComplexIso V y hyV).app P).hom.f n ≫
        ((stalkRestrictionComplexIso U y hyU).app P).inv.f n ≫
        (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map f ≫
        ((stalkRestrictionComplexIso U y hyU).app Q).hom.f n ≫
        ((stalkRestrictionComplexIso V y hyV).app Q).inv.f n := by sorry

end AlgebraicGeometry.Scheme.Modules
