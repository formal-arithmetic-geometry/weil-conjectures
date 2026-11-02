/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.DeligneLaumon.FrobeniusCohomologyTransportIso
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.DeligneLaumon.CondensedClopenCompact.CondensedClopenCompactDecomposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Native condensed global Frobenius for proper schemes

Source: latest blueprint, def-weil-global-geometric-frobenius, its two displayed
composites (blueprint: def-weil-global-geometric-frobenius).

The compact operator is the specified transport followed by the Weil map.
The proper comparison occurs only in germ evaluation.
The ordinary operator uses the same published transport interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedGlobalProper

/-- The ordinary displayed composite, using the recorded t before applying RΓ(theta).
Source: the ordinary global operator (blueprint: def-weil-global-geometric-frobenius). -/
def ordinary (l : ℕ) [Fact l.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) [QuasiCompact a]
    (g : Y ⟶ Y) [IsIso g] (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (w : g ≫ a = a ≫ h) (K : CondensedRing.CohomologyTransport.D
      (Profinite.padicAlgClRingObj l) Y)
    (theta : (CondensedRing.CohomologyTransport.L
      (Profinite.padicAlgClRingObj l) g).obj K ≅ K) :=
  CondensedRing.CohomologyTransport.t (Profinite.padicAlgClRingObj l) a a h g w K ≫
    (CondensedRing.CohomologyTransport.Γ (Profinite.padicAlgClRingObj l)
      (Spec (.of k))).map
        ((CondensedRing.CohomologyTransport.R (Profinite.padicAlgClRingObj l) a).map
          theta.hom)

end WeilConjectures.CondensedGlobalProper
