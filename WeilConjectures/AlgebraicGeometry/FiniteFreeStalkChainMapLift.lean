/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkChainMapLiftLocal
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkChainMapLiftRestrict

/-! # Local extension of one map between bounded finite free complexes
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- One prescribed stalk chain map extends, using the canonical comparison, to every
sufficiently small neighbourhood. -/
theorem exists_restrict_chainMap_of_stalk_eventually
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y)
    (f : ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P ⟶
      ((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q) :
    ∃ (U : Y.Opens), y ∈ U ∧ ∀ (V : Y.Opens) (hyV : y ∈ V), V ≤ U →
      let R := (restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)
      let S := (Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let eP := (stalkRestrictionComplexIso V y hyV).app P
      let eQ := (stalkRestrictionComplexIso V y hyV).app Q
      ∃ (fV : R.obj P ⟶ R.obj Q), S.map fV = eP.hom ≫ f ≫ eQ.inv := by
  obtain ⟨U, hyU, fU, hU⟩ := exists_chainMap_of_stalk_local
    P Q a b c e hPa hPb hQc hQe hPfree hQfree y f
  exact ⟨U, hyU, restrict_chainMap_of_stalk_local P Q y U hyU f fU hU⟩

end AlgebraicGeometry.Scheme.Modules
