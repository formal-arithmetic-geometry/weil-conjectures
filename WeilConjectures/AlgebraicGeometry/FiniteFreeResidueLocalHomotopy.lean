/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

public import Mathlib.Algebra.Homology.Homotopy

import WeilConjectures.AlgebraicGeometry.FiniteFreeResidueStalkHomotopy
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkHomotopySpread

/-! # Local homotopy normal form after pullback at a good residue point
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Local homotopy normal form after pullback at a good residue point. -/
theorem exists_restrict_homotopyEquiv_single_of_residue
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) {Y' : Scheme.{u}} (g : Y' ⟶ Y) (z : Y')
    (hz : (∀ q : ℕ, q ≠ i → IsZero
        ((((Modules.pullback (Y.fromSpecResidueField (g.base z))).mapHomologicalComplex _).obj
          P).homology q)) ∧
      ((((Modules.pullback (Y.fromSpecResidueField (g.base z))).mapHomologicalComplex _).obj
        P).homology i).IsFiniteLocallyFreeOfRank r) :
    ∃ U : Y'.Opens, z ∈ U ∧ Nonempty (HomotopyEquiv
      (((restrictFunctor U.ι).mapHomologicalComplex _).obj
        (((Modules.pullback g).mapHomologicalComplex _).obj P))
      ((CochainComplex.singleFunctor U.toScheme.Modules (i : ℤ)).obj
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))) := by
  obtain ⟨V, hzV, ⟨e⟩⟩ := exists_restrict_homotopyEquiv_single_of_stalk
    P d hge hle hfree (i : ℤ) r (g.base z)
    (nonempty_stalk_homotopyEquiv_single_of_residue P d hge hle hfree i r (g.base z) hz)
  let U : Y'.Opens := g ⁻¹ᵁ V
  let f : U.toScheme ⟶ V.toScheme := g ∣_ V
  let baseChange : Modules.pullback g ⋙ restrictFunctor U.ι ≅
      restrictFunctor V.ι ⋙ Modules.pullback f :=
    Functor.isoWhiskerLeft _ (restrictFunctorIsoPullback U.ι) ≪≫
      Modules.pullbackComp U.ι g ≪≫
      Modules.pullbackCongr (morphismRestrict_ι g V).symm ≪≫
      (Modules.pullbackComp f V.ι).symm ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoPullback V.ι).symm _
  let eP := (NatIso.mapHomologicalComplex baseChange (ComplexShape.up ℤ)).app P
  let F := restrictFunctor V.ι ⋙ Modules.pullback f
  let eQ := (HomologicalComplex.singleMapHomologicalComplex F
    (ComplexShape.up ℤ) (i : ℤ)).app
      (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ≪≫
    (CochainComplex.singleFunctor U.toScheme.Modules (i : ℤ)).mapIso
      ((Modules.pullback f).mapIso (restrictFreeIso V.ι (ULift.{u} (Fin r))) ≪≫
        pullbackFreeIso f (ULift.{u} (Fin r)))
  refine ⟨U, hzV, ?_⟩
  exact ⟨(HomotopyEquiv.ofIso eP).trans
    (((Modules.pullback f).mapHomotopyEquiv e).trans (HomotopyEquiv.ofIso eQ))⟩

end AlgebraicGeometry.Scheme.Modules
