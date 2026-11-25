/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits

/-!
# Exact products of pro-etale module sheaves
-/

@[expose] public section

set_option autoImplicit false

universe t u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every set-indexed product functor on modules over a pro-etale ring sheaf is exact.
The module universe contains the site and the indexing set. -/
theorem products_exact (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u w (t + 1)}) (I : Type w) :
    HasExactLimitsOfShape (Discrete I) (SheafOfModules.{max u w (t + 1)} R) := by
  classical
  let C := SheafOfModules.{max u w (t + 1)} R
  let L := Limits.lim (J := Discrete I) (C := C)
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryProducts L
  have : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  refine ⟨?_⟩
  suffices h : ∀ S : ShortComplex (Discrete I ⥤ C), S.Exact → (S.map L).Exact by
    have hL : Limits.PreservesFiniteLimits L ∧ Limits.PreservesFiniteColimits L :=
      ((Functor.exact_tfae L).out 2 4).mp h
    exact hL.2
  intro S hS
  apply ((sections_conservative X R).1 _ _ _ _ _ _).mpr
  intro W hWa hW
  let : IsAffine W.left := hWa
  let E := SheafOfModules.evaluation.{max u w (t + 1)} R (Opposite.op W)
  have hE := peSectionsLimitsColimits.{t, max u w (t + 1), 0, 0, 0} R W hW
  let : Limits.PreservesFiniteLimits E := ⟨fun _ _ _ ↦ inferInstance⟩
  let : Limits.PreservesColimitsOfSize.{0, 0} E := hE.2
  let : Limits.PreservesFiniteColimits E := inferInstance
  let F := (Functor.whiskeringRight (Discrete I) C _).obj E
  have hSF : (S.map F).Exact := hS.map F
  have : HasExactLimitsOfShape (Discrete (ULift.{max u w (t + 1)} I))
      (ModuleCat.{max u w (t + 1)} (R.obj.obj (Opposite.op W))) := inferInstance
  have : HasExactLimitsOfShape (Discrete I)
      (ModuleCat.{max u w (t + 1)} (R.obj.obj (Opposite.op W))) :=
    HasExactLimitsOfShape.of_domain_equivalence _ (Discrete.equivalence Equiv.ulift)
  have hprod : ((S.map F).map Limits.lim).Exact := hSF.map Limits.lim
  exact (ShortComplex.exact_iff_of_iso
    (S.mapNatIso (preservesLimitNatIso E))).mpr hprod

end AlgebraicGeometry.Scheme.ProEt
