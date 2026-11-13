/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonConstruction
import WeilConjectures.AlgebraicGeometry.KoszulCechComparisonIsIso
import WeilConjectures.AlgebraicGeometry.PrincipalCechResolutionQuasiIso

/-! # Koszul Hom colimits compute derived sections on a principal-open union

Source: Stacks Project, Tags 08D1 and 08D2.
-/

@[expose] public section

universe uT wT vT

open CategoryTheory

namespace AlgebraicGeometry

/-- For an unbounded complex of quasi-coherent modules on Spec(A), the canonical
Koszul-to-alternating-Čech map followed by the Čech-to-derived-sections map is an
isomorphism in D(A), equivalently a quasi-isomorphism of its complex representatives.
The positive exponent e is indexed by e-1 in the natural-number diagram
(Stacks, Tags 08D1 and 08D2). -/
theorem affine_koszul_cech_derived_comparison
    (A : Type uT) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{wT}
      (SheafOfModules.{uT} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{vT} (ModuleCat.{uT} A)]
    (F : CochainComplex
      (SheafOfModules.{uT} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (e : DerivedCategory.Q.obj F ≅ E.obj) :
    IsIso (koszulCechDerivedComparison A r f F ≫
      (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map e.hom) := by
  have : IsIso (koszulCechComparison A r f F) :=
    koszulCechComparison_isIso A r f F hF
  obtain ⟨J, hJ, i, _, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective F
  let _ := hJ
  let _ := hi
  have : QuasiIso ((principalCechFunctor r f).map i) :=
    principalCech_resolution_quasiIso A r f F J hF i
  have : QuasiIso ((principalCechAugmentation r f).app J) :=
    principalCechAugmentation_quasiIso r f J
  have hβ := (principalCechDerivedComparison_exists r f F).choose_spec J i
  have : IsIso (principalCechDerivedComparison r f F ≫
      (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map
        (DerivedCategory.Q.map i) ≫
      ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctorObjQIso J).hom ≫
      DerivedCategory.Q.map ((principalCechAugmentation r f).app J)) := by
    dsimp only [koszulOpen, principalCechDerivedComparison]
    rw [hβ]
    infer_instance
  have : IsIso (principalCechDerivedComparison r f F) :=
    IsIso.of_isIso_comp_right _
      ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor.map
          (DerivedCategory.Q.map i) ≫
        ((affineOpenSections A (koszulOpen A r f)).rightDerivedFunctorObjQIso J).hom ≫
        DerivedCategory.Q.map ((principalCechAugmentation r f).app J))
  dsimp only [koszulCechDerivedComparison]
  infer_instance

end AlgebraicGeometry
