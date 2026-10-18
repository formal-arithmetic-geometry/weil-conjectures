/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionNorm3

/-!
# Degree zero coefficient term map

Source: Stacks Project, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-term-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
/-- Degree-zero term map.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-term-map). -/
abbrev primeTensorTermMap (φ : A →+* B) (V : Scheme.{u})
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))
    (q : M ⟶ (Sheaf.restrictScalars V.smallEtaleTopology φ).obj N) :
    primeSingleComplex A V M ⟶ primeRestrictedComplex φ V (primeSingleComplex B V N) :=
  (CochainComplex.singleFunctor _ 0).map q ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (Sheaf.restrictScalars V.smallEtaleTopology φ) (.up ℤ) 0).inv.app N

end AlgebraicGeometry.Etale
