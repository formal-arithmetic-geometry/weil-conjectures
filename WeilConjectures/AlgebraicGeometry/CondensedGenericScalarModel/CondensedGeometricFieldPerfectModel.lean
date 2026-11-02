/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericScalarModel.CondensedGenericScalarModelData

/-! # Perfect scalar models at geometric points

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Lemma 4.1(2) and Theorem 4.13.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGenericScalarModel

/-- Dualizable complexes at a geometric point are perfect scalar realizations.

Source: HRS Lemma 4.1(2), Theorem 4.13, first paragraph
(blueprint: lem-zl-condensed-geometric-field-perfect-model).

Proof: the geometric-field profinite-site equivalence identifies the specified point
inverse image with an exact symmetric monoidal equivalence on coefficient modules.
Pass termwise to ordinary unbounded derived categories. The singleton profinite set
is extremally disconnected. Contractible lisse evaluation there identifies dualizable
complexes with perfect complexes over its coefficient section ring. That ring is
R = Gamma(*, Lambda), by the terminal-section comparison, including multiplication
and unit. Transport a bounded finite-projective representative along this ring
isomorphism to obtain P. The scalar compatibility of evaluation identifies its
realization with the original complex. This includes the zero ring and zero complex. -/
theorem geometric_field_perfect_model
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
        (condensedRingObj Λ.X (Spec (.of Ω)))))
    (hN : Nonempty (HasRightDual N)) :
    ∃ P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)),
      DerivedCategory.IsPerfectRingComplex P ∧
      Nonempty (N ≅ (condensedScalarRealization Λ.X (Spec (.of Ω))).obj P) := by sorry

end AlgebraicGeometry.ProEtale.CondensedGenericScalarModel
