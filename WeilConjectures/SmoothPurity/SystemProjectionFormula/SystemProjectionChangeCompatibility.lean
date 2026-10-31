/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaMaps
import WeilConjectures.SixFunctors.IntegralSystemRealization.ProjectionSystemCoherence
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.SystemProperOpenSupport

/-! # Projection compatibility with graph refinements

Source: Stacks 0F7B, 0F7J and 0B56; the strict-system projection calculation.
(blueprint: lem-pur-system-projection-change-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.SystemProjectionFormula

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverseOnDomain_eq {C : Type*} [Category C] [HasZeroMorphisms C]
    {K M : C} (b : K ⟶ M) [IsIso b] : inverseOnDomain b = inv b := by
  simp only [inverseOnDomain, dif_pos (inferInstance : IsIso b)]

section Geometry
variable (D : FiniteFieldDatum.{u})
  (o : Operations l E) (z : Realizations l E D o)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [QuasiCompact g]

-- Keep the original geometric interface, although the proof works more generally.
set_option linter.unusedSectionVars false in
include D overX overY sepX sepY ftX qcX ftY qcY overF sepF ftF in
end Geometry
end WeilConjectures.SystemProjectionFormula
