module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
public import WeilConjectures.AlgebraicGeometry.FunctionField

/-! # Coherent reflexive modules of rank one

Source: Stacks Project, Divisors, Tags 0EBL and 0EBM
(blueprint: def-sfb-coherent-reflexive-rank-one).

This module owns the conjunction of coherence, invertibility of the canonical biduality
morphism, and generic rank one. It reuses the existing definitions of all three conditions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A coherent reflexive module of rank one on an integral scheme. Reflexivity refers to the
canonical evaluation morphism, and rank is the dimension of the generic stalk.
Source: Stacks Project, Divisors, Tags 0EBL and 0EBM
(blueprint: def-sfb-coherent-reflexive-rank-one). -/
def Modules.IsCoherentReflexiveRankOne {Y : Scheme.{u}} [IsIntegral Y]
    (F : Y.Modules) : Prop :=
  RingedSpace.IsCoherent Y.toRingedSpace F ∧
    IsIso (SheafOfModules.bidual (R := Y.sheaf) F) ∧ Modules.rank F = 1

end AlgebraicGeometry.Scheme
