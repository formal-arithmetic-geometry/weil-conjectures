/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.DominantIntegralCurveQuasiFinite

/-!
# Proper birational morphisms of integral curves are finite

Source: Stacks Project, Varieties, Tags 0AB6 and 0AB7, and More on Morphisms, Tag 02LS
(blueprint: lem-trf-proper-birational-curve-finite).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A proper dominant morphism of integral curves inducing an isomorphism of function
fields is finite. Source: Stacks Project, Varieties, Tags 0AB6 and 0AB7, and More on
Morphisms, Tag 02LS (blueprint: lem-trf-proper-birational-curve-finite).

The birational hypothesis uses the actual stalk map of `p` at the generic point of `E`.
Dominance identifies its source with the generic stalk of `C`, namely `k(C)`, and its
codomain is `E.functionField = k(E)`. Bijectivity says this ring map is an isomorphism.

Proof:
1. By `lem-weil-pbc-finite-type-over-noetherian`, finite type over the spectrum of the
   field makes `C` Noetherian. Its dimension is one, so every local ring of `C` is
   Noetherian of dimension at most one. Properness gives local finite type of `p`.
   Dominance sends the generic point of `E` to that of `C`, and the function-field
   isomorphism is a finite generic extension. Tag 0AB6, condition (1), therefore gives
   quasi-finiteness at every point of `E`, as in `lem-trf-birational-curve-quasifinite`.
2. This is local quasi-finiteness in `pqf-def-quasifinite`. Together with properness,
   `pqf-lem-proper-lqf-finite`, namely `IsFinite.of_isProper_of_locallyQuasiFinite`
   (Tag 02LS), gives `IsFinite p`. Equivalently, Tag 0AB7 supplies finite neighbourhoods
   of every target point, and finiteness is local on the target. -/
theorem isFinite_of_isProper_birational_curve
    {k : Type u} [Field k] {C E : Scheme.{u}}
    [C.Over (Spec (.of k))] [E.Over (Spec (.of k))]
    [IsIntegral C] [IsIntegral E]
    [IsSeparated (C ↘ Spec (.of k))] [IsSeparated (E ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))] [QuasiCompact (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (E ↘ Spec (.of k))] [QuasiCompact (E ↘ Spec (.of k))]
    (hdimC : topologicalKrullDim C = 1) (hdimE : topologicalKrullDim E = 1)
    (p : E ⟶ C) [p.IsOver (Spec (.of k))] [IsProper p] [IsDominant p]
    (hbirational : Function.Bijective (p.stalkMap (genericPoint E) :
      C.presheaf.stalk (p (genericPoint E)) ⟶ E.functionField)) : IsFinite p := by
  sorry

end AlgebraicGeometry
