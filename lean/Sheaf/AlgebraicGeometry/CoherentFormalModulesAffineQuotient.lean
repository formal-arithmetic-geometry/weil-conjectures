/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # CoherentFormalModulesAffineQuotient

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Quotient systems of finite completed modules satisfy the coherent formal conditions.
Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof reduction to module
systems; Algebra 05GG (completion modulo an ideal power), and Schemes 01I7/01IB.
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-quotient).

Proof: Write B for the completion. Since A is Noetherian, I is finitely generated and
B/I^(n+1)B = A/I^(n+1). For finite B-module N, reducing a finite generating family
shows N/I^(n+1)N is finite over A/I^(n+1), hence over A. Affine tilde is exact and
identifies ideal products and their cokernels with module ideal products and quotients.
Consequently the nth sheaf in the displayed completion is canonically tilde of this
finite A-module. It is quasi-coherent of finite type, hence coherent on Spec A.
Multiplication by I^(n+1) on this quotient is zero, giving the annihilation condition.
For successive levels, quotienting N/I^(n+2)N by I^(n+1) gives N/I^(n+1)N because
I^(n+2)N is contained in I^(n+1)N. Applying tilde and the cokernel comparison gives
the required quotient isomorphism. Its composite with the projection is the canonical
reduction map, which is exactly formalCompletionFunctor's transition. These are the
three clauses of IsCoherentFormalModule. -/
theorem coherentFormalModules_affine_quotient_coherent
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (N : ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N)) :
    IsCoherentFormalModule J ((ObjectProperty.ι
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A)) ⋙
      tilde.functor (CommRingCat.of A) ⋙ formalCompletionFunctor J).obj N) := by
  sorry

/-- The canonical quotient functor, lifted to coherent formal systems.
Its objects and maps are the existing sheaf quotient construction; only the proof of
membership in the full subcategory uses the preceding theorem.
Source: Stacks Project, Lemma 087W (blueprint:
lem-weil-pbc-coherent-formal-modules-affine-quotient). -/
noncomputable def coherentFormalModules_affine_quotientFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) :
    ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⥤
      CoherentFormalModule (Spec (CommRingCat.of A)) J :=
  (IsCoherentFormalModule J).lift
    (ObjectProperty.ι
        (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A)) ⋙
      tilde.functor (CommRingCat.of A) ⋙ formalCompletionFunctor J)
    (coherentFormalModules_affine_quotient_coherent A I J hJ)

end AlgebraicGeometry
