/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! Closed-boundary restriction for the extension occurring in the proper-boundary argument. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The extension by zero from the clopen part over the open complement restricts to zero
on the closed boundary. This is the disjointness step in the proof of proper-boundary
cohomology. The proof uses the open-closed localization sequence and base change for the
closed immersion, together with the explicit intrinsic coefficient comparison.
Source: Stacks, Tags 09AH and 09BN; blueprint lem-sp-proetale-proper-boundary-cohomology.
(blueprint: lem-sp-proetale-proper-boundary-closed-restriction). -/
theorem proEtale_proper_boundary_extension_restricts_zero
    (R : Type u) [CommRing R]
    {Z E P U : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    [IsClosedImmersion z] (e : E ⟶ Spec (CommRingCat.of R))
    [IsOpenImmersion e] [QuasiCompact e]
    (hcomplement : Set.range e = (Set.range z)ᶜ)
    (p : P ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (h : U ⟶ pullback p e) [IsOpenImmersion h]
    (hclosed : IsClosed (Set.range h))
    [QuasiCompact (h ≫ pullback.fst p e)]
    (A : Type u) [CommRing A] [Finite A]
    (J : proEtaleRingModules U (proEtaleConstantRing U A)) [Injective J] :
    IsZero ((proEtaleConstantRingPullback A (pullback.snd z p)).obj
      ((sfIntrinsicExtensionByZero (h ≫ pullback.fst p e) A).obj J)) := by
  sorry

end AlgebraicGeometry.Scheme

