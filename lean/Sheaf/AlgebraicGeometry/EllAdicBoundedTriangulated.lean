/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Triangulated closure for the ell-adic finiteness coefficient class

The field cases use local finite freeness. The integral cases use the integral Serre
criterion. These are exactly the heart-closure inputs in the last step of blueprint
`lem-sfb-dc-tensor-preserves`.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

/-- The bounded constructible module-object category is triangulated for every ell-adic
finiteness coefficient. Field presentations become locally free, so the constructible
heart is Serre; the integral cases are the integral constructible Serre theorem. Applying
homology to distinguished triangles gives triangulated closure.
Source: Bhatt--Scholze, Proposition 6.8.11(1),(3), and the heart-closure inputs in
`lem-sfb-dc-tensor-preserves`, step 10.
(blueprint: lem-sfb-dc-ell-adic-triangulated) -/
theorem isTriangulated_boundedConstructible_ellAdic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {ℓ : ℕ} [h : IsEllAdicFinitenessCoefficient ℓ Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible (condensedRingObj Λ X)).IsTriangulated := by
  cases h with
  | continuous E =>
    exact isTriangulated_boundedConstructible (ℓ := ℓ) _ X
  | integral E =>
    exact isTriangulated_boundedConstructible (ℓ := ℓ) _ X
  | algebraicClosure =>
    exact isTriangulated_boundedConstructible (ℓ := ℓ) _ X
  | unitBall E O hO =>
    let : IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj O) := .unitBall E O hO
    exact isTriangulated_boundedConstructible (ℓ := ℓ) _ X

end CondensedRing
end AlgebraicGeometry.ProEtale
