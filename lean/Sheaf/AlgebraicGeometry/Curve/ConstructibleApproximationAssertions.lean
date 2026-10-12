/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-! # Constructible approximation for the eight assertions

Source: Stacks Project, Theorem 59.83.10 (03SC), first proof paragraph,
and Lemma 59.73.2 (03SA).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- On a fixed curve, assertions for all constructible Λ-module sheaves imply assertions
for every torsion Λ-module sheaf, provided Λ is finite.
Source: Stacks Project, Theorem 59.83.10 (03SC), first proof paragraph; Lemma 03SA.
(blueprint: lem-weil-pbc-constructible-approximation-assertions)

Proof: By 03SA(3), write F as a filtered colimit of constructible Λ-module sheaves.
Replace each stage by its image in F. The kernel of its map to F is a subsheaf of
a constructible sheaf on the Noetherian curve, hence constructible over the finite
(and thus Noetherian) ring Λ. Its cokernel, the image, is therefore constructible.
These images form a filtered union equal to F: every local section of F locally
comes from a stage. Thus we may use constructible Λ-submodule sheaves of F.
Forgetting scalars preserves this filtered colimit, as does inverse image.
Cohomology on the curve and its field extensions commutes with these filtered colimits
(03Q5; equivalently the Ext-to-derived comparison followed by derived continuity).
Vanishing C1,C2 is inherited from the constructible stages. If F is p-primary,
its subsheaves are p-primary, giving C3. If F has invertible torsion orders, so do
its subsheaves; naturality identifies its comparison map with the colimit of the
bijective stagewise maps, giving C6. The same argument without the order condition
and with properness gives C7. For C8, each class on the open comes from a stage;
lift it there by C8 and map the lift into H2(X,F). For C4,C5 the conclusion is
conditional on F itself being constructible, so use H on F directly: finiteness
is not inferred from a filtered colimit of finite groups. The filtered system
includes the zero subsheaf, so the empty scheme and zero sheaf cause no exception. -/
theorem IsCurve.assertions_of_constructible_approximation
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (H : ∀ (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions Λ f G)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionSheaf F] :
    IsCurve.Assertions Λ f F := by
  sorry

end AlgebraicGeometry
