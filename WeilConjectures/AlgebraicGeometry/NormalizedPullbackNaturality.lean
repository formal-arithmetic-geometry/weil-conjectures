/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedPullbackObjects

/-! # Objectwise normalized pullback of geometric fibres

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Remark 6.8.15;
Stacks Tag 03Q1(3) (blueprint: lem-per-normalized-pullback-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- Objectwise normalized comparisons are natural in heart morphisms.
Source: BS 6.8.4(4),(6), Remark 6.8.15; Stacks 03Q1(3).
(blueprint: lem-per-normalized-pullback-naturality).

Proof: choose a common adapted stratification for F and G and a pointed affine etale
refinement of their lattice charts. Full faithfulness of raw lattice rationalization
represents the restricted arrow by an integral lattice map divided by a uniformizer power.
Naturality of the finite inverse-image stalk comparison commutes with that integral map
at every positive reduction level. Apply the inverse-limit projections, then rationalize.
Both sides acquire the same inverse uniformizer scalar by the fractions equation of ω.
If two fractions represent the same arrow, a uniformizer power kills their cleared
difference; after rationalization this power is invertible, so their fibre maps agree.
The local_normalization clause of p identifies these computations with its components.
Changing lattices or charts conjugates both sides by the same intrinsic fibre comparisons,
so the equality descends from the common refinement to F and G. No integral Hom
cancellation or torsion-freeness is required. -/
theorem objectwise_normalized_pullback_naturality
    (ω : Fibres (k := k) l R) (p : ObjectwiseNormalizedPullback l R ω)
    (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : FiniteTypeBase k} (g : Y.scheme ⟶ X.scheme)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)
    {F G : NormalizedFibre.Heart l A (base l X)} (f : F ⟶ G) :
    ((ω A Y).point κ y).functor.map ((heartPull l A R g).map f) ≫
        (p.component A g κ y G).hom =
      (p.component A g κ y F).hom ≫ ((ω A X).point κ (y ≫ g)).functor.map f := by sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
