/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Finite cohomology of a sufficiently large Chow twist

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
construction of the module pi_* L^n.
(blueprint: lem-pc-q2-chow-twist-finite-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The analytic part of the Chow construction, for a specified projective model.
No integrality, birationality, or generic-stalk condition is required.

Source: Stacks Project, Tag 02O5, proposition-proper-pushforward-coherent,
paragraphs defining L and G and applying the relative Leray spectral sequence.
(blueprint: lem-pc-q2-chow-twist-finite-cohomology)

Proof:
1. The graph (j, pi) embeds Y as a closed subscheme of projective space over W:
   g is separated, pi is proper, and j is closed. The pullback L of the integral
   O(1) agrees with the twist from this graph. Hence L is invertible and relatively
   ample for both pi and pi followed by g. Reindex the finite coordinates by
   ULift (Fin (m+1)) when nonempty; if there are no coordinates Y is empty and
   all the asserted modules are zero.
2. Relative Serre vanishing supplies a common n killing all positive higher images
   of L^n for these two morphisms. Over each affine open of W, projective-space
   cohomology finiteness makes the sections of pi_* L^n finite. Quasi-coherent
   localization identifies its restrictions with the associated finite modules.
   W is locally Noetherian since it is proper over the affine Noetherian T, so
   pi_* L^n is coherent. This uses the projective finiteness theorem, never the
   general proper coherence theorem under construction.
3. Closed pushforward along i preserves quasi-coherence and finite presentation,
   so i_* pi_* L^n is coherent on the locally Noetherian X.
4. Leray for pi with its positive images zero, followed by the exact closed
   pushforward along i, compares its cohomology with H^q(Y,L^n). The comparison
   commutes with multiplication by global sections pulled back from T. The
   projective finiteness theorem over the affine Noetherian T makes these finite
   Gamma(T,top)-modules. Transport finiteness through these linear comparisons. -/
theorem exists_chow_twist_finite_cohomology {X W T Y : Scheme.{u}}
    (f : X ⟶ T) [IsProper f] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (i : W ⟶ X) [IsClosedImmersion i] (π : Y ⟶ W) [IsProper π]
    (N : Type u) [Finite N] (j : Y ⟶ ℙ(N; T)) [IsClosedImmersion j]
    (hj : j ≫ (ℙ(N; T) ↘ T) = π ≫ i ≫ f) :
    let L := (pullback j).obj
      ((pullback (ProjectiveSpace.toProjInt N T)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule N (ULift.{u} ℤ)) 1))
    ∃ n : ℕ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((pushforward i).obj ((pushforward π).obj (L.tensorPow n))) ∧
      (∀ q : ℕ,
        letI : Module Γ(T, ⊤)
          (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q) :=
            Module.compHom _ f.appTop.hom
        Module.Finite Γ(T, ⊤)
          (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q)) := by sorry

end AlgebraicGeometry.Scheme.Modules
