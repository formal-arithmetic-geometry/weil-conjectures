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
import Sheaf.AlgebraicGeometry.ProjectivePushforwardFiniteTypeIndependent
import Sheaf.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent
import Sheaf.AlgebraicGeometry.ProjectiveGraphTwistVanishing
import Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison
import Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

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
1. Put p = pi followed by i. The scheme X is Noetherian because it is proper
   over the affine Noetherian T. Separatedness of f gives a closed graph embedding
   of Y into projective space over X. Relative graph-twist vanishing chooses n
   killing every positive higher direct image of L.tensorPow n along p.
2. Invertibility of L makes its powers quasi-coherent and finitely presented.
   The independent projective pushforward argument gives finite type of p_* L^n:
   degree-zero projective finiteness on affine opens and quasi-coherent localization
   suffice. Quasi-coherence and the locally Noetherian finite-type criterion give
   coherence. Transport this along pushforwardComp pi i to i_* pi_* L^n.
3. The given closed embedding over T gives finite cohomology of L^n over Gamma(T,O).
   A linear Leray comparison for p, whose positive higher images vanish, identifies
   these groups with the cohomology of p_* L^n. The pushforwardComp isomorphism
   identifies the latter with that of i_* pi_* L^n. Restrict scalars along f.appTop
   and transport finite generation through the two linear equivalences. -/
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
          (((pushforward i).obj ((pushforward π).obj (L.tensorPow n))).H q)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
