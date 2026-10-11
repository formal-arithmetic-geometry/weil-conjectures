/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.Paper.PQFCohomology
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Cohomology along an affine morphism

Source: Stacks Project, Cohomology of Schemes, Lemma 089W and Lemma 01XC;
Cohomology, Lemma 01F4 and Equation 01FA
(blueprint: lem-weil-pbc-affine-morphism-cohomology-edge).
-/

universe v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- For an affine morphism, higher direct images of a quasi-coherent module vanish and
cohomology is carried isomorphically by the edge map.
Source: Stacks Project, Cohomology of Schemes, Lemma 089W and Lemma 01XC;
Cohomology, Lemma 01F4 and Equation 01FA
(blueprint: lem-weil-pbc-affine-morphism-cohomology-edge).

Proof:
1. By lem-pc-affine-morphism-hi (Stacks 01XC), higher direct images vanish: on
an affine open V of S, its inverse image is affine, so positive quasi-coherent
cohomology vanishes; affine opens form a basis.
2. Choose an injective resolution F → I. By pqf-def-cohomology and step 1,
h_*F → h_*I is exact. Its terms are Γ(S,-)-acyclic by
lem-weil-pbc-module-pushforward-injective-acyclic.
3. Choose an injective resolution s : h_*F → J. By
lem-weil-pbc-lift-along-injective-quasi-iso, lift s to γ : h_*I → J over h_*F.
It is a quasi-isomorphism. By lemma-weil-pbc-leray-acyclicity, Γ(S,γ) induces
an isomorphism in every nonnegative degree.
4. In def-weil-pbc-module-cohomology-fmap take the h-map id, the resolutions
I and J, the third resolution J, λ = γ and β = id. By
lem-weil-pbc-module-cohomology-fmap-functorial the choices do not affect the map.
The edge map is H(Γ(S,γ)) inverse, using Γ(S,h_*I) = Γ(X,I), so is invertible.
All maps are O_S(S)-linear; the action on H(X,F) is through h.appTop.
-/
theorem affine_morphism_cohomology_edge
    {X S : Scheme.{v}} (h : X ⟶ S) [IsAffineHom h]
    (F : X.Modules) [F.IsQuasicoherent] :
    (∀ (p : ℕ), 0 < p →
      IsZero (((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).rightDerived p).obj F)) ∧
      (∀ (p : ℕ), IsIso (moduleCohomologyEdgeMap h F p) ∧
        ∀ (r : Γ(S, ⊤))
          (x : (RingedSpace.moduleCohomology S.toRingedSpace p).obj
            ((pushforward h).obj F)),
          moduleCohomologyEdgeMap h F p (r • x) =
            h.appTop r •
              @id ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
                (moduleCohomologyEdgeMap h F p x)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
