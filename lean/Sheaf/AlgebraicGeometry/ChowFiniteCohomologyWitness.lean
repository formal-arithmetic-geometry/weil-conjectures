/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Sheaf.AlgebraicGeometry.ChowRelativeAmple
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism

/-! # A Chow module with finite cohomology and generic rank one

Source: Stacks Project, Proposition 30.19.1, Tag 02O5, Chow construction.
(blueprint: lem-pc-v3-chow-finite-cohomology-witness)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The Chow construction supplies one coherent module with finite cohomology on each
integral closed support, with its generic stalk the one-dimensional residue-field module.

Source: Stacks Project, Proposition 30.19.1, Tag 02O5, the construction following the
short exact sequence argument, label `proposition-proper-pushforward-coherent`.
(blueprint: lem-pc-v3-chow-finite-cohomology-witness)

Proof: The proper source and its closed subscheme W are Noetherian. Apply Chow's lemma
 to W over T, obtaining a projective modification π : W' → W that is an isomorphism over
 a dense open. The projective embedding gives an invertible module L relatively ample
 for both π and W' → T. Choose a common power killing both positive higher direct images,
 and put G = i_* π_* L^n. Projective-space cohomology finiteness on affine opens of W
 proves coherence of π_* L^n; use this independent projective argument, not the general
 proper coherence theorem. Closed pushforward preserves coherence. The Leray comparison
 and affine-base cohomology identify H^q(G) with H^q(W', L^n), which is finite by the
 projective-space theorem, with scalars induced by f.appTop. On the dense open π is an
 isomorphism, so the generic stalk is a line over the function field of W. Closed
 immersion identifies this field with the residue field at i(η); the scalar action is
 the quotient action and the maximal ideal annihilates it. The support is contained
 in i(W) by closed pushforward and contains its generic point. Coherence makes it closed,
 so it equals i(W). No ideal on W or induction hypothesis is needed for this module. -/
theorem exists_chow_finite_cohomology_witness {X T : Scheme.{u}}
    (f : X ⟶ T) [IsProper f] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (W : Scheme.{u}) (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W] :
    ∃ G : X.Modules, RingedSpace.IsCoherent X.toRingedSpace G ∧
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint W))),
        ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G, a • v = 0) ∧
      (∃ inst : Module (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
        (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
          (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
            (i.base (genericPoint W))).obj G),
          a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
        Module.finrank (X.residueField (i.base (genericPoint W)))
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G)
          = 1) ∧
      (∀ q : ℕ,
        letI : Module Γ(T, ⊤) (G.H q) := Module.compHom _ f.appTop.hom
        Module.Finite Γ(T, ⊤) (G.H q)) := by sorry

end AlgebraicGeometry.Scheme.Modules
