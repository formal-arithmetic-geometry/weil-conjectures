/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.LinearAlgebra.Dimension.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # An ideal lattice in a rank-one generic stalk

Source: Stacks Project, Tag 01YH, `lemma-property-irreducible`, proof, the sentence
"By (3)(c) we see that r = 1."
(blueprint: lem-pc-r2-rank-one-generic-ideal-inclusion)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

-- The residue-field instance is used implicitly by finrank.
set_option linter.unusedVariables false in
/-- A coherent module whose generic stalk is a residue-field line admits a nonzero
ideal pushforward inclusion with invertible generic stalk.
Source: Stacks Project, Tag 01YH, `lemma-property-irreducible`, proof, the first
ideal inclusion and the rank-one calculation using Tag 01YE.
(blueprint: lem-pc-r2-rank-one-generic-ideal-inclusion)

Proof: Apply the generic-point ideal inclusion of Tag 01YE to the coherent module
G and its maximal-ideal-annihilated stalk. This gives a coherent ideal J, an integer
r and a monomorphism from i_*(J^{⊕ r}) to G, invertible near the generic point.
Closed-pushforward stalk comparison and commutation of stalks with finite sums
identify its source stalk with r copies of J at the generic point of W. If J or r
were zero this stalk would vanish, contrary to target dimension one. Thus J is
nonzero. On the integral scheme W a nonzero ideal has the full generic stalk field.
The surjective closed-immersion local-ring map to that field identifies it with
κ(i(genericPoint W)). The scalar compatibility in hGrank makes the generic map
linear over that residue field, so dimension additivity and target dimension one
give r = 1. Identify the one-term coproduct with J to obtain the asserted mono;
its generic stalk is invertible because the original map is locally invertible.
This is only the generic-inclusion step: it uses no second ideal, makes no global
support assumption and asserts no cokernel property. To avoid the current library's
cohomology import cycle, formalize the Tag 01YE ideal-lattice construction through
stalk-map extension, shrinking to invertibility, and clearing denominators with a
power of the complement ideal, rather than importing cohomological pushforward files. -/
theorem rank_one_generic_ideal_inclusion {X W : Scheme.{u}} [IsNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hGcoh : RingedSpace.IsCoherent X.toRingedSpace G)
    (hGann : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint W))),
      ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G, a • v = 0)
    (hGrank : ∃ inst : Module (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
      (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G),
        a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
      Module.finrank (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G)
        = 1) :
    ∃ (J : W.IdealSheafData), J ≠ ⊥ ∧
      ∃ (α : (pushforward i).obj J.toModules ⟶ G), Mono α ∧
        IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).map α) := by sorry

end AlgebraicGeometry.Scheme.Modules
