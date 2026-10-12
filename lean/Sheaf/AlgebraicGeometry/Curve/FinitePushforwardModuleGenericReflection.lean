/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.GenericFiniteAlgebraSplitting
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.BaseChange

/-! # Generic local constancy reflected by a finite direct image

Source: Stacks Project, Tags 095K, 0959, 04DZ and 0A5D, with the module direct-factor
argument in the parent node's proof, steps 1--3.
(blueprint: lem-weil-pbc-finite-module-generic-reflection)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Generic local constancy of the source, after shrinking a dense open where the finite
module direct image is finite locally constant. Only the generic part is asserted;
nothing is claimed on the complement.
Source: Stacks Project, Tags 095K, 0959 and 04DZ; module direct-factor refinement of 0A5D.
(blueprint: lem-weil-pbc-finite-module-generic-reflection)

Proof: Reduce the Noetherian target, using the equivalence of etale sites for reduction.
There are finitely many irreducible components. Remove their pairwise intersections and
choose an affine integral dense open in each component, contained in V. Their union is
still dense. On each affine apply generic finite-algebra splitting and shrink further:
a finite etale surjective cover splits the inverse image into finitely many open-and-closed
pieces universally homeomorphic to the cover, including the unreduced source by reduction.
Finite base change identifies the pushforward there with the pullback of the finite locally
constant direct image. The direct image of each piece is a retract of this sheaf.
A retract of a finite locally constant module sheaf is locally constant: trivialize the
ambient sheaf as M, locally express its projector by a linear endomorphism using the finite
generators of M, and take its image. Equivalently its image is the kernel of one minus the
projector, whose local constancy follows from the module kernel theorem without a
Noetherian coefficient hypothesis. Universal-homeomorphism invariance transports this
local constancy to each source piece. Compose the trivializing covers to descend it along
the surjective etale cover, then along the disjoint affine open cover. The finitely many
shrunk opens give U. For an empty target density is vacuous; an empty finite inverse image
has locally constant zero sheaves. No arbitrary object is constructed from this existential
statement: U is used only as an existential witness in proofs. -/
theorem exists_dense_open_locallyConstant_of_finite_lowerStar_module
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : Y.Opens) (hV : Dense (V : Set Y))
    (h : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F))) :
    ∃ U : Y.Opens, U ≤ V ∧ Dense (U : Set Y) ∧
      IsLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ⁻¹ᵁ U).ι).obj F) := by sorry

end AlgebraicGeometry.Scheme
