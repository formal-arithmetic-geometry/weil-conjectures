/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.CoherentHomsOverOpen
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! Generic coherent ideal lattices. Source: Stacks Project, Tag 01YE. -/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite free map defined near the generic point extends from an ideal-sum lattice.

Source: Stacks Project, Tag 01YE, extension over a power of the complement ideal.
Proof: let J be the vanishing ideal of the closed subset Z ∖ U, with its
reduced induced closed subscheme structure. Its affine radical-ideal description
and the affine ideal-zero-set criterion show that J_x → O_{Z,x} is surjective
exactly for x ∈ U. Thus the open supplied by coherent_homs_over_open for J is U.
Let E be the finite free source. It is coherent by the locally Noetherian criterion;
G is quasi-coherent by that criterion and hG. Identify restriction to the open scheme
with restriction to the slice site, and apply the final surjectivity clause of
coherent_homs_over_open to the given φ. Obtain n and a map J^n E → G whose restriction
agrees with φ after the canonical inclusion J^n E → E.
Construct I as the ideal sheaf with affine sections J(W)^n (the unit ideal if n = 0).
The affine-sections formula for ideal products identifies J^n E with the finite sum
of copies of I: in each coordinate multiplication has image J(W)^n, and these
identifications commute with localization and glue on overlaps. Use this isomorphism
to turn the extension into χ. The power ideal is quasi-coherent by the ideal-products
lemma, and its inclusion into the coherent structure module is a monomorphism, so
the quasi-coherent-submodule clause gives its coherence. On U its inclusion is an
isomorphism, as is the inclusion J^n E → E. Take the stalk of the extension identity
at ξ ∈ U and conjugate by the restriction-stalk isomorphisms. It expresses χ_ξ as
φ_ξ composed with isomorphisms, so χ_ξ is invertible. For n = 0 this is the unit
ideal and for r = 0 all coordinate statements are empty; the argument still applies.
(blueprint: lem-weil-pbc-coherent-integral-generic-lattice-extension)
-/
theorem exists_generic_ideal_extension (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules)
    (hG : RingedSpace.IsCoherent Z.toRingedSpace G)
    (r : ℕ) (U : Z.Opens) (hx : genericPoint Z ∈ U)
    (φ : (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))) ⟶
      (restrictFunctor U.ι).obj G)
    (hφ : IsIso ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
      (⟨genericPoint Z, hx⟩ : U.toScheme)).map φ)) :
    ∃ (I : Z.IdealSheafData),
      RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      ∃ (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G),
        IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace
          (genericPoint Z)).map χ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
