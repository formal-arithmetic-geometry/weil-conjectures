/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Mathlib.RingTheory.AdicCompletion.Exactness
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Detecting maps using completion and a torsion-kernel comparison

Source: Stacks Project, Tag 0889, uniqueness argument, and Tag 088A, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Completion and composition with a map having power-torsion kernel detect maps.
Only the kernel of b needs a bound; its cokernel plays no role.
Source: Stacks Project, Tag 0889, uniqueness argument, and Tag 088A, final paragraph
(blueprint: lem-weil-pbc-coherent-map-torsion-completion-ext).

Proof: work on an affine open Spec A, where all three sheaves are finite A-modules.
The difference d = f-g lands in T = ker b by the comparison equality. Equality of
all completed components says the induced completed map is zero. Completion is exact
on finite modules over a Noetherian ring, so the completed inclusion T -> Q is
injective and the completed map into T is zero. Since K^t T = 0, the K-adic system
of T is constant from exponent t onwards and T -> its completion is an isomorphism.
Consequently the map P -> T is zero and d = 0. This gives equality on every affine
open and therefore equality of sheaf maps. For K the unit ideal, T is zero already;
for K zero, completion is the identity. The empty scheme has only zero maps.
-/
theorem coherentMap_torsion_completion_ext
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (P Q R : CoherentModules X) (b : Q ⟶ R)
    (hker : ∃ t : ℕ, 1 ≤ t ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel b.hom)))
    (f g : P ⟶ Q) (hcomp : f ≫ b = g ≫ b)
    (hcompletion : (completion X K).map f = (completion X K).map g) : f = g := by sorry

end AlgebraicGeometry
