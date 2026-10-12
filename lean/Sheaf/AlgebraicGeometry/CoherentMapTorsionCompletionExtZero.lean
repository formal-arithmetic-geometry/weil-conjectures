/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # A torsion kernel embeds in a sufficiently deep ideal quotient

Source: Stacks Project, Tags 0889 and 088A, uniqueness argument, via Artin--Rees.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A power-torsion kernel embeds into a sufficiently deep ideal quotient.
Source: Stacks Project, Tags 0889 and 088A, uniqueness argument.
Proof: on an affine open, Artin--Rees for the finite submodule T = ker b
of Q gives T intersect K^n Q contained in K^(n-c) T for n at least c.
Choose n at least c+t so that this intersection is zero. Thus the restriction
of Q -> Q/K^n Q to T is injective. A finite affine cover exists because X
is Noetherian; take the maximum of the finitely many bounds. Injectivity is
local on that cover, giving the stated monomorphism. Increasing n to a
positive exponent handles the zero module and unit or zero ideal cases.
(blueprint: lem-weil-pbc-coherent-map-torsion-completion-ext-zero)
-/
theorem coherentMap_torsion_completion_ext_zero
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (Q R : CoherentModules X) (b : Q ⟶ R)
    (hker : ∃ t : ℕ, 1 ≤ t ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel b.hom))) :
    ∃ n : ℕ, Mono (kernel.ι b.hom ≫ formalModuleQuotientπ K (n + 1) Q.obj) := by sorry

end AlgebraicGeometry
