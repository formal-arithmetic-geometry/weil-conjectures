/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Detection of formal maps by a torsion comparison and one quotient

Source: Stacks Project, Tags 0889 and 088A, Artin--Rees uniqueness argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- One separating quotient detects the difference of two formal maps into Q
whose composites with b agree.
Source: Stacks Project, Tags 0889 and 088A, uniqueness argument.
Proof: on an affine open, write T = ker(b). Exactness of Noetherian completion
identifies the kernel of the completed map with the completion of T. Since a
fixed power of J annihilates T, its completion is canonically T itself. The
hypothesis hsep embeds T into Q/J^(n+1)Q. For the difference of the two compatible
families, the composition hypothesis therefore puts its image in this copy of T,
and the equality of the n-th components kills its image in Q/J^(n+1)Q. Injectivity
of the displayed embedding kills the difference. The affine completion equivalence
identifies compatible quotient maps with maps of complete finite modules; hence
all components agree on this affine open. Equality is local on the affine cover,
and componentwise equality proves equality of the formal morphisms. At J=0 the
chosen quotient is Q; at the unit ideal T=0 and every completion term is zero.
(blueprint: lem-weil-pbc-formal-map-torsion-finite-detection). -/
theorem formalMap_torsion_finite_detection
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (Q R : CoherentModules X) (b : Q ⟶ R)
    (hker : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel b.hom)))
    (n : ℕ) (hsep : Mono (kernel.ι b.hom ≫ formalModuleQuotientπ J (n + 1) Q.obj))
    (M : CoherentFormalModule X J) (f g : M ⟶ (completion X J).obj Q)
    (hcomp : f ≫ (completion X J).map b = g ≫ (completion X J).map b)
    (hlevel : f.hom.app (op n) = g.hom.app (op n)) : f = g := by sorry

end AlgebraicGeometry
