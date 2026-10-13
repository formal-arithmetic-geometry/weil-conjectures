/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Factoring an ideal multiple through a generic coherent inclusion

Source: Stacks Project, Tag 01YL, third proof paragraph.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent inclusion which is an isomorphism at a point contains an ideal multiple
of its target, for a quasi-coherent ideal with full stalk at that point.

Source: Stacks Project, Tag 01YL, third proof paragraph: the ideal annihilating the
cokernel puts the ideal multiple of the target inside the source.
(blueprint: lem-weil-pbc-coherent-generic-mono-ideal-factor)

Proof: form the coherent cokernel Q of a. Exactness of stalks and surjectivity of a at
ξ make Q_ξ zero. The annihilator ideal J of Q is quasi-coherent on a locally Noetherian
scheme, and its closed zero set is the support of Q. Thus J has full ξ-stalk. Since J
annihilates Q, the composite JG → G → Q vanishes. The kernel universal property and the
canonical isomorphism of the image of the mono a with K give a factor ψ : JG → K whose
composite with a is the product inclusion. For zero Q take the unit annihilator; zero
K and zero G are included. No integral subscheme, finite sum, or generic rank enters
this factorization. -/
theorem coherent_generic_mono_ideal_factor
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    {K G : X.Modules}
    (hK : RingedSpace.IsCoherent X.toRingedSpace K)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (a : K ⟶ G) [Mono a] (ξ : X)
    (ha : Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map a).hom) :
    ∃ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf),
      Mono ι ∧ J.IsQuasicoherent ∧
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom ∧
      ∃ (ψ : idealModuleProduct ι G ⟶ K), ψ ≫ a = idealModuleProductι ι G := by sorry

end AlgebraicGeometry.Scheme.Modules
