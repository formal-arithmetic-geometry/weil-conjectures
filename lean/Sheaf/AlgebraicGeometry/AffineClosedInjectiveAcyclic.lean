/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Affine case of restricted injective acyclicity

Source: Stacks Project, Tag 0A51, the case n = 0.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- The restriction of a torsion injective module sheaf to a closed subscheme of an
 affine scheme has no positive cohomology.

Source: Stacks Project, Tag 0A51, first paragraph of the proof.
(blueprint: lem-weil-pbc-affine-closed-injective-acyclic)

Proof: write the affine scheme as Spec B and its closed subscheme as Spec B/K.
Form the henselization Bʰ of the pair (B,K), the filtered colimit of etale B-algebras C
whose reduction is B/K. Its quotient by KBʰ is B/K. Gabber's comparison identifies
cohomology of the restricted sheaf on the closed subscheme with that on Spec Bʰ.
Torsion is preserved by inverse image, so this comparison applies even when the
coefficient ring itself is not torsion. The limit theorem identifies the latter
cohomology with the filtered colimit of cohomology on Spec C. Restriction along
Spec C → Spec B preserves injective module sheaves, since etale extension by zero
is an exact left adjoint. Their underlying abelian sheaves are cohomologically
acyclic by Stacks 03FD: injective module sheaves have vanishing positive Cech
cohomology for every covering, which implies abelian cohomological acyclicity
by the Cech vanishing criterion. Thus every positive-degree group is zero. The colimit
is zero, and the comparison proves the assertion, including the empty closed
subscheme. All identifications commute with forgetting the module structure. -/
theorem Etale.subsingleton_H_affine_closed_of_injective
    (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective J] [IsTorsionSheaf J] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((i)^*[ModuleCat.{u + 1} Λ].obj J)) q) := by sorry

end AlgebraicGeometry
