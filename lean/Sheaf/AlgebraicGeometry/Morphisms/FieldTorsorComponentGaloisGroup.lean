/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.FieldTheory.Galois.Basic

import Sheaf.FieldTheory.EtaleFieldGaloisClassification

/-! # The Galois group of one field component of a finite torsor

Source: Stacks Project, Tags 03SF and 03QR.
(blueprint: lem-sbc-field-torsor-component-galois-group) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A field component of a finite group torsor is Galois, with automorphism group isomorphic
 to a subgroup of the torsor group.

Source: Stacks Project, Tags 03SF and 03QR.
(blueprint: lem-sbc-field-torsor-component-galois-group)

Proof: Since the structure map is finite etale, the open subscheme Spec E is a connected
component, and E/K is finite separable. Choose a separable closure Ks and a geometric point
in this component. Simple transitivity identifies all geometric points of the torsor with G.
The absolute Galois action commutes with the left G-action, hence is right multiplication:
write gamma(x) = x * c(gamma). With the usual left action convention c reverses products,
so gamma maps to c(gamma)^(-1) by a homomorphism. Its kernel N is open and normal, and is
also the stabilizer of every geometric point. In particular the chosen component corresponds
to a conjugate of N, which equals N. The finite separable extension/Galois-set correspondence
therefore identifies E with the fixed field of N. Normality makes E/K Galois and identifies
its automorphism group with Gal(Ks/K)/N. The homomorphism above identifies this quotient with
its image subgroup of G. Compose these group isomorphisms to obtain the stated equivalence.
No connectedness of the entire torsor is assumed. For the trivial group the component is K;
for a split torsor every component has trivial automorphism group. The inclusion of Spec E
is nonempty because E is a field, so there is no empty-component case. -/
theorem field_torsor_component_galois_group
    (K : Type u) [Field K]
    (G : Type (u + 1)) [Group G] [Finite G]
    (T : GaloisCover G (Spec (CommRingCat.of K)))
    (E : Type u) [Field E] [Algebra K E]
    (j : Spec (CommRingCat.of E) ⟶ T.P) [IsOpenImmersion j]
    (hj : j ≫ T.π = Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    IsGalois K E ∧ ∃ H : Subgroup G, Nonempty ((E ≃ₐ[K] E) ≃* H) := by sorry

end AlgebraicGeometry.Scheme
