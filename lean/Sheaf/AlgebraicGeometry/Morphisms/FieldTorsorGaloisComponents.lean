/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.FieldTheory.Galois.Basic

import Sheaf.FieldTheory.EtaleFieldGaloisClassification

/-! # Galois field components of a finite torsor

Source: Stacks Project, Tags 03SF and 03QR.
(blueprint: lem-sbc-field-torsor-galois-components) -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The field components of a finite group torsor are Galois of degree dividing the group order.

Source: Stacks Project, Tags 03SF and 03QR.
(blueprint: lem-sbc-field-torsor-galois-components)

Proof: A finite etale scheme over K is affine, with coordinate algebra a finite
product of finite separable fields. Use these fields, enumerated by Fin r, as E.
The finite separable extension classification identifies the geometric points of
this scheme with a finite continuous absolute Galois set. Choose a geometric point
of the torsor and identify the geometric points with G by its simply transitive
left action. The Galois action commutes with this action, so it is right translation
through a homomorphism to G. Its image J is a subgroup of G. Every orbit has
stabilizer the kernel of this homomorphism; that kernel is normal. Each component
field is therefore Galois with group J, and has degree |J|, which divides |G| by
Lagrange's theorem. The affine product decomposition gives the displayed scheme
isomorphism, and its structural maps are induced by the given K-algebra maps.
For the trivial group there is one component K. Disconnected torsors give several
orbits; no connectedness is assumed and every component has the same argument.
The fields are witnesses in a theorem, never data in a definition. -/
theorem field_torsor_galois_components
    (K : Type u) [Field K]
    (G : Type (u + 1)) [Group G] [Finite G] (T : GaloisCover G (Spec (CommRingCat.of K))) :
    ∃ (r : ℕ) (E : Fin r → Type u) (hE : ∀ i, Field (E i))
      (aE : ∀ i, Algebra K (E i)),
      letI := hE
      letI := aE
      (∀ i, FiniteDimensional K (E i) ∧ IsGalois K (E i) ∧
        Module.finrank K (E i) ∣ Nat.card G) ∧
      ∃ e : T.P ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)),
        e.hom ≫ Sigma.desc (fun i : Fin r ↦
          Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = T.π := by sorry

end AlgebraicGeometry.Scheme
