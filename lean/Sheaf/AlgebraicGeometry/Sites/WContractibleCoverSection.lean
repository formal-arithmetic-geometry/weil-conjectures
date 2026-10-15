/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Sections of pro-etale covers of w-contractible affine schemes

Source: Stacks Project, Tag 098F, forward implication, with Tags 098D and 0981
(blueprint: lem-weil-pbc-wcontractible-cover-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A pro-etale covering of an affine scheme whose faithfully flat weakly etale
algebras all retract admits a section into its covering coproduct.
Source: Stacks Project, Tag 098F, forward implication, and Tags 098D and 0981
(blueprint: lem-weil-pbc-wcontractible-cover-section).

Proof:
1. Apply the covering condition to the whole affine target to obtain a finite
   jointly surjective refinement by affine opens of the cover members (098D).
   Weak etaleness restricts to these opens by source locality
   (lem-weil-pbc-weakly-etale-source-locality).
2. Their finite coproduct is the spectrum of the product of their rings
   (lem-weil-pbc-finite-affine-coproduct-spectrum). Source locality makes its
   map to the target weakly etale, and the refinement makes it surjective.
3. Write that map as Spec of a ring map. Flatness follows from
   lem-weil-pbc-flat-ring-map-iff-flat-affine; surjectivity gives faithful
   flatness by lem-weil-pbc-flat-surjective-spectrum-faithfully-flat.
   The spectrum/ring weak-etaleness equivalence gives a weakly etale algebra.
   Apply the retraction hypothesis and take Spec to obtain a section of the
   finite affine coproduct map.
4. The refinement maps induce a map from the finite coproduct to the original
   coproduct (lem-weil-pbc-scheme-coproduct-family). Coproduct uniqueness shows
   its composite to the target is the finite covering map. Composing the
   section from step 3 with this refinement map proves the asserted identity.
   The empty refinement and zero ring cases obey the same construction. -/
theorem exists_section_proetaleCover_of_ring_retractions
    (A : Type u) [CommRing A]
    (hsplit : ∀ (B : Type u) [CommRing B] [Algebra A B],
      Module.FaithfullyFlat A B → Algebra.WeaklyEtale A B →
        ∃ r : B →+* A, r.comp (algebraMap A B) = RingHom.id A)
    (I : Type u) (T : I → Scheme.{u}) (f : ∀ i : I, T i ⟶ Spec (.of A))
    (hcover : Presieve.ofArrows T f ∈ Scheme.proetalePrecoverage (Spec (.of A))) :
    ∃ σ : Spec (.of A) ⟶ ∐ T, σ ≫ Sigma.desc f = 𝟙 (Spec (.of A)) := by
  sorry

end AlgebraicGeometry
