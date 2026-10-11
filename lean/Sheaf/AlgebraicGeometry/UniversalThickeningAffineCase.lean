/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Spectra of universal square-zero algebra extensions

Source: Stacks Project, More on Morphisms, proof of Lemma 04F3, affine-case paragraph,
using Algebra, Lemma 04EB (blueprint: lem-weil-pbc-universal-thickening-affine-case).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The spectrum of a universal square-zero extension of `R`-algebras is a universal
first order thickening over `Spec R`, including tests by non-affine schemes.
Source: Stacks Project, More on Morphisms, proof of Lemma 04F3, third paragraph
(blueprint: lem-weil-pbc-universal-thickening-affine-case).

Proof:
1. Use the bijection between maps `Y → Spec B` and ring maps `B → Γ(Y)`
   (lem-weil-pbc-morphism-into-affine-scheme). Its compatibility with composition and
   Spec maps follows from functoriality and lem-weil-pbc-spec-map-global-sections.
2. The algebra structure maps commute with `π`, so the triangle of spectra commutes.
   Surjectivity of `π` gives a closed immersion by
   lem-weil-pbc-closed-immersion-affine-cover-criterion. Its ideal sheaf on the whole
   affine target corresponds to the kernel of `π`; powers are computed on affine opens
   (def-sbc-closed-immersion-ideal-sheaf, def-sbc-ideal-sheaf-powers). Thus its square
   is zero, and it is a first order thickening (def-sbc-first-order-thickening).
3. For affine `T'`, the closed immersion `T → T'` gives a surjection on global sections
   with square-zero kernel. Identify its quotient with `Γ(T)`. Under the bijection in
   step 1, the two required conditions on a lift are precisely that it is an `R`-algebra
   map and that its composite with the quotient map is `a.comp π`. The ring universal
   property therefore gives exactly one scheme lift.
4. Restrict an arbitrary test thickening to opens of `T'`, using
   lem-weil-pbc-thickening-open-restriction and
   lem-weil-pbc-morphism-factors-through-open-subscheme. Solutions restrict to solutions.
5. Cover `T'` by affine opens (lem-weil-pbc-affine-opens-basis). Step 3 gives local lifts.
   On overlaps these agree on every affine open by uniqueness. Scheme morphism gluing
   (lem-weil-pbc-scheme-morphism-gluing) gives a global lift. Both triangle identities
   hold locally, hence globally; any other lift agrees locally and hence globally.
6. Steps 2 and 5 are exactly def-weil-pbc-universal-first-order-thickening. -/
theorem isUniversalFirstOrderThickening_spec
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    (φ : R →+* S)
    [Algebra R S] [Algebra R S'] (π : S' →ₐ[R] S)
    (hφ : algebraMap R S = φ)
    (hπ : Function.Surjective π) (hK : RingHom.ker π.toRingHom ^ 2 = ⊥)
    (hUniversal : ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A),
      I ^ 2 = ⊥ → ∀ a : S →ₐ[R] A ⧸ I,
        ∃! a' : S' →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp π) :
    IsUniversalFirstOrderThickening
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom π.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R S'))) := by
  sorry

end AlgebraicGeometry
