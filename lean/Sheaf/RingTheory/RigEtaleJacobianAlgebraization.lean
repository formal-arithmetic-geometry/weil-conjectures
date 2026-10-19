/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.RingTheory.CompletedPolynomialConormal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Algebraization from torsion in the completed conormal differential

Source: Stacks Project, restricted.tex, Tags 0AKG and 0AJU
(blueprint: lem-per-rig-etale-jacobian-algebraization).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- Algebraization from torsion in the completed conormal differential.
Source: Stacks Project, restricted.tex, Tag 0AKG (lemma-approximate-by-etale-over-complement),
with condition (3) of Tag 0AJU (lemma-equivalent-with-artin)
(blueprint: lem-per-rig-etale-jacobian-algebraization).
Proof (Stages 0AKA, 0ALS, 0GB2 and 0ALQ):
1. Induct on the length of generators of I (def-weil-pbc-noetherian-ring). For I = 0,
   take the finite type quotient E itself, since completion is trivial and the complement empty.
2. For any finite type model C with completion E, lem-per-jacobian-torsion-etale-shrink
   gives g = 1 + x, x in IC, such that D = C_g is etale away from V(I).
   Modulo I^n, g has inverse sum_{j<n} (-x)^j, so the compatible quotient isomorphisms
   give the same completion; D is still finite type.
3. For one generator apply lem-per-principal-jacobian-algebraization, then step 2.
4. For I = K + (a), reduce modulo a^m. The quotient base is Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian; the vanishing loci of I and K coincide
   there. Apply lem-per-jacobian-torsion-closed-base-change to get complete presentations
   with conormal torsion (the exponent may depend on m).
5. Apply induction over each quotient base. The resulting finite type models need not be
   compatible. lem-per-rig-etale-principal-reduction assembles them into an (a)-complete
   algebra F with conormal torsion and I-completion E.
6. Apply lem-per-principal-jacobian-algebraization to F, obtaining C with (a)-completion F.
   C is Noetherian. By lem-weil-pbc-completion-exact-finite-modules, complete
   0 -> I^n C -> C -> C/I^n C -> 0 along (a). Finite generators identify the first image
   with I^n times the completion; a^n lies in I^n, so C/I^n C is already (a)-complete.
   Thus C/I^n C identifies canonically with F/I^n F. These maps commute with reduction;
   their inverse limits identify the I-completion of C with E.
7. Apply step 2 to this C to finish the generator induction. -/
theorem rigEtaleJacobianAlgebraization {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (r : ℕ) (J : Ideal (rigPolynomialCompletion I r))
    [IsAdicComplete I (rigPolynomialCompletion I r ⧸ J)] (c : ℕ)
    (hkernel : I ^ c • (rigJacobianDifferential r I J).ker ≤ ⊥)
    (hcoker : I ^ c •
      (⊤ : Submodule A ((Fin r → (rigPolynomialCompletion I r ⧸ J)) ⧸
        (rigJacobianDifferential r I J).range)) ≤ ⊥) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      RingHom.FiniteType (algebraMap A D) ∧
        (∀ f : A, f ∈ I → Etale (Spec.map (CommRingCat.ofHom
          (IsLocalization.Away.map (Localization.Away f)
            (Localization.Away (algebraMap A D f)) (algebraMap A D) f)))) ∧
        Nonempty (AdicCompletion (I.map (algebraMap A D)) D ≃ₐ[A]
          (rigPolynomialCompletion I r ⧸ J)) := by
  sorry

end AlgebraicGeometry
