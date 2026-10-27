/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.EtaleAlgebraLift
import Sheaf.RingTheory.FormallyEtaleAssociatedGraded
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods

/-! # Compatible quotient models with actual reduction isomorphisms

Source: Stacks Project, restricted.tex, Tag 0AKA (lemma-approximate), the compatible-model
claim in its proof (blueprint: lem-per-rig-etale-compatible-model-tower).

The index `n : ℕ` denotes the positive level `m = n + 1`. The auxiliary definitions
are the actual quotient rings, extended ideals, open complement and quotient reduction
maps occurring in the statement. The first model and its map are prescribed literally.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace Algebra.CompatibleEtaleModelTower

/-- The ideal `(a)^m = (a^m)` defining the level-m quotient.
Source: Stacks 0AKA (blueprint: lem-per-rig-etale-compatible-model-tower). -/
abbrev powerIdeal {A : Type u} [CommRing A] (a : A) (m : ℕ) : Ideal A :=
  Ideal.span {a} ^ m

/-- The ring `A_m = A/(a^m)`.
Source: Stacks 0AKA (blueprint: lem-per-rig-etale-compatible-model-tower). -/
abbrev base {A : Type u} [CommRing A] (a : A) (m : ℕ) : Type u :=
  A ⧸ powerIdeal a m

/-- The ring `E_m = E/a^m E`, using the extended ideal.
Source: Stacks 0AKA (blueprint: lem-per-rig-etale-compatible-model-tower). -/
abbrev quotient {A E : Type u} [CommRing A] [CommRing E] [Algebra A E]
    (a : A) (m : ℕ) : Type u :=
  E ⧸ (powerIdeal a m).map (algebraMap A E)

/-- The canonical `A_m`-algebra structure on `E_m`, induced by the quotient map.
Source: Stacks 0AKA (blueprint: lem-per-rig-etale-compatible-model-tower). -/
instance quotientAlgebra {A E : Type u} [CommRing A] [CommRing E] [Algebra A E]
    (a : A) (m : ℕ) : Algebra (base a m) (quotient (E := E) a m) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

/-- The canonical reduction `E_(m+1) → E_m`.
Source: Stacks 0AKA (blueprint: lem-per-rig-etale-compatible-model-tower). -/
def reduction {A E : Type u} [CommRing A] [CommRing E] [Algebra A E]
    (a : A) (m : ℕ) : quotient (E := E) a (m + 1) →+* quotient (E := E) a m :=
  Ideal.Quotient.factor (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ m)))

/-- The extended ideal `K_m = K A_m`.
Source: Stacks 0AKA (blueprint: lem-per-rig-etale-compatible-model-tower). -/
abbrev quotientIdeal {A : Type u} [CommRing A] (K : Ideal A) (a : A) (m : ℕ) :
    Ideal (base a m) :=
  K.map (Ideal.Quotient.mk (powerIdeal a m))

/-- The open complement `Spec R \ V(J)`, as a scheme open.
Source: Stacks 0AKA (blueprint: lem-per-rig-etale-compatible-model-tower). -/
def complement {R : Type u} [CommRing R] (J : Ideal R) : (Spec (CommRingCat.of R)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (J : Set R))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- Compatible finite type models can be chosen while keeping the given first model
and its map. The equivalences of completions extend the displayed maps `v`; the
reduction equivalences induce exactly the displayed transitions `t`.

Source: Stacks Project, restricted.tex, Tag 0AKA, proof of lemma-approximate
(blueprint: lem-per-rig-etale-compatible-model-tower).

Proof:
1. Keep the prescribed first model. At level m >= 2 let T = A_m, H = K_m,
   b = a^(m-1), J = (b). Then J^2 = 0 and T/J = A_(m-1). Choose an independent
   model D at level m. All finite type rings here are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian.
2. Exactness of completion on finite modules
   (lem-weil-pbc-completion-exact-finite-modules) identifies the completion of
   D_0 = D/bD with E_(m-1), with its actual quotient map. Base change preserves
   etaleness off V(K) (lem-weil-pbc-etale-base-change-finite-limits).
3. Apply lem-per-etale-away-completion-finite-refinement to D_0 and the previous
   model R, with the specified completion identification. Obtain j : R → R'
   etale and an isomorphism modulo K, and u : D_0 → R' whose completion is the
   completion of j followed after the given identification. By
   lem-sfb-augmented-etale-associated-graded, j is an isomorphism on every
   K-power quotient, hence on completion, and so is u.
4. The map u is etale off V(K) by lem-weil-pbc-etale-composition-cancellation.
   Its power quotients are isomorphisms by lem-weil-pbc-module-completion-complete.
   Thus lem-weil-pbc-etale-infinitesimal-neighbourhoods makes u etale over V(K)
   too. Finite type over the Noetherian base supplies the finiteness hypotheses.
5. Lift the etale finitely presented algebra R' along D → D_0 using
   lem-exc-etale-algebra-lift. This gives an etale D-algebra D' with D'/bD' = R'.
   Finite presentation is lem-weil-pbc-etale-algebra-finite-presentation-localization.
   Transitivity gives finite type over T and etaleness off V(H).
6. Modulo H, the etale map D → D' becomes an isomorphism modulo the square-zero
   ideal (b). Apply lem-sfb-augmented-etale-associated-graded first to (b),
   then to H, obtaining isomorphisms on all H-power quotients and on completion.
   The specified completion of u ensures the completed reduction square commutes.
7. Apply lem-per-nilpotent-etale-neighbourhood-pushout-lift to T, H, J, D', R and j.
   Obtain B → D' etale, B/bB ≃ R with reduction j after this equivalence, and B
   finite type over T and etale off V(H).
8. Reduce B → D' modulo H. Its reduction modulo (b) is j modulo K, hence an
   isomorphism. Two applications of lem-sfb-augmented-etale-associated-graded
   give a completion isomorphism. Set C_m = B and v_m to its composite into E_m.
   Set t_m to the quotient B → B/bB followed by the specified equivalence to R.
   The completed square from step 6 gives the required equality with v_(m-1).
   Recursion chooses such extensions without changing any earlier model or map.
-/
theorem exists_compatible_models
    {A E : Type u} [CommRing A] [CommRing E] [Algebra A E] [IsNoetherianRing A]
    (K : Ideal A) (a : A) [IsAdicComplete (K ⊔ Ideal.span {a}) E]
    (hcomplete : ∀ n : ℕ, IsAdicComplete (quotientIdeal K a (n + 1))
      (quotient (E := E) a (n + 1)))
    (hmodels : ∀ n : ℕ, ∃ D : CommAlgCat (base a (n + 1)),
      (algebraMap (base a (n + 1)) D).FiniteType ∧
      AlgebraicGeometry.Etale (morphismRestrict
        (Spec.map (CommRingCat.ofHom (algebraMap (base a (n + 1)) D)))
        (complement (quotientIdeal K a (n + 1)))) ∧
      Nonempty (AdicCompletion ((quotientIdeal K a (n + 1)).map
        (algebraMap (base a (n + 1)) D)) D ≃ₐ[base a (n + 1)]
          quotient (E := E) a (n + 1)))
    (C₁ : CommAlgCat (base a 1)) (v₁ : C₁ →ₐ[base a 1] quotient (E := E) a 1)
    (hfinite₁ : (algebraMap (base a 1) C₁).FiniteType)
    (hetale₁ : AlgebraicGeometry.Etale (morphismRestrict
      (Spec.map (CommRingCat.ofHom (algebraMap (base a 1) C₁)))
      (complement (quotientIdeal K a 1))))
    (hv₁ : ∃ e : AdicCompletion ((quotientIdeal K a 1).map
      (algebraMap (base a 1) C₁)) C₁ ≃ₐ[base a 1] quotient (E := E) a 1,
      ∀ x : C₁, e (algebraMap C₁ _ x) = v₁ x) :
    ∃ (C : (n : ℕ) → CommAlgCat (base a (n + 1)))
      (v : (n : ℕ) → C n →ₐ[base a (n + 1)] quotient (E := E) a (n + 1))
      (t : (n : ℕ) → C (n + 1) →+* C n),
      C 0 = C₁ ∧ HEq (v 0) v₁ ∧
      (∀ n : ℕ, (algebraMap (base a (n + 1)) (C n)).FiniteType ∧
        AlgebraicGeometry.Etale (morphismRestrict
          (Spec.map (CommRingCat.ofHom (algebraMap (base a (n + 1)) (C n))))
          (complement (quotientIdeal K a (n + 1)))) ∧
        ∃ e : AdicCompletion ((quotientIdeal K a (n + 1)).map
          (algebraMap (base a (n + 1)) (C n))) (C n) ≃ₐ[base a (n + 1)]
            quotient (E := E) a (n + 1),
          ∀ x : C n, e (algebraMap (C n) _ x) = v n x) ∧
      (∀ (n : ℕ) (r : A),
        t n (algebraMap (base a (n + 1 + 1)) (C (n + 1))
          (Ideal.Quotient.mk (powerIdeal a (n + 1 + 1)) r)) =
        algebraMap (base a (n + 1)) (C n) (Ideal.Quotient.mk (powerIdeal a (n + 1)) r)) ∧
      (∀ n : ℕ, ∃ e : (C (n + 1) ⧸ Ideal.span
        {algebraMap (base a (n + 1 + 1)) (C (n + 1))
          (Ideal.Quotient.mk (powerIdeal a (n + 1 + 1)) (a ^ (n + 1)))}) ≃+* C n,
        ∀ x : C (n + 1), e (Ideal.Quotient.mk _ x) = t n x) ∧
      (∀ (n : ℕ) (x : C (n + 1)),
        v n (t n x) = reduction (E := E) a (n + 1) (v (n + 1) x)) := by
  sorry

end Algebra.CompatibleEtaleModelTower
