/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker T1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistSections
public import Sheaf.AlgebraicGeometry.AlternatingCechComputes
public import Sheaf.AlgebraicGeometry.ProjectiveSpace.ExponentCechComplex

/-!
# Laurent monomial decomposition of the alternating twist Čech complex

Source: Stacks Project, Tag 01XS, proof of Lemma 30.8.1
(blueprint: lem-pc-twist-cech-monomial-decomposition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme.Modules MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

open Classical in
/-- Sections on each nonempty standard intersection have the Laurent monomial basis;
restriction includes these bases. The alternating Čech complex, specified by its
terms and signed restriction differential as in `Scheme.alternatingCechComputes`,
is the direct sum of the existing `exponentCechComplex` complexes. The last clause
pins this isomorphism to the monomial coefficients, so its summands are the actual
fixed-exponent subcomplexes.

Source: Stacks Project, Tag 01XS, proof of Lemma 30.8.1
(blueprint: lem-pc-twist-cech-monomial-decomposition).

Proof:
1. On U_J, the twist transition rule identifies a section with a degree-d Laurent
   polynomial whose denominators involve only J. Laurent monomials are independent
   over any commutative ring and span these sections (def-pc-projective-space-twist,
   lem-pc-twist-cocycle, def-pc-proj).
2. Restriction localizes at the additional coordinates and preserves each monomial
   (def-pc-proj, def-pc-projective-space-twist).
3. The alternating differential is the signed face-restriction sum
   (lem-pc-alternating-cech-computes). It preserves the exponent vector. In each
   degree the finitely many intersections allow interchange of their finite sum
   with the direct sum over exponents. For a fixed exponent the allowed subsets
   are exactly those containing all its negative coordinates. The inherited
   differential adds one vertex with its position sign, giving exponentCechComplex.
-/
theorem twist_cech_monomial_decomposition (A : Type u) [CommRing A]
    (n : ℕ) (hn : 1 ≤ n) (d : ℤ) :
    ∃ b : ∀ (s : Set (ULift.{u} (Fin (n + 1)))), s.Nonempty →
      (laurentExponents s d →₀ A) ≃ₗ[A]
        ((ModuleCat.restrictScalars
          (((Scheme.ΓSpecIso (.of A)).inv ≫
            (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A)).appTop).hom)).obj
          ((twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) d).presheafModuleCat.obj
            (op (toProjInt (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ⁻¹ᵁ
              basicOpenInt (ULift.{u} (Fin (n + 1))) s)))),
      (∀ (s : Set (ULift.{u} (Fin (n + 1)))) (hs : s.Nonempty)
        (e : laurentExponents s d) (a : A),
        b s hs (Finsupp.single e a) =
          ((Scheme.ΓSpecIso (.of A)).inv ≫
            (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A)).appTop ≫
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)).presheaf.map
              (homOfLE (le_top : toProjInt (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ⁻¹ᵁ
                basicOpenInt (ULift.{u} (Fin (n + 1))) s ≤ ⊤)).op) a •
            twistMonomialSection (Spec (.of A)) s e) ∧
      (∀ (s t : Set (ULift.{u} (Fin (n + 1)))) (hs : s.Nonempty) (ht : t.Nonempty)
        (hst : s ⊆ t) (e : laurentExponents s d) (a : A),
        (twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) d).presheafModuleCat.map
            (homOfLE ((toProjInt (ULift.{u} (Fin (n + 1))) (Spec (.of A))).preimage_mono
              (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ) hst))).op
            (b s hs (Finsupp.single e a)) =
          b t ht (Finsupp.single ⟨e.1, laurentExponents_mono hst d e.2⟩ a)) ∧
      ∃ K : CochainComplex (ModuleCat.{u} A) ℕ,
      ∃ g : ∀ p : ℕ, K.X p ≃ₗ[A]
        (∀ t : {t : Fin (p + 1) → ULift.{u} (Fin (n + 1)) // StrictMono t},
          ((ModuleCat.restrictScalars
            (((Scheme.ΓSpecIso (.of A)).inv ≫
              (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A)).appTop).hom)).obj
            ((twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) d).presheafModuleCat.obj
              (op (toProjInt (ULift.{u} (Fin (n + 1))) (Spec (.of A)) ⁻¹ᵁ
                basicOpenInt (ULift.{u} (Fin (n + 1))) (Set.range t.1)))))),
      ∃ q : (∐ fun e : {e : Fin (n + 1) → ℤ // ∑ i, e i = d} ↦
        exponentCechComplex (A := A) n e.1) ≅ K,
        (∀ (p : ℕ) (c : K.X p)
          (t : {t : Fin (p + 2) → ULift.{u} (Fin (n + 1)) // StrictMono t}),
          g (p + 1) ((K.d p (p + 1)) c) t =
            ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
              ((ModuleCat.restrictScalars
                (((Scheme.ΓSpecIso (.of A)).inv ≫
                  (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘
                    Spec (.of A)).appTop).hom)).map
                ((twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) d).presheafModuleCat.map
                (homOfLE ((toProjInt (ULift.{u} (Fin (n + 1))) (Spec (.of A))).preimage_mono
                  (Proj.basicOpen_monomialToNat_indicator_mono (R := ULift.{u} ℤ)
                    (s := Set.range t.1) (t := Set.range (t.1 ∘ j.succAbove))
                    (Set.range_comp_subset_range j.succAbove t.1)))).op))
                (g p c ⟨t.1 ∘ j.succAbove,
                  t.2.comp (Fin.strictMono_succAbove j)⟩)) ∧
        (∀ (p : ℕ) (e : {e : Fin (n + 1) → ℤ // ∑ i, e i = d})
          (J : exponentCechBasis n e.1 p) (a : A)
          (t : {t : Fin (p + 1) → ULift.{u} (Fin (n + 1)) // StrictMono t})
          (w : laurentExponents (Set.range t.1) d),
          ((b (Set.range t.1) ⟨t.1 0, Set.mem_range_self 0⟩).symm
            (g p ((q.hom.f p)
              (((Sigma.ι (fun e : {e : Fin (n + 1) → ℤ // ∑ i, e i = d} ↦
                exponentCechComplex (A := A) n e.1) e).f p)
                (Finsupp.single J a))) t)) w =
              if (fun i ↦ w.1 (ULift.up i)) = e.1 ∧
                Set.range t.1 = ULift.up '' (J.1 : Set (Fin (n + 1))) then a else 0) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
