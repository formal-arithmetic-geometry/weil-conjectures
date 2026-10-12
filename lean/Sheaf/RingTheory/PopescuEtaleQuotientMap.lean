/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The étale map into an adapted Artinian subalgebra

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07FH, after property (1).
(blueprint: lem-weil-pbc-popescu-etale-quotient-map).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A fixed flat polynomial localization with adapted residue differentials induces an
étale map from its prime-power quotient into the admissible subalgebra. Unlike the original
existence theorem, this makes no choice of polynomial coordinates and assumes their flatness.
Source: Stacks Tag 07FH, construction of the factorization and its étaleness.
(blueprint: lem-weil-pbc-popescu-etale-quotient-map).

Proof: The polynomial evaluation into the ambient quotient has all variable images in A;
its coefficient images lie there because A is a k-subalgebra. Hence it factors through A.
Every polynomial outside p maps outside the ambient maximal ideal and thus outside m_A by
the contraction hypothesis. Such images are units in A, so extend evaluation to P by the
localization universal property. Its composite with the inclusion A → B agrees with the
quotient of ψ by uniqueness of localization maps. Since pΛ_q = qΛ_q, this composite kills
p^nP. The inclusion is injective, so the map into A also kills p^nP, giving f : P/p^nP → A
and the displayed compatibility. This map is local, since all elements of p map
into m_A. The quotient map P/p^nP → B is the base change of the flat ψ and therefore flat.
The inclusion A → B is flat local, hence faithfully flat. Flatness descends to f by 0584.
The extension of pA to B equals qB, which also equals the extension of m_A; faithful flat
ideal contraction gives pA = m_A. The induced field extension F/κ(p) is finitely generated,
since A is essentially of finite type over k. The surjection Ω(F/k) → Ω(F/κ(p)) kills the
differentials of all the coordinate residues, which span by hypothesis, so the latter is
zero. By the finitely generated field criterion (Algebra 090W) the
field extension is finite separable. Since A is Artinian, finite residue
extension and pA = m_A imply that A is finite over P/p^nP by the Artinian
finite-over-residue-finite lemma. The base is Noetherian,
so A is finitely presented. Finally the flat local criterion 00U6, with pA = m_A and finite
separable residue extension, gives étaleness at the maximal ideal. Since A is Artinian local,
this is its only prime, so the map is étale. This proves the statement without any geometric
regularity or characteristic hypothesis. -/
theorem exists_etale_popescu_quotient_map
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (A : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) [IsLocalRing A]
    (hA : A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (hAm : IsLocalRing.maximalIdeal A = Ideal.comap A.val.toRingHom
      ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (ψ : Localization.AtPrime (q.comap φ.toRingHom) →+* Localization.AtPrime q)
    (hψ : ψ.comp (algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (q.comap φ.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom)
    (hideal : q.map (algebraMap Λ (Localization.AtPrime q)) =
      (q.comap φ.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom))
    (hflat : ψ.Flat) (a : Fin m → A)
    (ha : ∀ j, (a j : Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
      Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
        (algebraMap Λ (Localization.AtPrime q) (φ (MvPolynomial.X j))))
    (hspan : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun j ↦ KaehlerDifferential.D k (IsLocalRing.ResidueField A)
        (IsLocalRing.residue A (a j)))) = ⊤) :
    ∃ f : (Localization.AtPrime (q.comap φ.toRingHom) ⧸
        ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) →+* A,
      IsLocalHom f ∧
      (letI := f.toAlgebra
       Etale (Localization.AtPrime (q.comap φ.toRingHom) ⧸
         ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
           (Localization.AtPrime (q.comap φ.toRingHom)))) ^ n) A) ∧
      (A.val.toRingHom.comp f).comp
        (Ideal.Quotient.mk ((q.comap φ.toRingHom).map (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (q.comap φ.toRingHom))) ^ n)) =
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)).comp ψ := by
  sorry

end Algebra
