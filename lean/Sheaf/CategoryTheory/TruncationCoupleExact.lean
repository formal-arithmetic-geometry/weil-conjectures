/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.CategoryTheory.TruncationCouple
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.TruncationRawExact

/-!
# Exactness of the truncation couple

Source: Weil conjectures blueprint, sec-proper-base-change, sk-thm-properbasechange,
node lem-sp-truncation-couple-exact, order 1210; Stacks Project, Tags 08J5, 05SE,
0148 and 011Q (blueprint: lem-sp-truncation-couple-exact).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The truncation couple `truncationCouple F K a ha` = (D, E, alpha, f, g) is an exact
couple: at each of its three kinds of vertex the two consecutive structure maps compose
to zero and the resulting short complex is exact. The vertices are D^{p+2,q-1} (incoming
f : E^{p,q} → D^{p+2,q-1}, outgoing alpha), E^{p,q} (incoming g : D^{p,q} → E^{p,q},
outgoing f) and D^{p-1,q+1} (incoming alpha : D^{p,q} → D^{p-1,q+1}, outgoing g); since
p and q range over all of ℤ these are the three kernel = image conditions of
def-sp-exact-couple at every bidegree.

Proof (the four steps of the node):
1. By `lem-weil-pbc-truncation-triangle`, form the canonical triangle T_q with terms
   tau_{<=q-1}K, tau_{<=q}K and H^q(K)[-q]. All three are bounded below.
   `lem-sp-grothendieck-enough-injectives` supplies enough injectives, so the right
   derived functor exists by `lem-weil-pbc-derived-direct-image-triangulated`.
   `def-sp-kinjective-bridge` and `lem-sp-kinjective-computes` identify its cohomology
   with the chosen-resolution terms of `def-sp-truncation-couple`. The inclusions
   from T_{q+1} induce alpha, the projections from T_q induce g, and the third maps
   of T_q followed by the derived shift isomorphism induce f. Their bidegrees are
   (-1,+1), (0,0) and (+2,-1), respectively. The lower vanishing bound is unused.
2. `lem-weil-pbc-derived-direct-image-triangulated` sends each T_q to a distinguished
   triangle in D^+(B), hence in D(B).
3. By `lem-sf-derived-homology-long-exact`, its long exact cohomology sequence contains
   D^{p+1,q-1} -> D^{p,q} -> E^{p,q} -> D^{p+2,q-1} -> D^{p+1,q},
   with maps alpha, g, f, alpha. The connecting map is cohomology of the third arrow
   followed by H^n(M[1]) = H^{n+1}(M), exactly the boundary defining f.
4. Exactness for T_q gives ker g = im alpha and ker f = im g at (p,q).
   Exactness for T_{q+1}, in total degree p+q, gives ker alpha = im f at D^{p,q},
   with incoming term E^{p-2,q+1}. These equalities also give all three zero
   composites. Since p and q are arbitrary, these are all the conditions required by
   `def-sp-exact-couple`.

Source: Weil conjectures blueprint, sec-proper-base-change, sk-thm-properbasechange,
node lem-sp-truncation-couple-exact, order 1210; Stacks Project, Derived Categories,
Remark 08J5, Proposition 05SE and sequence 0148; Homological Algebra, Definition 011Q
(blueprint: lem-sp-truncation-couple-exact). -/
theorem truncationCouple_exact
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q)) :
    (∀ p q : ℤ,
      ∃ w : (truncationCouple F K a ha).2.2.2.1 p q ≫
          (truncationCouple F K a ha).2.2.1 (p + 2) (q - 1) = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : (truncationCouple F K a ha).2.2.2.2 p q ≫
          (truncationCouple F K a ha).2.2.2.1 p q = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : (truncationCouple F K a ha).2.2.1 p q ≫
          (truncationCouple F K a ha).2.2.2.2 (p - 1) (q + 1) = 0,
        (ShortComplex.mk _ _ w).Exact) := by
  let _ := HasDerivedCategory.standard A
  let _ := HasDerivedCategory.standard B
  obtain ⟨hfa, hgf, hag⟩ := truncation_raw_exact F K
  have exact_transport_local
      {X₁ X₂ X₃ Y₁ Y₂ Y₃ : B} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
      (w : a ≫ b = 0) (h : (ShortComplex.mk a b w).Exact)
      {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃}
      (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
      (h₁ : e₁.hom ≫ a' = a ≫ e₂.hom)
      (h₂ : e₂.hom ≫ b' = b ≫ e₃.hom) :
      ∃ w' : a' ≫ b' = 0, (ShortComplex.mk _ _ w').Exact := by
    have w' : a' ≫ b' = 0 := by
      rw [← cancel_epi e₁.hom, ← Category.assoc, h₁, Category.assoc, h₂,
        ← Category.assoc, w, zero_comp, comp_zero]
    refine ⟨w', ShortComplex.exact_of_iso ?_ h⟩
    exact ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂
  have reindex_hom_local
      (X Y : ℤ → ℤ → B)
      (f : ∀ p q, X p q ⟶ Y p q) {p q p' q' : ℤ}
      (hp : p = p') (hq : q = q') :
      eqToHom (congrArg₂ X hp hq) ≫ f p' q' =
        f p q ≫ eqToHom (congrArg₂ Y hp hq) := by
    subst p'
    subst q'
    simp
  dsimp only [truncationCouple]
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    exact hfa p q
  · intro p q
    obtain ⟨w, hw⟩ := hgf p q
    exact exact_transport_local _ _ w hw (Iso.refl _) (eqToIso (by simp)).symm
      (eqToIso (by simp)).symm (by simp) (by
        let E' : ℤ → ℤ → B := TruncationCouple.E F K
        let D' : ℤ → ℤ → B := TruncationCouple.D F K
        let f' : ∀ r t, E' r t ⟶ D' (r + 2) (t - 1) :=
          TruncationCouple.f F K
        have hidx := reindex_hom_local E' (fun r t ↦ D' (r + 2) (t - 1)) f'
          (show p + (0 : ℤ) = p by omega) (show q - (0 : ℤ) = q by omega)
        simpa [Iso.symm_hom, eqToIso.hom, eqToIso.inv, E', D', f'] using hidx)
  · intro p q
    obtain ⟨w, hw⟩ := hag p q
    exact exact_transport_local _ _ w hw (Iso.refl _) (Iso.refl _)
      (eqToIso (by simp)).symm (by simp) (by simp)

end CategoryTheory
