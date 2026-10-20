/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel

/-! # Finite-tail limiting subobjects

Source: Stacks Project, Tag 011T, exact-couple cycle and boundary formulas.
(blueprint: lem-sp-finite-cocone-limit-boundaries)
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

private theorem alphaIter_cocone
    {C : Type u} [Category.{v} C] [Abelian C] (X : BigradedExactCouple C 0)
    (n : ℤ) (A : AlphaColimit X n) (r : ℕ) (p q : ℤ) (hn : p + q = n) :
    X.alphaIter r p q ≫ eqToHom (by congr 1; omega) ≫ A.ι (p - r) =
      eqToHom (by congr 1; omega) ≫ A.ι p := by
  induction r generalizing p q with
  | zero =>
    apply eq_of_heq
    simp only [alphaIter, eqToHom_trans_assoc,
      eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    congr! 1
    omega
  | succ r ih =>
    have htail : X.alphaIter r (p - 1) (q + 1) ≫
        eqToHom (by congr 1 <;> omega) ≫ A.ι (p - (r + 1 : ℕ)) =
        eqToHom (by congr 1; omega) ≫ A.ι (p - 1) := by
      have hh := ih (p - 1) (q + 1) (by omega)
      apply eq_of_heq
      have hleft : X.alphaIter r (p - 1) (q + 1) ≫
          eqToHom (by congr 1 <;> omega) ≫ A.ι (p - (r + 1 : ℕ)) ≍
          X.alphaIter r (p - 1) (q + 1) ≫
            eqToHom (by congr 1; omega) ≫ A.ι (p - 1 - r) := by
        apply heq_comp rfl rfl rfl HEq.rfl
        simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
        congr! 1
        omega
      exact hleft.trans (heq_of_eq hh)
    simp only [alphaIter, Category.assoc, eqToHom_trans_assoc]
    rw [htail]
    apply eq_of_heq
    have hm : X.alpha p q ≫ eqToHom (by congr 1; omega) ≫ A.ι (p - 1) ≍
        X.alphaDiagonal n (p - 1) ≫ A.ι (p - 1) := by
      dsimp [alphaDiagonal]
      simp only [Category.assoc]
      apply heq_comp (f := X.alpha p q)
        (f' := X.alpha (p - 1 + 1) (n - (p - 1 + 1)))
        (by congr 1 <;> omega) (by congr 1 <;> omega) rfl
      · congr! 1 <;> omega
      · simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
        rfl
    apply (hm.trans (heq_of_eq (A.comm (p - 1)))).trans
    rw [heq_eqToHom_comp_iff]
    congr! 1
    omega

/-- An invertible left cocone tail identifies limiting boundaries with g of its kernel.
Source: Stacks Project, Tag 011T, formula for boundaries; Tag 012W, lower-tail argument.
(blueprint: lem-sp-finite-cocone-limit-boundaries).

Proof: Write T for the canonical cycle-boundary tower, and suppress only the
canonical integer-index transports. First prove by induction on r that
T.B r p q = initialG(ker(alphaIter r p q)). At r=0 the iterate is an
isomorphism and T.B 0 is zero. For the induction, construct the canonical epi
 e_r : D(p,q) -> D_r(p-r,q+r) by iterating image projections. Its composite
with the canonical mono inclusion I_r is alphaIter r. The derived-map
restriction equations show that e_r followed by derived g_r agrees with the
factorization of initialG into T.Z r followed by T.projection r. They also
show that derived alpha_r followed by the next I_r agrees with the original
alpha at the endpoint of alphaIter r. Hence e_r(x) is killed by derived alpha
exactly when x is killed by alphaIter (r+1), by monicity of I_r.

Use generalized elements with epimorphic refinements throughout. Exactness
of the r-th couple identifies the incoming differential image at (p,q) with
derived g_r of ker(derived alpha_r) at (p-r,q+r). Given an element z of the
pullback defining T.B (r+1), lift its differential-image representative to
ker(derived alpha_r), then lift along e_r after refinement. The lift x is
killed by alphaIter (r+1). The projection of z-initialG(x) is zero, so this
difference lies in T.B r by projection_kernel. By induction it is initialG(y)
for y killed by alphaIter r, after another refinement. Thus z=initialG(x+y),
with x+y killed by alphaIter (r+1). Conversely, any such x maps under e_r
into ker(derived alpha_r)=im(derived f_r); its derived g image is an incoming
differential boundary. Since initialG(x) lies in all cycles, B_succ places it
in T.B (r+1). These tests prove the induction equality. Refinements descend
because each subobject is the kernel of its cokernel in an abelian category.

Let j_p be the transported cocone map in the conclusion. Iterating A.comm
shows j_p = alphaIter r p q followed by the transported map A(p+q).ι(p-r).
Choose a from hleft(p+q). For every r with p-r <= a the second factor is an
isomorphism, so ker(alphaIter r p q)=ker(j_p). For every smaller r, its kernel
is contained in ker(j_p) by the same cocone equation. Thus all T.B r are at
most initialG(ker(j_p)), and all sufficiently large r equal it. This value
is the least upper bound of the boundary range; uniqueness with L.B_lub
proves the assertion. No cycle regularity or upper zero tail is needed. -/
theorem finiteCocone_limitBoundaries
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hleft : ∀ n : ℤ, ∃ a : ℤ, ∀ P : ℤ, P ≤ a → IsIso ((A n).ι P))
    (L : X.LimitSubobjects) (p q : ℤ) :
    L.B p q = (Subobject.«exists» (X.initialG p q)).obj
      (kernelSubobject (eqToHom (by congr 1; omega) ≫ (A (p + q)).ι p)) := by
  let j : X.D p q ⟶ (A (p + q)).obj :=
    eqToHom (by congr 1; omega) ≫ (A (p + q)).ι p
  let S := (Subobject.«exists» (X.initialG p q)).obj (kernelSubobject j)
  let c (r : ℕ) : X.D (p - r) (q + r) ⟶ (A (p + q)).obj :=
    eqToHom (by congr 1; omega) ≫ (A (p + q)).ι (p - r)
  have hc (r : ℕ) : X.alphaIter r p q ≫ c r = j :=
    alphaIter_cocone X (p + q) (A (p + q)) r p q rfl
  have hle (r : ℕ) : X.cycleBoundaryTower.B r p q ≤ S := by
    rw [finiteBoundary_alphaKernel]
    apply (Subobject.«exists» (X.initialG p q)).monotone
    simpa only [hc r] using kernelSubobject_comp_le (X.alphaIter r p q) (c r)
  obtain ⟨a, ha⟩ := hleft (p + q)
  let r := (p - a).toNat
  have hr : p - (r : ℤ) ≤ a := by dsimp [r]; omega
  have hi : IsIso ((A (p + q)).ι (p - r)) := ha _ hr
  let := hi
  have hmono : Mono (c r) := by dsimp [c]; infer_instance
  let := hmono
  have heq : X.cycleBoundaryTower.B r p q = S := by
    rw [finiteBoundary_alphaKernel]
    dsimp [S]
    congr 1
    symm
    simpa only [hc r] using kernelSubobject_comp_mono (X.alphaIter r p q) (c r)
  change L.B p q = S
  apply le_antisymm
  · exact (L.B_lub p q).2 (by rintro _ ⟨t, rfl⟩; exact hle t)
  · rw [← heq]
    exact (L.B_lub p q).1 ⟨r, rfl⟩

end CategoryTheory.BigradedExactCouple
