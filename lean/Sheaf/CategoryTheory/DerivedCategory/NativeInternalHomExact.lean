/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Ring

/-! # Exactness of the native derived internal Hom in its source

Source: Stacks Project, Cohomology on Sites, Tag 08JC, and the internal-Hom
complex proof in `DerivedCategory.exists_distinguished_ihom_pre`.
-/

@[expose] public section

set_option autoImplicit false

universe c v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open CategoryTheory.Pretriangulated.Opposite

namespace DerivedCategory

private theorem cochainSourceShift
    (C : Type c) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (P : CochainComplex C ℤ) (n : ℤ) :
    Nonempty (CochainComplex.internalHom (P⟦n⟧) ≅
      CochainComplex.internalHom P ⋙ shiftFunctor _ (-n)) := by
  let T := curriedTensor (CochainComplex C ℤ)
  let e : T.obj (P⟦n⟧) ≅ T.obj P ⋙ shiftFunctor _ n :=
    NatIso.ofComponents (fun Q ↦ ((T.flip.obj Q).commShiftIso n).app P) (by
      intro Q Q' f
      exact (NatTrans.shift_app_comm (T.flip.map f) n P).symm)
  let a := CochainComplex.tensorHomAdjunction P
  let : (CochainComplex.internalHom P).CommShift ℤ := a.rightAdjointCommShift ℤ
  exact ⟨(CochainComplex.tensorHomAdjunction (P⟦n⟧)).rightAdjointUniq
    ((a.comp (shiftEquiv _ n).toAdjunction).ofNatIsoLeft e.symm) ≪≫
      (CochainComplex.internalHom P).commShiftIso (-n)⟩

private theorem sourceShiftSign_add (m n : ℤ) :
    (m + n) * (m + n - 1) / 2 = m * (m - 1) / 2 + n * (n - 1) / 2 + m * n := by
  have even (k : ℤ) : 2 ∣ k * (k - 1) := by
    convert Int.two_dvd_mul_add_one (k - 1) using 1
    ring
  have hm := Int.ediv_mul_cancel (even m)
  have hn := Int.ediv_mul_cancel (even n)
  have hmn := Int.ediv_mul_cancel (even (m + n))
  have h : (m + n) * (m + n - 1) =
      m * (m - 1) + n * (n - 1) + 2 * (m * n) := by ring
  omega

/-- The native derived closed structure is exact in the contravariant variable.
Source: Stacks Project, Tag 08JC; the K-injective internal-Hom model used by
`exists_distinguished_ihom_pre`
(blueprint: lem-weil-native-internal-hom-contravariant-exact).

Proof: Choose a K-injective complex I representing W. Put F(P)=internalHomObj P I.
Its degree n is the product of [P^p,I^(p+n)], with differential
(-1)^p (d_I f_p - f_(p+1) d_P). The evaluation-adjunct comparison
qhInternalHomToIhom identifies Q F(P) naturally with native Hom(Q P,Q I).
It is an isomorphism for every P, since I is K-injective. Thus Q F sends
quasi-isomorphisms to isomorphisms and descends to the derived category.

For m in Z put q(m)=m(m-1)/2. Reindexing the factors p to p+m, with coefficient
(-1)^(m*(p+m)+q(m)), defines F(P[m]) -> F(P)[-m]. In terms of the target
factor indexed by r=p+m the coefficient is (-1)^(m*r+q(m)). Substitution
in the displayed differential proves the chain-map equation: the source term
uses d_(P[m])=(-1)^m d_P, and changing r to r+1 changes the coefficient by
(-1)^m. The inverse uses the inverse reindexing and the same unit scalars.
These maps are natural for precomposition. Two raw reindexings differ from the
sum reindexing by (-1)^(m*l). The identity q(m+l)=q(m)+q(l)+m*l cancels this
factor, including for negative integers; at zero both reindexing and sign are
identities. Applying the construction with m=-n gives the coherent CommShift
structure for the opposite-category n-shift.

Check triangles on a degreewise split sequence A -> B -> C, with retraction r
and section s in each degree. Its connecting cochain is h_p = r_(p+1) ∘ d_B ∘ s_p.
The reversed Hom sequence has retraction pre(s) and section pre(r), by
internalHomShortComplexSplitting. Its connecting cochain, tested in degree n
at the product factor C^p -> I^(p+n+1), is (-1)^(p+1) f_(p+1) h_p:
expanding section*d_F*retraction gives two terms, the first zero because
r_p ∘ s_p=0, and the second this expression. On the other hand the opposite
triangle's third arrow is h[-1].op, without an extra sign, as specified by
triangleOpEquivalence. Applying F and the comparison at m=-1 gives precisely
the same expression, since q(-1)=1. Thus the image triangle is the distinguished
triangle of the reversed split sequence, including its actual connecting arrow.
Every distinguished derived triangle is isomorphic to one represented by such
a split sequence of complexes. Localize the coherent shift comparisons, then
transport through qhInternalHomToIhom and the isomorphism Q I = W. This proves
IsTriangulated with that very CommShift structure. No boundedness, symmetry
beyond braiding, or reflexivity is used; the signs also work in characteristic two. -/
theorem nativeInternalHom_contravariant_exact
    (C : Type c) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (W : DerivedCategory C) :
    ∃ s : (MonoidalClosed.internalHom.flip.obj W).CommShift ℤ,
      letI := s
      (MonoidalClosed.internalHom.flip.obj W).IsTriangulated := by
  sorry

end DerivedCategory
