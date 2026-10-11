/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.CategoryTheory.DoubleComplexTotal
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Homotopy

/-!
# Horizontal and vertical components of a Cartan--Eilenberg comparison homotopy

Source: Stacks Project, Derived Categories, Tags 015I and 015K; Weibel,
Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-cartan-eilenberg-double-complex-homotopy).

The vertical natural index is extended by zero using Mathlib's extension functor
before forming the integer-indexed total complex and its second filtration.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A comparison lifting an augmented null-homotopy admits horizontal and vertical
components, with a total homotopy lowering the vertical filtration by at most one.
Source: Stacks Project, Tags 015I and 015K; Weibel, Homological Algebra, Lemma 5.7.10
(blueprint: lem-sp-cartan-eilenberg-double-complex-homotopy).

Proof:
1. Apply lem-sp-ce-horizontal-lift to the exact source and injective target
   boundary, cycle and cohomology resolutions. Lift the given homotopy s to
   vertical-complex maps s1, respecting the augmentation. The residual
   R = delta - d_h s1 - s1 d_h vanishes on the augmentation.
2. R commutes with both differentials: horizontally this follows from d_h squared
   being zero, vertically from s1 being a column map. Apply
   lem-sp-ce-vertical-nullhomotopy to assemble compatible row null-homotopies
   through the exact cycle/boundary sequences, obtaining s2 with
   R = d_v s2 + s2 d_v and s2 d_h = d_h s2.
3. Set H = s1 + (-1)^p s2 on each diagonal summand. Expanding
   d_Tot = d_h + (-1)^p d_v gives the diagonal identity delta and cancels
   the two off-diagonal terms, using the compatibilities of s1 and s2.
4. s1 preserves vertical degree; s2 lowers it by one. Thus their sum factors
   from F^q in degree n through F^(q-1) in degree n-1. First-quadrant vanishing
   makes each diagonal finite (def-sp-double-complex-total, def-sp-filtration).

Exactness of the canonical sequences of horizontal cycles, boundaries and
cohomology is automatic in the abelian category of vertical complexes.
The resolution hypotheses are the quasi-isomorphism and term-injectivity
fields of InjectiveResolution, as in exists_cartanEilenberg_resolution.
-/
theorem cartanEilenberg_doubleComplex_homotopy
    (C : Type u) [Category.{v} C] [Abelian C]
    (K L : CochainComplex C ℤ)
    (I J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      ⟶ I)
    (eJ : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ⟶ J)
    (hI : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hJ : ∀ p : ℤ, p < 0 → IsZero (J.X p))
    (hIres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map
        (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (hJres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map
        (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (hJinj : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (δ : I ⟶ J) (w : K ⟶ L)
    (s : ∀ p : ℤ, K.X p ⟶ L.X (p - 1))
    (hs : ∀ p : ℤ,
      w.f p = s p ≫ L.d (p - 1) p +
        K.d p (p + 1) ≫ s (p + 1) ≫ eqToHom (congrArg L.X (Int.add_sub_cancel p 1)))
    (hδ : ∀ p : ℤ, (eI.f p).f 0 ≫ (δ.f p).f 0 = w.f p ≫ (eJ.f p).f 0) :
    let E := (ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let I' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj I
    let J' : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj J
    ∃ (tI : I'.HasTotal (ComplexShape.up ℤ)) (tJ : J'.HasTotal (ComplexShape.up ℤ)),
      letI := tI
      letI := tJ
      ∃ (s1 : ∀ p q : ℤ, (I'.X p).X q ⟶ (J'.X (p - 1)).X q)
        (s2 : ∀ p q : ℤ, (I'.X p).X q ⟶ (J'.X p).X (q - 1)),
        (∀ p q : ℤ, p ≤ 0 ∨ q < 0 → s1 p q = 0) ∧
        (∀ p q : ℤ, p < 0 ∨ q ≤ 0 → s2 p q = 0) ∧
        (∀ p : ℤ,
          (eI.f p).f 0 ≫ ((I.X p).extendXIso ComplexShape.embeddingUpNat
            (i := 0) (i' := 0) rfl).inv ≫ s1 p 0 =
          s p ≫ (eJ.f (p - 1)).f 0 ≫ ((J.X (p - 1)).extendXIso
            ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv) ∧
        ∃ H : Homotopy (HomologicalComplex₂.total.map (E.map δ) (ComplexShape.up ℤ)) 0,
          (∀ (p q n : ℤ) (hpq : p + q = n),
            I'.ιTotal (ComplexShape.up ℤ) p q n hpq ≫ H.hom n (n - 1) =
              s1 p q ≫ J'.ιTotalOrZero (ComplexShape.up ℤ) (p - 1) q (n - 1) +
              p.negOnePow •
                (s2 p q ≫ J'.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) (n - 1))) ∧
          (∀ q n : ℤ,
            ∃ f : ((I'.secondFiltration n).step q : C) ⟶
              ((J'.secondFiltration (n - 1)).step (q - 1) : C),
              f ≫ ((J'.secondFiltration (n - 1)).step (q - 1)).arrow =
                ((I'.secondFiltration n).step q).arrow ≫ H.hom n (n - 1)) := by
  sorry

end CategoryTheory
