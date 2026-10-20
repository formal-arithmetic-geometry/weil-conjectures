/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import WeilConjectures.CategoryTheory.CartanEilenbergExists
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.CategoryTheory.CartanEilenbergVerticalNullhomotopy
import Sheaf.CategoryTheory.HorizontalComparisonLift

/-! Component construction for Cartan--Eilenberg comparison homotopies.
(blueprint: lem-sp-cartan-eilenberg-double-complex-homotopy-components)
-/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
/-- Horizontal and vertical components of the Cartan--Eilenberg comparison homotopy,
before the separate second-filtration factorization.
Source: Stacks Project, Tags 015I and 015K; Weibel, Homological Algebra, Lemma 5.7.10.
(blueprint: lem-sp-cartan-eilenberg-double-complex-homotopy-components)

Proof:
1. First derive the column hypotheses of horizontal_comparison_lift. The canonical
   short exact sequences 0 -> Z_I^p -> I^{p,*} -> B_I^{p+1} -> 0, and the
   corresponding sequences for the single-degree source, are natural in eI.
   Their outer augmentation maps are quasi-isomorphisms by hIres (use the
   boundary hypothesis at p+1). The homology long exact sequence gives a
   quasi-isomorphism on the middle column. For J, evaluate the same short exact
   sequence in each vertical degree. Its first and third terms are injective
   by hJinj, so the sequence splits and its middle term is injective.
   Apply horizontal_comparison_lift with these column facts and the given row
   hypotheses. It gives column maps s1 with the prescribed augmentation identity.
   The residual R = delta - d_h s1 - s1 d_h vanishes on the augmentation.
2. The residual commutes with d_h: both d_h (d_h s1 + s1 d_h) and
   (d_h s1 + s1 d_h) d_h equal d_h s1 d_h, since d_h squared is zero.
   It commutes with d_v because delta and s1 do. Apply the vertical null-homotopy
   theorem to the boundary, cycle and horizontal-cohomology row resolutions.
   Assembly through the exact sequences gives s2, zero in vertical degree zero,
   with R = d_v s2 + s2 d_v and s2 d_h = d_h s2.
3. On a diagonal summand set H = s1 + (-1)^p s2. Expand the total differential
   d_Tot = d_h + (-1)^p d_v. The component returning to bidegree (p,q) is
   d_h s1 + s1 d_h + d_v s2 + s2 d_v = delta by the definition of R.
   The terms landing in (p+1,q-1) cancel by s2 d_h = d_h s2; those landing in
   (p-1,q+1) cancel by s1 d_v = d_v s1. Thus d_Tot H + H d_Tot = delta.
4. Extend the vertical natural index by zero and transport both components along
   the extension isomorphisms in nonnegative degrees. First-quadrant vanishing
   makes every total diagonal a finite coproduct. Its universal property constructs
   H from the component formula, and step 3 verifies its homotopy identity on every
   inclusion. For s1 the target is zero when p <= 0 and the source when q < 0;
   for s2 the source is zero when p < 0 and the target when q <= 0. This proves
   the stated vanishing conditions. Transport in degree zero preserves the
   augmentation identity from step 1.
-/
theorem cartanEilenberg_doubleComplex_homotopy_components
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
                (s2 p q ≫ J'.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) (n - 1)))
 := by
  sorry

end CategoryTheory
