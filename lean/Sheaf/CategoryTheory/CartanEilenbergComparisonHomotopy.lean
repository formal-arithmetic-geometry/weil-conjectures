/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy

/-!
# Homotopy uniqueness of Cartan--Eilenberg comparison lifts

Source: Stacks Project, Derived Categories, Tags 015I and 015K
(blueprint: lem-sp-cartan-eilenberg-comparison-homotopy).

Resolutions use the augmentation and resolution fields of
`exists_cartanEilenberg_resolution`. Extend the natural resolution index by zero
before forming total complexes. The filtration is by the second, resolution index.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Comparison lifts of homotopic complex maps have a total homotopy lowering
resolution degree by at most one.
Source: Stacks Project, Derived Categories, Tags 015I and 015K
(blueprint: lem-sp-cartan-eilenberg-comparison-homotopy).

Proof:
1. Set delta = phi - psi. The augmentation identities imply that delta lifts
   u - u', whose null-homotopy is the given s (Homotopy.equivSubZero).
2. Exactness of F preserves the augmented boundary, cycle and cohomology
   resolutions of I and their canonical short exact sequences. The corresponding
   resolutions of J have injective terms, by lem-sp-cartan-eilenberg-exists.
   Apply lem-sp-cartan-eilenberg-double-complex-homotopy to delta and s.
3. Its horizontal component s1 restricts to s on the augmentation; its vertical
   component s2 supplies the residual null-homotopy.
4. On each summand set H = s1 + (-1)^p s2. The component equations give
   Tot(phi) - Tot(psi) = dH + Hd. The horizontal component preserves resolution
   degree and the vertical component lowers it by one, so their sum factors
   through the second filtration step q-1 in degree n-1
   (def-sp-double-complex-total, def-sp-filtration).
When u = u', take Homotopy.ofEq of this equality, whose components are zero.
The same conclusion gives the final assertion without an additional hypothesis.
-/
theorem cartanEilenberg_comparison_homotopy
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p))
    (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p))
    (u u' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ L)
    (s : Homotopy u u')
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (hIbelow : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hIcol : ∀ p : ℤ, QuasiIso (eI.f p))
    (hIinj : ∀ (p : ℤ) (q : ℕ), Injective ((I.X p).X q))
    (hIinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((I.cycles p).X q) ∧
      Injective ((image (I.d (p - 1) p)).X q) ∧
      Injective ((I.homology p).X q))
    (hIres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (J : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eJ : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (hJbelow : ∀ p : ℤ, p < 0 → IsZero (J.X p))
    (hJcol : ∀ p : ℤ, QuasiIso (eJ.f p))
    (hJinj : ∀ (p : ℤ) (q : ℕ), Injective ((J.X p).X q))
    (hJinj' : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (hJres : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p)) :
    let FI : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ) :=
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I
    let E := (ComplexShape.embeddingUpNat.extendFunctor B).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let FIZ : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj FI
    let JZ : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) := E.obj J
    ∀ (φ ψ : FI ⟶ J),
      (∀ p : ℤ,
        F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
            (eI.f p).f 0) ≫ (φ.f p).f 0 =
          u.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
            (eJ.f p).f 0) →
      (∀ p : ℤ,
        F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X p)).inv ≫
            (eI.f p).f 0) ≫ (ψ.f p).f 0 =
          u'.f p ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.X p)).inv ≫
            (eJ.f p).f 0) →
      ∃ (tI : FIZ.HasTotal (ComplexShape.up ℤ)) (tJ : JZ.HasTotal (ComplexShape.up ℤ)),
        letI := tI
        letI := tJ
        ∃ H : Homotopy
          (HomologicalComplex₂.total.map (E.map φ) (ComplexShape.up ℤ))
          (HomologicalComplex₂.total.map (E.map ψ) (ComplexShape.up ℤ)),
          ∀ q n : ℤ,
            ∃ f : ((FIZ.secondFiltration n).step q : B) ⟶
              ((JZ.secondFiltration (n - 1)).step (q - 1) : B),
              f ≫ ((JZ.secondFiltration (n - 1)).step (q - 1)).arrow =
                ((FIZ.secondFiltration n).step q).arrow ≫ H.hom n (n - 1) := by
  sorry

end CategoryTheory
