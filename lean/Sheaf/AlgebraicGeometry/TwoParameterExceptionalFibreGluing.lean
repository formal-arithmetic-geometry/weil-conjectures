/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q140 stage 2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Blowup.Affine.Defs
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts

/-!
# Gluing the exceptional fibre of a two-parameter blowup

Source: Stacks Project, Tags 0AGQ, 0BIQ, 01M4, 01NG and 00OQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing).

The auxiliary constructions name the actual quotient, global blowup fibre, and
homogeneous chart coordinates. The two indices are 0 (x-chart) and 1 (y-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The ideal of the two parameters. Source: Stacks, Tag 0BIQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
def twoParameterIdeal {A : Type u} [CommRing A] (x y : A) : Ideal A :=
  Ideal.span {x, y}

/-- The literal quotient by the parameter ideal. Source: Stacks, Tags 0BIQ and 0AGQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
abbrev TwoParameterQuotient {A : Type u} [CommRing A] (x y : A) :=
  A ⧸ twoParameterIdeal x y

/-- The centre as a closed subscheme of the affine base. Source: Stacks, Tag 0AGQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterCenter {A : Type u} [CommRing A] (x y : A) :
    (Spec (.of A)).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (twoParameterIdeal x y)))).ker

/-- The exceptional fibre is the scheme-theoretic pullback, with no reduction.
Source: Stacks, Tag 0AGQ (blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterExceptional {A : Type u} [CommRing A] (x y : A) :
    Scheme.{u} :=
  pullback (twoParameterCenter x y).blowupMap
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (twoParameterIdeal x y))))

/-- Its canonical map to the blowup. Source: Stacks, Tag 0AGQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterExceptionalι {A : Type u} [CommRing A] (x y : A) :
    twoParameterExceptional x y ⟶ (twoParameterCenter x y).blowup :=
  pullback.fst _ _

/-- Its canonical map to the quotient spectrum. Source: Stacks, Tag 0AGQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterExceptionalBase {A : Type u} [CommRing A] (x y : A) :
    twoParameterExceptional x y ⟶ Spec (.of (TwoParameterQuotient x y)) :=
  pullback.snd _ _

/-- The homogeneous degree-one parameter, in the order x,y. Source: Stacks, Tag 0BIQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterRees {A : Type u} [CommRing A] (x y : A) (i : Fin 2) :
    reesAlgebra (twoParameterIdeal x y) :=
  reesX (twoParameterIdeal x y) (![x, y] i)
    (by fin_cases i <;> exact Ideal.subset_span (by simp))

/-- The degree-zero homogeneous localization for either chart. Source: Stacks, Tag 0BIQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
abbrev TwoParameterChartRing {A : Type u} [CommRing A] (x y : A) (i : Fin 2) :=
  HomogeneousLocalization.Away (reesGrading (twoParameterIdeal x y)) (twoParameterRees x y i)

/-- The actual homogeneous fraction yT/xT or xT/yT. Source: Stacks, Tags 0BIQ and 01M4
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterRatio {A : Type u} [CommRing A] (x y : A) (i : Fin 2) :
    TwoParameterChartRing x y i :=
  HomogeneousLocalization.Away.mk (reesGrading (twoParameterIdeal x y))
    (d := 1) (by apply reesX_mem) 1 (twoParameterRees x y (![1, 0] i))
    (by change twoParameterRees x y (![1, 0] i) ∈ reesGrading _ 1; apply reesX_mem)

/-- The canonical affine chart morphism of the Rees Proj. Source: Stacks, Tags 0BIQ and 01M4
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterChart {A : Type u} [CommRing A] (x y : A) (i : Fin 2) :
    Spec (.of (TwoParameterChartRing x y i)) ⟶ AffineBlowup (twoParameterIdeal x y) :=
  AffineBlowup.chart _ (twoParameterRees x y i) (by apply reesX_mem)

/-- The standard open in the existing base-change projective line. Source: Stacks, Tag 01NG
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterProjectiveOpen (k : Type u) [CommRing k] (i : Fin 2) :
    (ProjectiveLine (Spec (.of k))).Opens :=
  ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) (ULift.up i)

/-- The ratio T_1/T_0 or T_0/T_1 on the standard projective-line chart, using the
published canonical chart isomorphism. Source: Stacks, Tag 01NG
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing). -/
noncomputable def twoParameterProjectiveRatio (k : Type u) [CommRing k] (i : Fin 2) :
    Γ((twoParameterProjectiveOpen k i).toScheme, ⊤) :=
  (ProjectiveSpace.standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) (ULift.up i)).hom.appTop
    (AffineSpace.coord (Spec (.of k))
      ⟨ULift.up (![1, 0] i), by fin_cases i <;> decide⟩)

/-- The exceptional fibre has its canonical two affine-line charts, with reciprocal
coordinate transition, and these glue with their inverses to the projective line over
A/(x,y). Its stalks are the prime localizations of the displayed polynomial chart rings,
and the fibre is regular.

Source: Stacks Project, Tags 0AGQ, 0BIQ, 01M4, 01NG, 01JA and 00OQ
(blueprint: lem-sfb-two-parameter-exceptional-fibre-gluing).

Proof plan:
1. Use lem-sfb-two-parameter-blowup-atlas for both ordered regular sequences. The two
   Rees charts cover the global blowup and have presentations A[t]/(xt-y), A[u]/(yu-x).
2. Use lem-weil-pbc-open-fibre-product and lem-weil-pbc-fibre-product-affine-spectra.
   Tensor the presentations with k=A/(x,y). Reduction sends [f] tensor a to a*f_bar;
   its inverse sends coefficients to 1 tensor a and the variable to [t] tensor 1.
   These mutually inverse coefficient-fixing maps give the scheme-theoretic fibre charts.
3. Use lem-weil-pbc-proj-basic-open-intersection and
   lem-weil-pbc-affine-open-section-vanishing-prime. The overlap is D(t)=D(u), and its
   ring is k[t,t^-1]. The homogeneous fractions in
   def-nagata-homogeneous-localization-degree-zero multiply to one, so u=t^-1.
4. Use lem-weil-pbc-projective-space-standard-charts and the same overlap calculation.
   The coefficient-fixing maps t to T_1/T_0 and u to T_0/T_1 commute on the overlap,
   as do their inverse maps, since either composite fixes coefficients and the variable.
5. Apply lem-weil-pbc-scheme-morphism-gluing to these maps and their inverses. Uniqueness
   makes both composites identities and makes both maps morphisms over Spec k.
6. By lem-sc-p1-polynomial-regular, k[t] and k[u] are regular rings. By
   lem-weil-pbc-affine-open-stalk-localization every stalk is its corresponding prime
   localization, including the zero prime. Thus def-weil-regular-scheme applies.
-/
theorem twoParameterExceptionalFibreGluing
    {A : Type u} [CommRing A] [IsNoetherianRing A] (x y : A)
    (hxy : RingTheory.Sequence.IsRegular A [x, y])
    (hyx : RingTheory.Sequence.IsRegular A [y, x])
    [(twoParameterIdeal x y).IsMaximal] :
    ∃ (b : AffineBlowup (twoParameterIdeal x y) ≅ (twoParameterCenter x y).blowup)
      (a : Fin 2 → (Spec (.of (Polynomial (TwoParameterQuotient x y))) ⟶
        twoParameterExceptional x y))
      (r : ∀ i : Fin 2, TwoParameterChartRing x y i →+*
        Polynomial (TwoParameterQuotient x y))
      (c : ∀ i : Fin 2, Spec (.of (Polynomial (TwoParameterQuotient x y))) ≅
        (twoParameterProjectiveOpen (TwoParameterQuotient x y) i).toScheme)
      (e : twoParameterExceptional x y ≅
        ProjectiveLine (Spec (.of (TwoParameterQuotient x y)))),
      b.hom ≫ (twoParameterCenter x y).blowupMap =
        AffineBlowup.toSpec (twoParameterIdeal x y) ∧
      (∀ i : Fin 2, IsOpenImmersion (a i) ∧
        Set.range (a i) =
          ((twoParameterExceptionalι x y) ⁻¹ᵁ (b.inv ⁻¹ᵁ
            Proj.basicOpen (reesGrading (twoParameterIdeal x y))
              (twoParameterRees x y i)) : Set (twoParameterExceptional x y)) ∧
        a i ≫ twoParameterExceptionalι x y =
          Spec.map (CommRingCat.ofHom (r i)) ≫ twoParameterChart x y i ≫ b.hom ∧
        a i ≫ twoParameterExceptionalBase x y =
          Spec.map (CommRingCat.ofHom Polynomial.C) ∧
        (∀ z : A, r i (AffineBlowup.awayAlgebraMap _ (twoParameterRees x y i) z) =
          Polynomial.C (Ideal.Quotient.mk (twoParameterIdeal x y) z)) ∧
        r i (twoParameterRatio x y i) = Polynomial.X ∧
        (c i).hom.appTop (twoParameterProjectiveRatio (TwoParameterQuotient x y) i) =
          (Scheme.ΓSpecIso (.of (Polynomial (TwoParameterQuotient x y)))).inv Polynomial.X ∧
        (c i).hom ≫ (twoParameterProjectiveOpen (TwoParameterQuotient x y) i).ι ≫
            (ProjectiveLine (Spec (.of (TwoParameterQuotient x y))) ↘
              Spec (.of (TwoParameterQuotient x y))) =
          Spec.map (CommRingCat.ofHom Polynomial.C) ∧
        a i ≫ e.hom =
          (c i).hom ≫ (twoParameterProjectiveOpen (TwoParameterQuotient x y) i).ι ∧
        (c i).inv ≫ a i =
          (twoParameterProjectiveOpen (TwoParameterQuotient x y) i).ι ≫ e.inv ∧
        (∀ p : PrimeSpectrum (Polynomial (TwoParameterQuotient x y)),
          Nonempty (((twoParameterExceptional x y).presheaf.stalk (a i p)) ≃+*
            Localization.AtPrime p.asIdeal) ∧
          IsRegularLocalRing ((twoParameterExceptional x y).presheaf.stalk (a i p)))) ∧
      Set.range (a 0) ∪ Set.range (a 1) = Set.univ ∧
      (a 0) ⁻¹ᵁ ((twoParameterExceptionalι x y) ⁻¹ᵁ (b.inv ⁻¹ᵁ
          Proj.basicOpen (reesGrading (twoParameterIdeal x y)) (twoParameterRees x y 1))) =
        PrimeSpectrum.basicOpen (Polynomial.X : Polynomial (TwoParameterQuotient x y)) ∧
      (a 1) ⁻¹ᵁ ((twoParameterExceptionalι x y) ⁻¹ᵁ (b.inv ⁻¹ᵁ
          Proj.basicOpen (reesGrading (twoParameterIdeal x y)) (twoParameterRees x y 0))) =
        PrimeSpectrum.basicOpen (Polynomial.X : Polynomial (TwoParameterQuotient x y)) ∧
      (∃ d : Spec (.of (LaurentPolynomial (TwoParameterQuotient x y))) ≅
          pullback (a 0) (a 1),
        d.hom ≫ pullback.fst (a 0) (a 1) =
          Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom LaurentPolynomial.C
            (LaurentPolynomial.T 1))) ∧
        d.hom ≫ pullback.snd (a 0) (a 1) =
          Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom LaurentPolynomial.C
            (LaurentPolynomial.T (-1))))) ∧
      e.hom ≫ (ProjectiveLine (Spec (.of (TwoParameterQuotient x y))) ↘
        Spec (.of (TwoParameterQuotient x y))) = twoParameterExceptionalBase x y ∧
      IsRegularScheme (twoParameterExceptional x y) := by
  sorry

end AlgebraicGeometry
