/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.FiniteJetSmoothGenericFibre
public import Sheaf.AlgebraicGeometry.IsolatedCurveFormalLifting
public import Sheaf.AlgebraicGeometry.ProperFormalCurveAlgebraization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.RingTheory.PresentationFittingIdeal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ToNat

/-! # Finite-jet Fitting bounds on pure pieces

Source: Stacks Project, Tag 0E7Y, first and last paragraphs.
(blueprint: lem-sfb-isolated-curve-local-fitting-bounds).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Local differential Fitting bounds at finitely many exceptional points extend to
the specified finite jet of each proper pure-dimensional open piece of an existing family.

Source: Stacks Project, Tag 0E7Y, final paragraph, using Algebra Tags 00OU, 00RT,
00RV, Divisors Tag 0C3K and More on Algebra Tag 07ZA.
(blueprint: lem-sfb-isolated-curve-local-fitting-bounds).

Proof: At a marked closed point of the pure d-dimensional special fibre, the
closed-point dimension formula and Zariski's lemma identify the index
of the given presentation ideal with d. Set n=ex+1, so n is positive and
n-1=ex. For the nth jet,
identify the marked stalk with B_i/(t^n) by the supplied scalar-compatible ring
equivalence. Differentials commute with this quotient base change and with stalk
localization. Presentation independence and base change of Fitting ideals
therefore carry the prescribed bound into the dth differential Fitting ideal
stalk; multiplication by the missing power gives t^(n-1). At any unmarked closed
point, flatness, finite presentation and the smooth special fibre imply smoothness
of the infinitesimal family. Its differentials are locally free of rank d, so
the dth Fitting ideal is the unit ideal. The quotient of the structure sheaf by
the Fitting ideal is coherent on this Noetherian jet. The image of the section
t^(n-1) has closed support containing no closed point, hence empty support.
Thus t^ex belongs to the ideal on the whole jet, as asserted by
idealOfOpens top. Restriction to an open piece preserves the marked stalk
comparisons, and points outside that piece need no bound. Empty pieces have
zero section rings; exponent zero and the empty list require no exception.
No Cohen--Macaulay partition, existence of a family, or generic smoothness is
asserted or used. -/
theorem isolated_curve_local_fitting_bounds
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (r : ℕ) (p : Fin r → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (hsmooth : ∀ x ∉ Set.range p, ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f))
    (B : Fin r → Type u) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)]
    [∀ i, Algebra (PowerSeries k) (B i)] [∀ i, Algebra k (B i)]
    [∀ i, IsScalarTower k (PowerSeries k) (B i)]
    [∀ i, Module.Flat (PowerSeries k) (B i)]
    [∀ i, Algebra.EssFiniteType (PowerSeries k) (B i)]
    (ex : ℕ) (m : Fin r → ℕ)
    (π : ∀ i, (Fin (m i) → B i) →ₗ[B i] KaehlerDifferential (PowerSeries k) (B i))
    (hπ : ∀ i, Function.Surjective (π i))
    (hbound : ∀ i,
      let : Algebra k (X.presheaf.stalk (p i)) :=
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
          X.presheaf.germ ⊤ (p i) trivial).hom.toAlgebra)
      (algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ ex ∈
        (π i).presentationFittingIdeal
          ((WithBot.unbotD 0 (ringKrullDim (X.presheaf.stalk (p i)))).toNat +
            (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk (p i)))).toNat))
    (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (PowerSeries k)))
    [Flat g] [LocallyOfFinitePresentation g] [IsHProjective g]
    (e : pullback g (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k)))) ≅ X)
    (he : e.hom ≫ f = pullback.snd g (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k)))))
    (j : ∀ n, X ⟶ pullback g (formalCurveBaseι k n))
    (hj : ∀ n, j n ≫ pullback.fst g (formalCurveBaseι k n) =
      e.inv ≫ pullback.fst g (Spec.map (CommRingCat.ofHom
        (PowerSeries.constantCoeff (R := k)))))
    (h : ∀ i n,
      (pullback g (formalCurveBaseι k n)).presheaf.stalk (j n (p i))
        ≃+* (B i ⧸ Ideal.span
          {(algebraMap (PowerSeries k) (B i) PowerSeries.X) ^ (n + 1)}))
    (hscalar : ∀ i n a, h i n (isolatedCurveScalarToStalk
      (pullback.snd g (formalCurveBaseι k n)) (j n (p i))
      (Ideal.Quotient.mk _ a)) = Ideal.Quotient.mk _ (algebraMap _ _ a))
    (U : Fin 2 → Y.Opens)
    (hproper : ∀ i, IsProper ((U i).ι ≫ g))
    (hpure : ∀ i, (pullback ((U i).ι ≫ g) (Spec.map (CommRingCat.ofHom
      (PowerSeries.constantCoeff (R := k))))).IsPureDimension i.val) :
    ∀ i,
        (pullback.snd ((U i).ι ≫ g) (Scheme.powerSeriesJetBaseMap k (ex + 1))).appTop
          ((Scheme.ΓSpecIso (.of ((PowerSeries k) ⧸
            Ideal.span {(PowerSeries.X : PowerSeries k) ^ (ex + 1)}))).inv
            (Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ ex))) ∈
        (Scheme.Modules.fittingIdealSheaf
          (pullback.snd ((U i).ι ≫ g)
            (Scheme.powerSeriesJetBaseMap k (ex + 1))).relativeDifferentials
          i.val).idealOfOpens ⊤ := by
  sorry

end AlgebraicGeometry
