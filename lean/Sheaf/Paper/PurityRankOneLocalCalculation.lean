/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneSectionData
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Sheaf.Paper.PurityRankOneEtaleCalculation
import Sheaf.Paper.PurityAcyclicPairSupportComparison
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# The finite rank-one Kummer residue

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`thm-pur-rank-one-local-calculation` (blueprint: thm-pur-rank-one-local-calculation).

The boundary below is specified by the snake boundary of the actual section complexes
of every injective resolution. In particular its sign is fixed. Module-valued derived
sections retain the coefficient action, so the normalization and its uniqueness are linear.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.RankOne

private theorem normalized_iso_unique {A : Type (u + 1)} [CommRing A]
    {H : ModuleCat.{u + 1} A} (e : H ≅ ModuleCat.of A A) (x : H)
    (hx : e.hom x = 1) (r : H ≅ ModuleCat.of A A) (hr : r.hom x = 1) : r = e := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hy : y = (e.hom y) • x := by
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    simp [hx]
  rw [hy]
  simp [hx, hr]

private theorem polynomial_value_one (Ω : Type u) [Field Ω]
    (a : Polynomial Ω) (ha : a.eval 0 ≠ 0) :
    (Polynomial.idealX Ω).intValuation a = 1 := by
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
  change a ∉ Ideal.span {Polynomial.X}
  simpa [Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_eval_zero] using ha

private theorem quotient_value_one (Ω : Type u) [Field Ω]
    (a b : Polynomial Ω) (ha : a.eval 0 ≠ 0) (hb : b.eval 0 ≠ 0) :
    (Polynomial.idealX Ω).valuation (RatFunc Ω) (RatFunc.mk a b) = 1 := by
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  rw [Polynomial.valuation_of_mk (K := Ω) a hb0, polynomial_value_one Ω a ha,
    polynomial_value_one Ω b hb, div_self one_ne_zero]

private theorem monomial_value (Ω : Type u) [Field Ω] (c : Ωˣ) (r : ℤ) :
    (Polynomial.idealX Ω).valuation (RatFunc Ω)
      (RatFunc.C (c : Ω) * (RatFunc.X : RatFunc Ω) ^ r) = WithZero.exp (-r) := by
  have hc : (Polynomial.idealX Ω).valuation (RatFunc Ω) (RatFunc.C (c : Ω)) = 1 := by
    rw [← RatFunc.algebraMap_C,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact polynomial_value_one Ω _ (by simp)
  rw [map_mul, hc, one_mul, map_zpow₀, Polynomial.valuation_X_eq_neg_one]
  simp

/-- Finite rank-one local purity, including the coefficient-linear normalization,
residues, all other support degrees, and the actual comparison to the pro-etale site.
Neither the construction nor its normalization contains a primitive-root choice.
The exponent r in the unit decomposition is ord_0: the exponent of the uniformizer t
in Omega(t), with t of order one and local-ring units of order zero.

Source: Milne, Lectures on Etale Cohomology, Section 14, Proposition 14.3 and
Example 16.3; blueprint main-20261015, sk-prop-a1-kummer
(blueprint: thm-pur-rank-one-local-calculation).

Proof plan:
1. A temporary primitive root identifies mu_(ell^N) with the constant Z/ell^N line.
   Connectedness gives H0(X,M)=H0(U,M)=M with identity restriction.
   Use lem-sc-primitive-root, def-sc-mu-trivialization, and
   lem-weil-pbc-constant-sheaf-sections-connected.
2. Define tau_M(a) as the image of delta_N(t) under z mapping to z tensor a.
   It is linear and natural. Kummer exactness and affine/punctured-line unit and Picard
   computations give the result for F_ell, with level compatibility of Kummer classes.
   Use lem-asd-etale-finite-twist-pullback, lem-sc-kummer-exact, and
   thm-pur-kummer-affine-line. The power map z mapping to z^(ell^(N-1)) carries the
   level-N Kummer class to the level-one class. Connecting-map naturality is supplied by
   lem-weil-pbc-right-derived-universal-delta-functor on the small skeleton of
   def-weil-size-convention, with lem-weil-pbc-site-sheaves-enough-injectives.
3. Devissage through a simple submodule and its quotient, using sheafification exactness
   and the coefficient long exact sequence, proves H1(U,M)=M, higher U vanishing, and
   positive X vanishing. No freeness over Z/ell^N is assumed.
   Use lem-weil-pbc-sheafification-exact and
   lem-weil-pbc-pullback-cohomology-long-exact-ladder. For nonzero M, an element of
   least positive ell-power order supplies a copy C of F_ell. For Q=M/C, the induction
   hypotheses give the higher vanishings and short exactness of the H1 sequence on U:
   the H0 map M to Q is surjective and H2(U,C(1)) vanishes. Naturality of tau gives a
   map from 0 to C to M to Q to 0 to this sequence. Its outer maps are isomorphisms,
   so lifting a Q-label and then a C-label proves surjectivity, and the same sequence
   proves injectivity. For M=A, tau_A(a)=a*kappa_A(t), hence tau_A is A-linear.
4. On each injective resolution restriction is surjective termwise; its kernel is the
   supported section complex. The snake sequence and Step 1 identify its actual boundary
   as an isomorphism H1(U,A(1)) to H2_Z(X,A(1)), with all other support groups zero.
   Its composite with tau_A is A-linear; its inverse is rho. Since tau_A(1)=kappa_A(t),
   A-linearity proves uniqueness of the normalized rho.
   Use thm-pur-with-support-exactness. In degrees zero and one, identity restriction
   gives vanishing; in degrees at least three, the adjacent ordinary groups vanish.
5. Every unit on U is c*t^r. Algebraic closedness makes c an ell^N-th power, so
   kappa_A(c*t^r)=r*kappa_A(t). The t-adic valuation gives ord_0(c*t^r)=r.
   Use lem-pur-affine-punctured-line-algebra and lem-sc-kummer-exact. Factoring out
   the largest t-power from a polynomial and subtracting for a quotient gives order;
   numerators and denominators nonzero at zero both have order zero.
6. The defining tensor map, Kummer extension, and snake boundary are canonical;
   hence rho is independent of the temporary primitive root.
7. Finite etale/pro-etale comparison is induced by the inverse-image unit on sections.
   It commutes with restriction and with the snake boundary. Both boundaries are
   isomorphisms, so their square determines the support comparison. The normalized
   pro-etale rho is its transported inverse and has the same residue formula.
   Use lem-weil-pbc-comparison-global-cohomology, lem-weil-pbc-comparison-pullback,
   and thm-pur-with-support-exactness. The inverse-image Kummer class is the image
   under ordinary comparison. Every other support degree vanishes by the same sequence.
-/
theorem rankOne_local_calculation (P : PurityFiniteSetting.{u})
    (N : ℕ) (hN : 1 ≤ N) (hA : ((P.coefficients.l ^ N : ℕ) : P.Coefficient) = 0)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (CommRingCat.of P.field.k))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (hy : y ≫ aY = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) :
    ∃ (hm : IsUnit (((P.coefficients.l ^ N : ℕ)) : Γ((Line (Spec (CommRingCat.of Ω))), ⊤)))
      (f : (Line (Spec (CommRingCat.of Ω))).rootsOfUnitySheaf ((P.coefficients.l ^ N : ℕ)) ⟶
        (Etale.moduleAbelianForget (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))).obj
        (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec
        (CommRingCat.of Ω))) hA 1)),
      (∀ (V : (Line (Spec (CommRingCat.of Ω))).Etaleᵒᵖ) (z : ((Line (Spec (CommRingCat.of
        Ω))).rootsOfUnitySheaf ((P.coefficients.l ^ N : ℕ))).obj.obj V),
        f.hom.app V z = Scheme.finiteEtaleTateOneGenerator (P.Coefficient) ((P.coefficients.l ^ N :
          ℕ)) (Line (Spec (CommRingCat.of Ω))) hA V 1 z) ∧
      ∃ (δet : ((sections (Line (Spec (CommRingCat.of Ω))).smallEtaleTopology (P.Coefficient)
        (openObject (Spec (CommRingCat.of Ω)))).rightDerived 1).obj (Scheme.finiteEtaleTateSheaf
        (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) ⟶
        (((Sheaf.supportedSectionsFunctor (Line (Spec (CommRingCat.of Ω))).smallEtaleTopology
        (ModuleCat.{u + 1} (P.Coefficient)) (restriction (Spec (CommRingCat.of Ω)))).rightDerived
        2).obj (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec
        (CommRingCat.of Ω))) hA 1)))
        (δpro : ((sections (Scheme.ProEt.topology (Line (Spec (CommRingCat.of Ω)))) (P.Coefficient)
          ((Scheme.toProEt (Line (Spec (CommRingCat.of Ω)))).obj (openObject (Spec (CommRingCat.of
            Ω))))).rightDerived 1).obj (proCoefficient (P.Coefficient) (Line (Spec (CommRingCat.of
            Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line
            (Spec (CommRingCat.of Ω))) hA 1)) ⟶ (((Sheaf.supportedSectionsFunctor
            (Scheme.ProEt.topology (Line (Spec (CommRingCat.of Ω)))) (ModuleCat.{u + 1}
            (P.Coefficient)) ((Scheme.toProEt (Line (Spec (CommRingCat.of Ω)))).map (restriction
            (Spec (CommRingCat.of Ω))))).rightDerived 2).obj (proCoefficient (P.Coefficient) (Line
            (Spec (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient)
            ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)))),
        IsBoundary (Line (Spec (CommRingCat.of Ω))).smallEtaleTopology (P.Coefficient) (restriction
          (Spec (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l
          ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) δet ∧
        IsBoundary (Scheme.ProEt.topology (Line (Spec (CommRingCat.of Ω)))) (P.Coefficient)
          ((Scheme.toProEt (Line (Spec (CommRingCat.of Ω)))).map (restriction (Spec (CommRingCat.of
          Ω)))) (proCoefficient (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))
          (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec
          (CommRingCat.of Ω))) hA 1)) δpro ∧
        IsIso δet ∧ IsIso δpro ∧
        IsIso ((comparisonCohomology (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (openObject
          (Spec (CommRingCat.of Ω))) 1).app (Scheme.finiteEtaleTateSheaf (P.Coefficient)
          ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)) ∧
        ∃ (ρet : (((Sheaf.supportedSectionsFunctor (Line (Spec (CommRingCat.of
          Ω))).smallEtaleTopology (ModuleCat.{u + 1} (P.Coefficient)) (restriction (Spec
          (CommRingCat.of Ω)))).rightDerived 2).obj (Scheme.finiteEtaleTateSheaf (P.Coefficient)
          ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)) ≅ ModuleCat.of
          (P.Coefficient) (P.Coefficient)) (ρpro : (((Sheaf.supportedSectionsFunctor
          (Scheme.ProEt.topology (Line (Spec (CommRingCat.of Ω)))) (ModuleCat.{u + 1}
          (P.Coefficient)) ((Scheme.toProEt (Line (Spec (CommRingCat.of Ω)))).map (restriction (Spec
          (CommRingCat.of Ω))))).rightDerived 2).obj (proCoefficient (P.Coefficient) (Line (Spec
          (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N :
          ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1))) ≅ ModuleCat.of (P.Coefficient)
          (P.Coefficient))
          (cZ : (((Sheaf.supportedSectionsFunctor (Line (Spec (CommRingCat.of
            Ω))).smallEtaleTopology (ModuleCat.{u + 1} (P.Coefficient)) (restriction (Spec
            (CommRingCat.of Ω)))).rightDerived 2).obj (Scheme.finiteEtaleTateSheaf (P.Coefficient)
            ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)) ≅
            (((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology (Line (Spec (CommRingCat.of
            Ω)))) (ModuleCat.{u + 1} (P.Coefficient)) ((Scheme.toProEt (Line (Spec (CommRingCat.of
            Ω)))).map (restriction (Spec (CommRingCat.of Ω))))).rightDerived 2).obj (proCoefficient
            (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf
            (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)))),
          ρet.hom (δet ((kummerClass (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (openObject
            (Spec (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient)
            ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) ((P.coefficients.l ^
            N : ℕ)) hm f) (coordinateUnit (Spec (CommRingCat.of Ω))))) = 1 ∧
          ρpro.hom (δpro (((comparisonCohomology (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))
            (openObject (Spec (CommRingCat.of Ω))) 1).app (Scheme.finiteEtaleTateSheaf
            (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1))
            ((kummerClass (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (openObject (Spec
            (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N
            : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) ((P.coefficients.l ^ N : ℕ)) hm f)
            (coordinateUnit (Spec (CommRingCat.of Ω)))))) = 1 ∧
          (∀ ρ : (((Sheaf.supportedSectionsFunctor (Line (Spec (CommRingCat.of
            Ω))).smallEtaleTopology (ModuleCat.{u + 1} (P.Coefficient)) (restriction (Spec
            (CommRingCat.of Ω)))).rightDerived 2).obj (Scheme.finiteEtaleTateSheaf (P.Coefficient)
            ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)) ≅ ModuleCat.of
            (P.Coefficient) (P.Coefficient),
            ρ.hom (δet ((kummerClass (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (openObject
              (Spec (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient)
              ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) ((P.coefficients.l
              ^ N : ℕ)) hm f) (coordinateUnit (Spec (CommRingCat.of Ω))))) = 1 → ρ = ρet) ∧
          (∀ ρ : (((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology (Line (Spec
            (CommRingCat.of Ω)))) (ModuleCat.{u + 1} (P.Coefficient)) ((Scheme.toProEt (Line (Spec
            (CommRingCat.of Ω)))).map (restriction (Spec (CommRingCat.of Ω))))).rightDerived 2).obj
            (proCoefficient (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))
            (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec
            (CommRingCat.of Ω))) hA 1))) ≅ ModuleCat.of (P.Coefficient) (P.Coefficient),
            ρ.hom (δpro (((comparisonCohomology (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))
              (openObject (Spec (CommRingCat.of Ω))) 1).app (Scheme.finiteEtaleTateSheaf
              (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1))
              ((kummerClass (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (openObject (Spec
              (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^
              N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) ((P.coefficients.l ^ N : ℕ)) hm f)
              (coordinateUnit (Spec (CommRingCat.of Ω)))))) = 1 → ρ = ρpro) ∧
          δet ≫ cZ.hom = ((comparisonCohomology (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))
            (openObject (Spec (CommRingCat.of Ω))) 1).app (Scheme.finiteEtaleTateSheaf
            (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)) ≫
            δpro ∧ cZ.hom ≫ ρpro.hom = ρet.hom ∧
          (∀ q : ℕ, q ≠ 2 →
            IsZero (((Sheaf.supportedSectionsFunctor (Line (Spec (CommRingCat.of
              Ω))).smallEtaleTopology
              (ModuleCat.{u + 1} (P.Coefficient)) (restriction (Spec (CommRingCat.of
                Ω)))).rightDerived q).obj (Scheme.finiteEtaleTateSheaf (P.Coefficient)
                ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1)) ∧
            IsZero (((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology (Line (Spec
              (CommRingCat.of Ω))))
              (ModuleCat.{u + 1} (P.Coefficient)) ((Scheme.toProEt (Line (Spec (CommRingCat.of
                Ω)))).map (restriction (Spec (CommRingCat.of Ω))))).rightDerived q).obj
                (proCoefficient (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))
                (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line
                (Spec (CommRingCat.of Ω))) hA 1)))) ∧
          (∀ v : Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤)ˣ,
            ∃ (c : Ωˣ) (r : ℤ), v = constantUnit Ω c * coordinateUnit (Spec (CommRingCat.of Ω)) ^ r)
              ∧
          (∀ (a b : Polynomial Ω), a.eval 0 ≠ 0 → b.eval 0 ≠ 0 →
            (Polynomial.idealX Ω).valuation (RatFunc Ω) (RatFunc.mk a b) = 1) ∧
          (∀ (c : Ωˣ) (r : ℤ),
            (Polynomial.idealX Ω).valuation (RatFunc Ω)
              (RatFunc.C (c : Ω) * (RatFunc.X : RatFunc Ω) ^ r) =
                WithZero.exp (-r) ∧
            ρet.hom (δet ((kummerClass (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (openObject
              (Spec (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient)
              ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) ((P.coefficients.l
              ^ N : ℕ)) hm f) (constantUnit Ω c * coordinateUnit (Spec (CommRingCat.of Ω)) ^ r))) =
              r • (1 : (P.Coefficient)) ∧
            ρpro.hom (δpro (((comparisonCohomology (P.Coefficient) (Line (Spec (CommRingCat.of Ω)))
              (openObject (Spec (CommRingCat.of Ω))) 1).app (Scheme.finiteEtaleTateSheaf
              (P.Coefficient) ((P.coefficients.l ^ N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1))
              ((kummerClass (P.Coefficient) (Line (Spec (CommRingCat.of Ω))) (openObject (Spec
              (CommRingCat.of Ω))) (Scheme.finiteEtaleTateSheaf (P.Coefficient) ((P.coefficients.l ^
              N : ℕ)) (Line (Spec (CommRingCat.of Ω))) hA 1) ((P.coefficients.l ^ N : ℕ)) hm f)
              (constantUnit Ω c * coordinateUnit (Spec (CommRingCat.of Ω)) ^ r)))) =
              r • (1 : (P.Coefficient))) := by
  have _ := hy
  let S := Spec (CommRingCat.of Ω)
  let X := Line S
  let F := Scheme.finiteEtaleTateSheaf P.Coefficient (P.coefficients.l ^ N) X hA 1
  obtain ⟨hm, f, hf, e, he, hX, hU, hres, hunits, hmon⟩ :=
    rankOne_etale_calculation P N hN hA Ω
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  have : Mono (restriction S) := by
    constructor
    intro T g h hgh
    apply MorphismProperty.Over.Hom.ext
    exact (cancel_mono (openImmersion S)).mp
      (congrArg (fun a ↦ a.left) hgh)
  obtain ⟨δ, δp, hδ, hδp, hδiso, hδpiso, hc, c, hsquare, hz⟩ :=
    acyclic_pair_support_comparison P.Coefficient X (openObject S) (restriction S) F hX hU hres
  let := hδiso
  let := hδpiso
  let := hc
  let cU := (comparisonCohomology P.Coefficient X (openObject S) 1).app F
  let ρ := (asIso δ).symm ≪≫ e
  let ρp := c.symm ≪≫ ρ
  let k := kummerClass P.Coefficient X (openObject S) F (P.coefficients.l ^ N) hm f
  have hnorm : ρ.hom (δ (k (coordinateUnit S))) = 1 := by
    change e.hom ((asIso δ).inv (δ (k (coordinateUnit S)))) = 1
    simpa using he
  have htransport : cU ≫ δp ≫ ρp.hom = δ ≫ ρ.hom := by
    rw [← Category.assoc, ← hsquare]
    simp [ρp]
  have hnormp : ρp.hom (δp (cU (k (coordinateUnit S)))) = 1 := by
    have h := congrArg (fun g ↦ g (k (coordinateUnit S))) htransport
    exact h.trans hnorm
  refine ⟨hm, f, hf, δ, δp, hδ, hδp, hδiso, hδpiso, hc, ρ, ρp, c,
    hnorm, hnormp, ?_, ?_, hsquare, ?_, ?_, hunits,
    quotient_value_one Ω, ?_⟩
  · intro r hr
    exact normalized_iso_unique ρ _ hnorm r hr
  · intro r hr
    exact normalized_iso_unique ρp _ hnormp r hr
  · simp [ρp]
  · intro q hq
    exact hz q hq
  · intro a r
    have hk := hmon a r
    have hres : ρ.hom (δ (k (constantUnit Ω a * coordinateUnit S ^ r))) =
        r • (1 : P.Coefficient) := by
      change ρ.hom (δ (kummerClass _ _ _ _ _ _ _ _)) = _
      rw [hk]
      simpa using congrArg (fun x ↦ r • x) hnorm
    refine ⟨monomial_value Ω a r, hres, ?_⟩
    have h := congrArg (fun g ↦ g (k (constantUnit Ω a * coordinateUnit S ^ r))) htransport
    exact h.trans hres

end WeilConjectures.PurityFiniteSetting.RankOne
