/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneLocalData
import Sheaf.Paper.RankOneFiniteKummerCohomology
import Sheaf.Paper.RankOneKummerMonomial
import Sheaf.Paper.RankOneClassicalSupportComparison
import WeilConjectures.AlgebraicGeometry.AffineSpace.PuncturedLine
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-! # The finite rank-one Kummer residue

Source: Milne, Lectures on Etale Cohomology, Sections 9, 14 and 16;
(blueprint: thm-pur-rank-one-local-calculation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

attribute [local implicit_reducible] Functor.mapHomologicalComplex
  HomologicalComplex.homologyFunctor



private theorem support_calculation
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) (F : Sheaf J (ModuleCat.{u + 1} A))
    (δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F)
    (hδ : IsBoundary J A j F δ)
    (hX : ∀ q : ℕ, 0 < q → IsZero (((sections J A V).rightDerived q).obj F))
    (hU : ∀ q : ℕ, 2 ≤ q → IsZero (((sections J A W).rightDerived q).obj F))
    (h0 : IsIso ((NatTrans.rightDerived
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) 0).app F)) :
    IsIso δ ∧ ∀ q : ℕ, q ≠ 2 →
      IsZero (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived
        q).obj F) := by
  let I := injectiveResolution F
  obtain ⟨hS, hδeq⟩ := hδ I
  let S := sectionComplex J A j I.cocomplex
  have hX' (q : ℕ) (hq : 0 < q) : IsZero (S.X₂.homology q) :=
    (hX q hq).of_iso (I.isoRightDerivedObj (sections J A V) q).symm
  have hU' (q : ℕ) (hq : 2 ≤ q) : IsZero (S.X₃.homology q) :=
    (hU q hq).of_iso (I.isoRightDerivedObj (sections J A W) q).symm
  have hg0 : IsIso (HomologicalComplex.homologyMap S.g 0) := by
    have heq : HomologicalComplex.homologyMap S.g 0 =
        (I.isoRightDerivedObj (sections J A V) 0).inv ≫
          (NatTrans.rightDerived
            ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) 0).app F ≫
          (I.isoRightDerivedObj (sections J A W) 0).hom := by
      rw [I.rightDerived_app_eq]
      change HomologicalComplex.homologyMap S.g 0 =
        (I.isoRightDerivedObj (sections J A V) 0).inv ≫
          (I.isoRightDerivedObj (sections J A V) 0).hom ≫
            HomologicalComplex.homologyMap S.g 0 ≫
              (I.isoRightDerivedObj (sections J A W) 0).inv ≫
                (I.isoRightDerivedObj (sections J A W) 0).hom
      simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rw [heq]
    infer_instance
  have hsnake : IsIso (hS.δ 1 2 support_degree_relation) :=
    hS.isIso_δ 1 2 support_degree_relation (hX' 1 (by omega)) (hX' 2 (by omega))
  refine ⟨?_, ?_⟩
  · rw [hδeq]
    infer_instance
  · intro q hq
    apply IsZero.of_iso _
      (I.isoRightDerivedObj
        (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) q)
    apply HomologicalComplex.ExactAt.isZero_homology
    apply hS.exactAt_X₁ q (h₁ := ?_) (h₂ := ?_)
    · by_cases hq0 : q = 0
      · subst q
        infer_instance
      · exact (hX' q (by omega)).mono _
    · intro i hi
      have hiq : i + 1 = q := hi
      by_cases hi0 : i = 0
      · subst i
        have hq1 : q = 1 := by omega
        subst q
        infer_instance
      · exact (hU' i (by omega)).epi _

private theorem zeroth_isIso_iff
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] {E G : C ⥤ D} [E.Additive] [G.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteLimits G] (α : E ⟶ G) (F : C) :
    IsIso ((NatTrans.rightDerived α 0).app F) ↔ IsIso (α.app F) := by
  have h := rightDerived_zero_transformation α F
  constructor
  · intro hα
    have : IsIso (α.app F ≫ G.toRightDerivedZero.app F) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (G.toRightDerivedZero.app F)
  · intro hα
    have : IsIso (E.toRightDerivedZero.app F ≫ (NatTrans.rightDerived α 0).app F) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (E.toRightDerivedZero.app F) _

private theorem normalized_iso_unique
    {A : Type (u + 1)} [CommRing A] {M : ModuleCat.{u + 1} A}
    (e : ModuleCat.of A A ≅ M) (x : M) (hx : e.hom 1 = x)
    (ρ σ : M ≅ ModuleCat.of A A) (hρ : ρ.hom x = 1) (hσ : σ.hom x = 1) :
    ρ = σ := by
  apply Iso.ext
  apply (cancel_epi e.hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change ρ.hom (e.hom 1) = σ.hom (e.hom 1)
  rw [hx, hρ, hσ]

private theorem valuation_unit (Ω : Type u) [Field Ω]
    (a : Polynomial Ω) (ha : a.eval 0 ≠ 0) :
    (Polynomial.idealX Ω).intValuation a = 1 := by
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
  change a ∉ Ideal.span {Polynomial.X}
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
  exact ha

private theorem valuation_quotient (Ω : Type u) [Field Ω]
    (a b : Polynomial Ω) (ha : a.eval 0 ≠ 0) (hb : b.eval 0 ≠ 0) :
    (Polynomial.idealX Ω).valuation (RatFunc Ω) (RatFunc.mk a b) = 1 := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [Polynomial.valuation_of_mk Ω a hb0, valuation_unit Ω a ha,
    valuation_unit Ω b hb, div_self one_ne_zero]

private theorem valuation_monomial (Ω : Type u) [Field Ω] (c : Ωˣ) (r : ℤ) :
    (Polynomial.idealX Ω).valuation (RatFunc Ω)
      (RatFunc.C (c : Ω) * (RatFunc.X : RatFunc Ω) ^ r) = WithZero.exp (-r) := by
  have hc : (Polynomial.idealX Ω).valuation (RatFunc Ω) (RatFunc.C (c : Ω)) = 1 := by
    rw [← RatFunc.algebraMap_C,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact valuation_unit Ω (Polynomial.C (c : Ω)) (by simp)
  rw [map_mul, hc, one_mul, map_zpow₀, Polynomial.valuation_X_eq_neg_one,
    ← WithZero.exp_zsmul]
  congr 1
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
  classical
  have := hy
  let X := Line (Spec (CommRingCat.of Ω))
  let m := P.coefficients.l ^ N
  let F := Scheme.finiteEtaleTateSheaf P.Coefficient m X hA 1
  let : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  let : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  have hℓ : IsUnit (P.coefficients.l : Ω) := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    have : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    have h : IsUnit (P.coefficients.l : P.field.k) :=
      isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime _
        (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)
    simpa only [map_natCast] using h.map (algebraMap P.field.k Ω)
  have hm : IsUnit (m : Γ(X, ⊤)) := by
    simpa only [m, map_natCast, map_pow, Nat.cast_pow] using
      (hℓ.pow N).map
        (((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫
          (lineProjection (Spec (CommRingCat.of Ω))).appTop).hom)
  let f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget P.Coefficient X).obj F :=
    Etale.ordinaryFiniteRootMap P.Coefficient m hA X
  have hf : ∀ V z, f.hom.app V z =
      Scheme.finiteEtaleTateOneGenerator P.Coefficient m X hA V 1 z := by
    intro V z
    rfl
  obtain ⟨⟨τ, hτ⟩, hX, hU, h0⟩ := finite_kummer_cohomology
    P.Coefficient Ω P.coefficients.l N (Fact.out : P.coefficients.l.Prime) hℓ hN hA hm f hf
  have hκ := kummer_monomial P.Coefficient Ω m
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos N) hA F hm f
  have hj : Mono (restriction (Spec (CommRingCat.of Ω))) := by
    apply (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map
    change Mono (openImmersion (Spec (CommRingCat.of Ω)))
    infer_instance
  obtain ⟨hc, ⟨δet, hδet⟩, ⟨δpro, hδpro⟩⟩ :=
    classical_support_comparison P.Coefficient X
      (restriction (Spec (CommRingCat.of Ω))) F
  obtain ⟨hisoet, hzero⟩ := support_calculation X.smallEtaleTopology
    P.Coefficient (restriction (Spec (CommRingCat.of Ω))) F δet hδet hX hU h0
  have := hc (openObject (Spec (CommRingCat.of Ω))) 1
  let cU := asIso ((comparisonCohomology P.Coefficient X
    (openObject (Spec (CommRingCat.of Ω))) 1).app F)
  have hXpro (q : ℕ) (hq : 0 < q) : IsZero
      (((sections (Scheme.ProEt.topology X) P.Coefficient
        ((Scheme.toProEt X).obj (Scheme.Etale.mk (𝟙 X)))).rightDerived q).obj
          (proCoefficient P.Coefficient X F)) := by
    have := hc (Scheme.Etale.mk (𝟙 X)) q
    exact (hX q hq).of_iso (asIso ((comparisonCohomology P.Coefficient X
      (Scheme.Etale.mk (𝟙 X)) q).app F)).symm
  have hUpro (q : ℕ) (hq : 2 ≤ q) : IsZero
      (((sections (Scheme.ProEt.topology X) P.Coefficient
        ((Scheme.toProEt X).obj (openObject (Spec (CommRingCat.of Ω))))).rightDerived q).obj
          (proCoefficient P.Coefficient X F)) := by
    have := hc (openObject (Spec (CommRingCat.of Ω))) q
    exact (hU q hq).of_iso (asIso ((comparisonCohomology P.Coefficient X
      (openObject (Spec (CommRingCat.of Ω))) q).app F)).symm
  have h0et : IsIso (F.obj.map (restriction (Spec (CommRingCat.of Ω))).op) :=
    (zeroth_isIso_iff _ F).mp h0
  have h0pro : IsIso ((NatTrans.rightDerived
      ((sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)).map
        ((Scheme.toProEt X).map (restriction (Spec (CommRingCat.of Ω)))).op) 0).app
          (proCoefficient P.Coefficient X F)) := by
    apply (zeroth_isIso_iff _ _).mpr
    let η := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X).unit.app F
    have := ProEtale.isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} P.Coefficient) X
    have hn := η.hom.naturality (restriction (Spec (CommRingCat.of Ω))).op
    have heq : (proCoefficient P.Coefficient X F).obj.map
        ((Scheme.toProEt X).map (restriction (Spec (CommRingCat.of Ω)))).op =
        inv (η.hom.app (op (Scheme.Etale.mk (𝟙 X)))) ≫
          F.obj.map (restriction (Spec (CommRingCat.of Ω))).op ≫
            η.hom.app (op (openObject (Spec (CommRingCat.of Ω)))) := by
      apply (cancel_epi (η.hom.app (op (Scheme.Etale.mk (𝟙 X))))).mp
      rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
      exact hn.symm
    change IsIso ((proCoefficient P.Coefficient X F).obj.map
      ((Scheme.toProEt X).map (restriction (Spec (CommRingCat.of Ω)))).op)
    rw [heq]
    infer_instance
  obtain ⟨hisopro, hzeropro⟩ := support_calculation (Scheme.ProEt.topology X)
    P.Coefficient ((Scheme.toProEt X).map (restriction (Spec (CommRingCat.of Ω))))
      (proCoefficient P.Coefficient X F) δpro hδpro hXpro hUpro h0pro
  let cZ := (asIso δet).symm ≪≫ cU ≪≫ asIso δpro
  have hsquare : δet ≫ cZ.hom = cU.hom ≫ δpro := by simp [cZ]
  let e := τ ≪≫ asIso δet
  let ρet := e.symm
  let ρpro := cZ.symm ≪≫ ρet
  have hnorm : ρet.hom (δet (kummerClass P.Coefficient X
      (openObject (Spec (CommRingCat.of Ω))) F m hm f
        (coordinateUnit (Spec (CommRingCat.of Ω))))) = 1 := by
    rw [← hτ]
    exact ConcreteCategory.congr_hom e.hom_inv_id 1
  have hcompat : cZ.hom ≫ ρpro.hom = ρet.hom := by
    simp [ρpro]
  have hres (v : Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤)ˣ) :
      ρpro.hom (δpro (cU.hom (kummerClass P.Coefficient X
        (openObject (Spec (CommRingCat.of Ω))) F m hm f v))) =
      ρet.hom (δet (kummerClass P.Coefficient X
        (openObject (Spec (CommRingCat.of Ω))) F m hm f v)) := by
    have hh := congrArg (fun g ↦ g ≫ ρpro.hom) hsquare
    rw [Category.assoc, hcompat] at hh
    exact (ConcreteCategory.congr_hom hh
      (kummerClass P.Coefficient X (openObject (Spec (CommRingCat.of Ω))) F m hm f v)).symm
  refine ⟨hm, f, hf, δet, δpro, hδet, hδpro, hisoet, hisopro, hc _ 1,
    ρet, ρpro, cZ, hnorm, ?_, ?_, ?_, hsquare, hcompat, ?_, ?_,
    valuation_quotient Ω, ?_⟩
  · exact (hres (coordinateUnit (Spec (CommRingCat.of Ω)))).trans hnorm
  · intro ρ hρ
    exact normalized_iso_unique e _ (congrArg δet hτ) ρ ρet hρ hnorm
  · intro ρ hρ
    let epro := e ≪≫ cZ
    have hepro : epro.hom 1 = δpro (cU.hom (kummerClass P.Coefficient X
        (openObject (Spec (CommRingCat.of Ω))) F m hm f
          (coordinateUnit (Spec (CommRingCat.of Ω))))) := by
      change (e.hom ≫ cZ.hom) 1 = _
      change (τ.hom ≫ δet ≫ cZ.hom) 1 = _
      rw [hsquare]
      change δpro (cU.hom (τ.hom 1)) = _
      rw [hτ]
    exact normalized_iso_unique epro _ hepro ρ ρpro hρ (by rw [hres]; exact hnorm)
  · intro q hq
    exact ⟨hzero q hq, hzeropro q hq⟩
  · intro v
    have hjrange := AffineSpace.range_basicOpen_ι_coord
      (Spec (CommRingCat.of Ω))
    obtain ⟨⟨c, r⟩, hv⟩ := (AffineSpace.bijective_unitsProdZPowHomLine
      (openImmersion (Spec (CommRingCat.of Ω))) hjrange).2 v
    have ht : AffineSpace.unitLineCoord (openImmersion (Spec (CommRingCat.of Ω)))
        hjrange = coordinateUnit (Spec (CommRingCat.of Ω)) := by
      apply Units.ext
      rw [AffineSpace.val_unitLineCoord]
      exact (IsUnit.unit_spec _).symm
    refine ⟨c, r.toAdd, ?_⟩
    rw [AffineSpace.unitsProdZPowHomLine_apply, ht] at hv
    exact hv.symm
  · intro c r
    have hmon : ρet.hom (δet (kummerClass P.Coefficient X
        (openObject (Spec (CommRingCat.of Ω))) F m hm f
          (constantUnit Ω c * coordinateUnit (Spec (CommRingCat.of Ω)) ^ r))) =
        r • (1 : P.Coefficient) := by
      calc
        _ = ρet.hom (δet (r • kummerClass P.Coefficient X
            (openObject (Spec (CommRingCat.of Ω))) F m hm f
              (coordinateUnit (Spec (CommRingCat.of Ω))))) :=
          congrArg (fun z ↦ ρet.hom (δet z)) (hκ c r)
        _ = r • ρet.hom (δet (kummerClass P.Coefficient X
            (openObject (Spec (CommRingCat.of Ω))) F m hm f
              (coordinateUnit (Spec (CommRingCat.of Ω))))) := by
          rw [map_zsmul, map_zsmul]
        _ = _ := congrArg (fun z ↦ r • z) hnorm
    exact ⟨valuation_monomial Ω c r, hmon,
      (hres (constantUnit Ω c * coordinateUnit (Spec (CommRingCat.of Ω)) ^ r)).trans hmon⟩

end WeilConjectures.PurityFiniteSetting.RankOne
