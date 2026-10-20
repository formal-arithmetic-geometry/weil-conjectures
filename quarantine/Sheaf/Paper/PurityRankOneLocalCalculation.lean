/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
public import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.AlgebraicGeometry.KummerAffineLine
import Sheaf.AlgebraicGeometry.SupportComparisonBoundary
import Sheaf.AlgebraicGeometry.SupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Sites.Kummer

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

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.RankOne

/-- Evaluation on a site object, the section functor used in the support definition.
Source: blueprint proof Step 4 (blueprint: thm-pur-rank-one-local-calculation). -/
abbrev sections {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] (W : C) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙ (evaluation _ _).obj (op W)

/-- The recorded open immersion is the inclusion of its basic open.
Source: blueprint affine-line datum (blueprint: thm-pur-rank-one-local-calculation). -/
instance openImmersion_isOpenImmersion (Y : Scheme.{u}) :
    IsOpenImmersion (openImmersion Y) :=
  inferInstanceAs (IsOpenImmersion (((Line Y).basicOpen (coordinate Y)).ι))

/-- The standard punctured-line object of the small etale site.
Source: blueprint proof Step 1 (blueprint: thm-pur-rank-one-local-calculation). -/
def openObject (Y : Scheme.{u}) : (Line Y).Etale :=
  Scheme.Etale.mk (openImmersion Y)

/-- Restriction from the affine line to its punctured open, whose complement is the origin.
Source: blueprint proof Step 4 (blueprint: thm-pur-rank-one-local-calculation). -/
def restriction (Y : Scheme.{u}) : openObject Y ⟶ Scheme.Etale.mk (𝟙 (Line Y)) :=
  MorphismProperty.Over.homMk (openImmersion Y)
    (by change openImmersion Y ≫ 𝟙 (Line Y) = openImmersion Y; simp)

/-- The genuine inverse-image coefficient sheaf on the pro-etale site.
Source: blueprint proof Step 7 (blueprint: thm-pur-rank-one-local-calculation). -/
abbrev proCoefficient (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F

/-- The three complexes in the support sequence, with the actual kernel inclusion and
restriction. Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def sectionComplex {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] {V W : C} (j : W ⟶ V)
    (I : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex
      (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j) (.up ℕ)).app I)
    ((NatTrans.mapHomologicalComplex
      ((sheafSections J (ModuleCat.{u + 1} A)).map j.op) (.up ℕ)).app I)
    (by ext n : 1; exact kernel.condition ((I.X n).obj.map j.op))

/-- A support boundary is exactly the snake boundary on injective section complexes,
transported by the canonical resolution comparisons. This characterization rules out
both an arbitrary isomorphism and an arbitrary choice of sign.
Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def IsBoundary {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] [HasSheafify J (ModuleCat.{u + 1} A)]
    [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
    {V W : C} (j : W ⟶ V) (F : Sheaf J (ModuleCat.{u + 1} A))
    (δ : ((sections J A W).rightDerived 1).obj F ⟶
      ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).rightDerived 2).obj F) :
    Prop :=
  ∀ I : InjectiveResolution F, ∃ hI : (sectionComplex J A j I.cocomplex).ShortExact,
    δ = (I.isoRightDerivedObj (sections J A W) 1).hom ≫
      hI.δ 1 2 rfl ≫
      (I.isoRightDerivedObj
        (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) 2).inv

/-- Free abelian sheafification represents sections, with its canonical Yoneda map.
Source: Stacks 03F3; blueprint proof Step 2
(blueprint: thm-pur-rank-one-local-calculation). -/
def evaluationRepresented (X : Scheme.{u}) (W : X.Etale) :
    preadditiveCoyoneda.obj (op ((presheafToSheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free))) ≅
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op W) :=
  NatIso.ofComponents
    (fun F ↦ (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W F).toAddCommGrpIso)
    (by
      intro F G f
      ext a
      exact (EtaleOpenComparison.sectionsEquiv_naturality X.smallEtaleTopology W f a).symm)

/-- The Ext/derived-evaluation comparison normalized on every injective cocycle.
The theorem used here determines the comparison uniquely, since every Ext class has
an injective cocycle representative. No coefficient object is chosen from mere existence.
Source: Stacks 06XR; blueprint proof Step 2
(blueprint: thm-pur-rank-one-local-calculation). -/
def evaluationExt (X : Scheme.{u}) (W : X.Etale) (q : ℕ) :=
  Classical.choose (CategoryTheory.exists_ext_rightDerived_cocycle_comparison
    ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (uliftYoneda.{u + 1}.obj W ⋙ AddCommGrpCat.free))
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation _ _).obj (op W)) (evaluationRepresented X W)) q

/-- The actual Kummer class over an etale object: precompose the Kummer extension
with the section represented by the unit, then apply the specified coefficient map.
The final inverse is the canonical module/abelian evaluation comparison.
Source: Kummer sequence; blueprint proof Steps 2 and 4
(blueprint: thm-pur-rank-one-local-calculation). -/
def kummerClass (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (v : Γ(W.left, ⊤)ˣ) : ((sections X.smallEtaleTopology A W).rightDerived 1).obj F := by
  letI := (Etale.module_cohomology_conventions A X).2.1 F W 1
  exact (asIso ((Etale.moduleEvaluationForgetComparison A X W 1).app F)).inv
    ((evaluationExt X W 1).inv.app ((Etale.moduleAbelianForget A X).obj F)
      (((Abelian.Ext.mk₀
        ((EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W X.gmSheaf).symm
          (ULift.up (Additive.ofMul v)))).comp
            (X.kummerSequence_shortExact m hm).extClass (zero_add 1)).comp
              (Abelian.Ext.mk₀ f) (add_zero 1)))

/-- The section comparison is the actual unit of etale/pro-etale inverse image,
evaluated at the same etale object. Source: blueprint proof Step 7
(blueprint: thm-pur-rank-one-local-calculation). -/
def comparisonSections (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : X.Etale) :
    sections X.smallEtaleTopology A W ⋙ 𝟭 (ModuleCat.{u + 1} A) ⟶
      ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W) where
  app F := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.app
    (op W)
  naturality F G f := by
    exact congrArg (fun t ↦ t.hom.app (op W))
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.naturality f)

/-- The canonical higher section comparison, derived from the adjunction unit.
Source: Stacks 099W; blueprint proof Step 7
(blueprint: thm-pur-rank-one-local-calculation). -/
def comparisonCohomology (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (W : X.Etale) (q : ℕ) :=
  Functor.rightDerivedBaseChange
    (G := sections X.smallEtaleTopology A W)
    (G' := sections (Scheme.ProEt.topology X) A ((Scheme.toProEt X).obj W))
    (β := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (γ := 𝟭 (ModuleCat.{u + 1} A)) (comparisonSections A X W) q

/-- Pullback of a constant unit to the punctured affine line.
Source: blueprint proof Step 5 (blueprint: thm-pur-rank-one-local-calculation). -/
def constantUnit (Ω : Type u) [Field Ω] (c : Ωˣ) :
    Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤)ˣ :=
  Units.map
    (((puncturedProjection (Spec (CommRingCat.of Ω))).appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).toMonoidHom c

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
  sorry

end WeilConjectures.PurityFiniteSetting.RankOne
