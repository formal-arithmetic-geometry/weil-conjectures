module

public import Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings

import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import WeilConjectures.RingTheory.RingPseudoCoherent
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat

/-! # Polynomial models of infinitesimal derived limits

Source: Stacks Project, spaces-flat.tex, Tags 0CX7 and 0CX9; more-morphisms.tex,
Tags 09UU and 09VF; more-algebra.tex, Tags 064K and 06Y6
(blueprint: lem-sfb-space-inverse-module-polynomial-model).

## Main definitions

* `inverseModuleAffineChart`, `inverseModuleLocalizedChart`: the given chart and its
  principal open charts, as objects of the existing small etale ringed site.
* `inverseModuleChartSections`, `inverseModuleChartDerivedSections`: actual sections
  and their unbounded right derived functor, retaining the coordinate-ring action.
* `inverseModuleLocalizeComplex`, `inverseModulePolynomialBaseComplex`,
  `inverseModuleLocalizedBaseComplex`: termwise localization and coefficient restriction.
* `inverseModuleLocalizedPolynomialSections`: derived localized sections with the
  canonical action of the localized polynomial ring.

## Main statements

* `inverseModuleChartSections_additive`: the additivity obligation used in deriving sections.
* `inverseModulePolynomialModel`: one bounded-above finite-free model, its principal
  localizations, their A-K-flatness, and arbitrary termwise derived coefficient extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine étale chart as an object of the existing ringed site.
Source: Stacks, 0CX9 (blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModuleAffineChart {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    (B : CommRingCat.{u}) (a : schemeSpace (inverseModuleSpec B) ⟶ X)
    (ha : IsEtale a.hom.hom) : X.EtaleSite :=
  ⟨CostructuredArrow.mk a.hom.hom, ha⟩

/-- The principal localization of the given affine chart, using the actual spectrum map.
Source: Stacks, 0CX9 and 08DW
(blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModuleLocalizedChart {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    (B : CommRingCat.{u}) (a : schemeSpace (inverseModuleSpec B) ⟶ X)
    (ha : IsEtale a.hom.hom) (b : B) : X.EtaleSite :=
  ⟨CostructuredArrow.mk
      (yoneda.map (inverseModuleSpecMap (CommRingCat.ofHom
        (algebraMap B (Localization.Away b)))) ≫ a.hom.hom),
    isEtale_comp _ _
      (((representable_etale_scheme_tests (S := Spec (.of (ULift.{u} ℤ)))).2.2.2.2.2.2.2.1
        _ _ (inverseModuleSpecMap (CommRingCat.ofHom
          (algebraMap B (Localization.Away b))))).2
        (inferInstance : Etale (Spec.map (CommRingCat.ofHom
          (algebraMap B (Localization.Away b)))))) ha⟩

/-- Actual sections on a specified affine chart, with its coordinate-ring action.
The ring map is from B to Γ(Spec B,O), the inverse of ΓSpecIso.
Source: Stacks, 0CX9 and 09VF
(blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModuleChartSections {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    (B : CommRingCat.{u}) (T : X.EtaleSite) (e : X.etaleForget.obj T ≅ Spec B) :
    X.SmallModules ⥤ ModuleCat.{u} B :=
  X.smallModuleEquivalence.inverse ⋙ SheafOfModules.evaluation X.structureSheaf (op T) ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso B).inv ≫ e.hom.appTop).hom)

/-- Additivity of the actual chart-sections functor.
Source: Stacks, 079V (blueprint: lem-sfb-space-inverse-module-polynomial-model).
Proof: the inverse small-site equivalence preserves biproducts and is additive.
Evaluation preserves sums of module maps sectionwise. Restriction of scalars is
additive. Compose these three additive functors. -/
@[instance] theorem inverseModuleChartSections_additive
    {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    (B : CommRingCat.{u}) (T : X.EtaleSite) (e : X.etaleForget.obj T ≅ Spec B) :
    (inverseModuleChartSections B T e).Additive := by
  sorry

/-- Unbounded derived sections of the same chart, retaining the B-action.
Source: Stacks, 079V and 0CX9
(blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModuleChartDerivedSections {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    [HasDerivedCategory.{w} X.SmallModules]
    (B : CommRingCat.{u}) (T : X.EtaleSite) (e : X.etaleForget.obj T ≅ Spec B) :
    X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} B) :=
  (inverseModuleChartSections B T e).rightDerivedFunctor

/-- Termwise localization of a polynomial complex, namely P_f tensor_P E.
Source: Stacks, 08DW and 00CS
(blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModuleLocalizeComplex {P : Type u} [CommRing P]
    (E : CochainComplex (ModuleCat.{u} P) ℤ) (g : P) :
    CochainComplex (ModuleCat.{u} (Localization.Away g)) ℤ :=
  ((ModuleCat.extendScalars (algebraMap P (Localization.Away g))).mapHomologicalComplex
    (.up ℤ)).obj E

/-- Restrict a polynomial complex to its actual coefficient ring.
Source: Stacks, 0CX9 (blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModulePolynomialBaseComplex (A : CommRingCat.{u}) (d : ℕ)
    (E : CochainComplex (ModuleCat.{u} (MvPolynomial (Fin d) A)) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ModuleCat.restrictScalars (MvPolynomial.C : A →+* MvPolynomial (Fin d) A)).mapHomologicalComplex
     (.up ℤ)).obj E

/-- Restrict the localized complex along A to P to P_g, preserving its coefficient action.
Source: Stacks, 0CX9 and 064K
(blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModuleLocalizedBaseComplex (A : CommRingCat.{u}) (d : ℕ)
    (E : CochainComplex (ModuleCat.{u} (MvPolynomial (Fin d) A)) ℤ)
    (g : MvPolynomial (Fin d) A) : CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ModuleCat.restrictScalars ((algebraMap (MvPolynomial (Fin d) A) (Localization.Away g)).comp
    MvPolynomial.C)).mapHomologicalComplex (.up ℤ)).obj
      (inverseModuleLocalizeComplex E g)

/-- Derived sections over the localized chart restricted from B_bar(g) to P_g.
The scalar map is the canonical localization of the given polynomial presentation.
Source: Stacks, 08DW and 09VF
(blueprint: lem-sfb-space-inverse-module-polynomial-model). -/
def inverseModuleLocalizedPolynomialSections
    {X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
    [HasDerivedCategory.{w} X.SmallModules]
    (A B : CommRingCat.{u}) (d : ℕ) (π : MvPolynomial (Fin d) A →+* B)
    (a : schemeSpace (inverseModuleSpec B) ⟶ X) (ha : IsEtale a.hom.hom)
    (g : MvPolynomial (Fin d) A) (K : X.DerivedModules) :
    DerivedCategory (ModuleCat.{u} (Localization.Away g)) :=
  ((ModuleCat.restrictScalars (IsLocalization.Away.map
    (Localization.Away g) (Localization.Away (π g)) π g)).mapDerivedCategory).obj
      ((inverseModuleChartDerivedSections (.of (Localization.Away (π g)))
        (inverseModuleLocalizedChart B a ha (π g)) (Iso.refl _)).obj K)

/-- A bounded-above finite-free polynomial model and all its principal localizations
represent the indicated derived sections, are K-flat over A, and compute arbitrary
coefficient extension termwise. Every comparison is in the stated module category,
so in particular it retains the action of A.
Source: Stacks, spaces-flat.tex, 0CX7 and 0CX9; spaces-more-morphisms.tex, 0CSX;
more-morphisms.tex, 09UU and 09VF; perfect.tex, 08E7 and 08DW;
more-algebra.tex, 064K and 06Y6
(blueprint: lem-sfb-space-inverse-module-polynomial-model).

Proof:
1. The derived-limit theorem gives bounded quasi-coherent K. Finite presentation
   over the qcqs affine base makes X qcqs. Its perfect tensor tests have bounded
   finite-projective representatives, and the finite-free replacement theorem makes
   these pseudo-coherent over A (lem-sfb-space-inverse-module-perfect-tests,
   lem-pc-finite-projective-complex-free-model, def-pc-ring-pseudo-coherent-complex).
2. Apply lem-sfb-space-perfect-to-pseudocoherent-tests and then
   lem-sfb-space-pseudocoherent-tests-relative: K is pseudo-coherent relative to A.
   No flatness of X over A is required.
3. Relative pseudo-coherence is tested on all etale charts. The derived etale/Zariski
   equivalence identifies the chart restriction. Embed Spec B in Spec P using π.
   Polynomial projection is flat and finitely presented, so
   lem-sfb-flat-ambient-relative-pseudocoherence makes its derived pushforward
   pseudo-coherent (lem-sfb-space-relative-pseudocoherence-etale-locality,
   lem-sfb-derived-etale-zariski-equivalence, lem-nagata-polynomial-projection-flat).
4. The affine QCoh derived equivalence represents the restriction by a module
   complex C. On standard opens, sections of its termwise pushforward are precisely
   the localization of Res_P C. The affine pushforward resolution comparison shows
   this computes the derived pushforward. The affine pseudo-coherent criterion gives
   the bounded-above finite-free E (lem-pc-affine-qcoh-derived-equivalence,
   lem-weil-pbc-spec-module-tilde-sections, lem-pc-affine-pushforward-resolution-quasi-iso,
   lem-pc-affine-pseudo-coherent-criterion).
5. Exact localization and affine derived pullback identify E_g with sections on
   Spec B_bar(g). The fraction map c/g^j to c/bar(g)^j is A-linear, as are the original
   comparisons (lem-weil-pbc-localization-module-exact,
   lem-pc-affine-derived-pullback-tensor-tilde).
6. Finite free P-modules are A-free via monomials. Localization preserves A-flatness
   (lem-pc-affine-flat-module-localization-preserves-flatness). Both complexes are
   bounded above, so lem-pc-module-bounded-flat-kflat gives the displayed acyclic
   total-tensor conditions. Finally lem-pur-derived-change-of-rings computes derived
   extension along every A to R on these K-flat representatives. This also covers
   g=0, g=1, d=0 and the zero complex.
-/
theorem inverseModulePolynomialModel
    (A : ℕ → CommRingCat.{u}) (r : ∀ n : ℕ, A (n + 1) ⟶ A n)
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    (hnil : ∀ (n : ℕ) (a : A (n + 1)), (r n) a = 0 → IsNilpotent a)
    (c : Cone (Functor.ofOpSequence r)) (hc : IsLimit c)
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    [HasDerivedCategory.{w} X.SmallModules]
    (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hqc : ∀ n : ℕ, (M n).IsQuasicoherent)
    (hfin : ∀ n : ℕ, (M n).IsFinitePresentation)
    (hflat : ∀ (n : ℕ) (U : (properQuotFibre f (inverseModuleTest c n)).EtaleSite),
      ((schemeRestriction _ U).obj (M n)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f (inverseModuleTest c n)).hom.hom)).left)
    (hsupp : ∀ n : ℕ, ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (i : Z ⟶ properQuotFibre f (inverseModuleTest c n)),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd f (inverseModuleTest c n)) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M n))
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n)
    (hq : ∀ n : ℕ,
      X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)))
    [HasProduct (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))]
    (K : X.DerivedQCoh)
    (p : K ⟶ ∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)))
    (δ : (∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))) ⟶ K⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle (fun n : ℕ ↦ inverseModuleDerivedTransition f
      (inverseModuleTestMap c n) (M n) (M (n + 1)) (e n) (hq n) (hq (n + 1))) K p δ)
    (B : CommRingCat.{u}) (a : schemeSpace (inverseModuleSpec B) ⟶ X)
    (ha : IsEtale a.hom.hom) (β : c.pt ⟶ B)
    (hβ : a.hom.hom ≫ f.hom.hom = yoneda.map (inverseModuleSpecMap β))
    (d : ℕ) (π : MvPolynomial (Fin d) c.pt →+* B)
    (hπ : Function.Surjective π) (hπA : π.comp MvPolynomial.C = β.hom) :
    ∃ E : CochainComplex (ModuleCat.{u} (MvPolynomial (Fin d) c.pt)) ℤ,
      (∃ b : ℤ, E.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Free (MvPolynomial (Fin d) c.pt) (E.X i) ∧
        Module.Finite (MvPolynomial (Fin d) c.pt) (E.X i)) ∧
      Nonempty (DerivedCategory.Q.obj E ≅
        ((ModuleCat.restrictScalars π).mapDerivedCategory).obj
          ((inverseModuleChartDerivedSections B (inverseModuleAffineChart B a ha)
            (Iso.refl _)).obj K.obj)) ∧
      (∀ L : CochainComplex (ModuleCat.{u} c.pt) ℤ, L.Acyclic →
        (CochainComplex.mapBifunctor L (inverseModulePolynomialBaseComplex c.pt d E)
          (MonoidalCategory.curriedTensor _)).Acyclic) ∧
      ∀ g : MvPolynomial (Fin d) c.pt,
        Nonempty (DerivedCategory.Q.obj (inverseModuleLocalizeComplex E g) ≅
          inverseModuleLocalizedPolynomialSections c.pt B d π a ha g K.obj) ∧
        (∀ L : CochainComplex (ModuleCat.{u} c.pt) ℤ, L.Acyclic →
          (CochainComplex.mapBifunctor L (inverseModuleLocalizedBaseComplex c.pt d E g)
            (MonoidalCategory.curriedTensor _)).Acyclic) ∧
        ∀ (R : CommRingCat.{u}) (ρ : c.pt ⟶ R),
          Nonempty (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars ρ.hom).mapHomologicalComplex (.up ℤ)).obj
              (inverseModuleLocalizedBaseComplex c.pt d E g)) ≅
            (ModuleCat.ordinaryDerivedExtendScalars ρ.hom).obj
              (((ModuleCat.restrictScalars
                ((algebraMap (MvPolynomial (Fin d) c.pt) (Localization.Away g)).comp
                  MvPolynomial.C)).mapDerivedCategory).obj
                    (inverseModuleLocalizedPolynomialSections c.pt B d π a ha g K.obj))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
