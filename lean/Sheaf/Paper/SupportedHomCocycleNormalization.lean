/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Sheaf.Paper.SupportedCohomologyHom
import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # Evaluation and cocycle normalization of supported Hom

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5 and the Ext proof
of Theorem 9.4, pp. 66--67; Stacks Tags 05TH, 05TI, 070I, 070J and 095L
(blueprint: lem-pur-supported-hom-cocycle-normalization).

The interface below specifies evaluation, the actual derived-unit transport, and the
localized cocycle map. It uses the existing kernel functor in both topologies.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace AlgebraicGeometry

/-- Localize the canonical single-object cocycle without exposing its cochain construction.
Source: Stacks 070I (blueprint: lem-pur-supported-hom-cocycle-normalization). -/
@[irreducible] def supportedHomLocalizedCocycle.{uC, vC, wC}
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : C} (I : CochainComplex C ℤ) (a : ℤ) (f : B ⟶ I.X a)
    (hf : f ≫ I.d a (a + 1) = 0) :
    (DerivedCategory.singleFunctor C 0).obj B ⟶ (DerivedCategory.Q.obj I)⟦a⟧ :=
  ShiftedHom.map (Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q

/-- The localized cocycle is the original shifted single-complex map.
Source: Stacks 070I (blueprint: lem-pur-supported-hom-cocycle-normalization). -/
theorem supportedHomLocalizedCocycle_eq.{uC, vC, wC}
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : C} (I : CochainComplex C ℤ) (a : ℤ) (f : B ⟶ I.X a)
    (hf : f ≫ I.d a (a + 1) = 0) :
    supportedHomLocalizedCocycle I a f hf =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q := by
  with_unfolding_all rfl


section Site

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
variable (A : Type (u + 1)) [CommRing A]
variable [HasSheafify J (ModuleCat.{u + 1} A)]
variable [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} A))]
variable [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} A))]
variable {T W : C} (hT : IsTerminal T) (j : W ⟶ T)
variable (B : Sheaf J (ModuleCat.{u + 1} A))
variable (rho : (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ B)

/-- A specified resolution induces this isomorphism in D+, using the canonical
quotient-to-derived comparisons on both complexes.
Source: Stacks 05TI and 070I; lem-sc-p1-rhom-hom-derived-roof
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomResolutionIso
    (K I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
    (e : K ⟶ I) [QuasiIso e.hom] :
    DerivedCategory.Plus.Q.obj K ≅ DerivedCategory.Plus.Q.obj I :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.quotientCompQhIso _).app K.obj ≪≫
      asIso (DerivedCategory.Q.map e.hom) ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app I.obj)

/-- The type of additive evaluation isomorphisms onto the actual support kernel.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev SupportedHomEvaluationIso :=
  preadditiveCoyoneda.obj (op B) ≅
    Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}

/-- Evaluation after the actual constant restriction, at the scalar one.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomEvaluation
    (theta : SupportedHomEvaluationIso J A j B) : Prop :=
  ∀ (M : Sheaf J (ModuleCat.{u + 1} A)) (f : B ⟶ M),
    kernel.ι (M.obj.map j.op) (theta.hom.app M f) =
      ((constantSheafAdj J (ModuleCat.{u + 1} A) hT).homEquiv _ _ (rho ≫ f)) 1

/-- The type of additive comparisons with derived morphisms, in all integer degrees.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev SupportedHomChi :=
  ∀ (F : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A))) (a : ℤ),
    (Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).obj F ≃+
      ((DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{u + 1} A)) 0).obj
        B ⟶ F.obj⟦a⟧)

/-- Naturality of the comparison on the bounded-below derived category.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomChiNatural (chi : SupportedHomChi J A j B) : Prop :=
  ∀ (F G : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      (v : F ⟶ G) (a : ℤ)
      (s : (Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).obj F),
    chi G a ((Sheaf.supportHypercohomologyFunctor J (ModuleCat.{u + 1} A) j a).map v s) =
      chi F a s ≫ (DerivedCategory.Plus.ι.map v)⟦a⟧'

/-- The formula on every injective resolution and every supported cocycle.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomChiCocycle
    (theta : SupportedHomEvaluationIso J A j B)
    (chi : SupportedHomChi J A j B) : Prop :=
  ∀ (K I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      [∀ r : ℤ, Injective (I.obj.X r)] (e : K ⟶ I) [QuasiIso e.hom] (a : ℤ)
      (x : ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (ComplexShape.up ℤ) |>.obj I.obj).cycles a),
    ∃! f : B ⟶ I.obj.X a,
      theta.hom.app (I.obj.X a) f =
        ((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj I.obj).iCycles a x ∧
      ∃ hf : f ≫ I.obj.d a (a + 1) = 0,
        chi (DerivedCategory.Plus.Q.obj K) a
          ((Sheaf.supportSequenceModelIso J (ModuleCat.{u + 1} A)
            (Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j) I
            (DerivedCategory.Plus.Q.obj K) (supportedHomResolutionIso J A K I e).symm a).hom
              (((Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j).mapHomologicalComplex
                (ComplexShape.up ℤ) |>.obj I.obj).homologyπ a x)) =
          supportedHomLocalizedCocycle I.obj a f hf ≫
            ((DerivedCategory.quotientCompQhIso _).inv.app I.obj)⟦a⟧' ≫
            (DerivedCategory.Plus.ι.map (supportedHomResolutionIso J A K I e).inv)⟦a⟧'

/-- Evaluation, naturality, and the roof formula, all with the canonical normalization.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
structure SupportedHomCocycleNormalization where
  theta : SupportedHomEvaluationIso J A j B
  evaluation : SupportedHomEvaluation J A hT j B rho theta
  chi : SupportedHomChi J A j B
  naturality : SupportedHomChiNatural J A j B chi
  cocycle : SupportedHomChiCocycle J A j B theta chi

/-- The actual restriction on abelian groups underlying module-valued sections.
Source: Milne, Section 9, Example 9.5
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomAbelianRestriction :
    (sheafSections J (ModuleCat.{u + 1} A)).obj (op T) ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ⟶
      (sheafSections J (ModuleCat.{u + 1} A)).obj (op W) ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} :=
  Functor.whiskerRight ((sheafSections J (ModuleCat.{u + 1} A)).map j.op)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- The inclusion of the actual support kernel, after forgetting scalar multiplication.
Source: Milne, Section 9, Example 9.5
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomAbelianInclusion :
    Sheaf.supportedSectionsFunctor J (ModuleCat.{u + 1} A) j ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} ⟶
      (sheafSections J (ModuleCat.{u + 1} A)).obj (op T) ⋙
        forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1} :=
  Functor.whiskerRight (Sheaf.supportedSectionsInclusion J (ModuleCat.{u + 1} A) j)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- Agreement on injective representatives with the shifted restriction cone: the
comparison is exactly kernel inclusion composed with evaluation, hence sends a supported
section to `(0,s)`. This specifies the comparison itself, including its sign.
Source: blueprint lem-amb-closed-support-hom, Hom triangle proof; Milne, Section 9
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomCocycleNormalization.ConeAgreement
    (N : SupportedHomCocycleNormalization J A hT j B rho) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J (ModuleCat.{u + 1} A)))
      [∀ r : ℤ, Injective (I.obj.X r)],
    ∃ h : ((supportedHomAbelianInclusion J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj ≫
        ((supportedHomAbelianRestriction J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj = 0,
      QuasiIso (CochainComplex.closedConeLift
        (((supportedHomAbelianRestriction J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj)
        (((supportedHomAbelianInclusion J A j).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I.obj) h) ∧
      QuasiIso (((NatIso.mapHomologicalComplex N.theta (ComplexShape.up ℤ)).app I.obj).hom ≫
        CochainComplex.closedConeLift
          (((supportedHomAbelianRestriction J A j).mapHomologicalComplex
            (ComplexShape.up ℤ)).app I.obj)
          (((supportedHomAbelianInclusion J A j).mapHomologicalComplex
            (ComplexShape.up ℤ)).app I.obj) h)

end Site

namespace Etale

/-- The scalar-preserving constant restriction to the open site, obtained by sheafification.
Source: Milne, Section 9, Example 9.5; Stacks 03DI
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomOpenConstantMap (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) :=
  ((sheafificationAdjunction U.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    (Functor.whiskerLeft (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))))

/-- The actual open counit at the constant module, with the scalar-preserving restriction.
Source: Milne, Section 9, Example 9.5; Stacks 03DI
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomOpenCounit (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).symm
    (supportedHomOpenConstantMap A j)

/-- Under the two evaluation adjunctions, precomposition with the actual open counit
is the actual restriction of sections. The site arrow has underlying morphism `j`.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomOpenEvaluation (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop :=
  ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (g : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A) ⟶ M),
    ((constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _
        ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _
          (supportedHomOpenCounit A j ≫ g))) 1 =
      M.obj.map (MorphismProperty.Over.homMk j
        (by exact (Category.comp_id j).trans (Category.id_comp j).symm) :
          (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj
            (Scheme.Etale.mk (𝟙 U)) ⟶ Scheme.Etale.mk (𝟙 X)).op
        (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _ g) 1)

/-- The prescribed etale coefficient object and its constant restriction map.
Source: Milne, Section 9, proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomConstantRestriction (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app (ModuleCat.of A A)).hom

/-- Specialization of evaluation normalization to the etale site of the closed pair.
Source: Milne, Section 9, Example 9.5 and Ext proof of Theorem 9.4
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev supportedHomNormalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  SupportedHomCocycleNormalization X.smallEtaleTopology P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale Z))
    (supportedHomConstantRestriction P.Coefficient i)

end Etale

namespace ProEtale

/-- The actual open counit, adjoint to the existing scalar-preserving constant map.
Source: Milne, Section 9, Ext proof; pro-etale constant presentation
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def supportedHomOpenCounit (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homEquiv
    _ _).symm (Scheme.proEtaleFixedOpenConstantMap j A)

/-- Evaluation of precomposition by the pro-etale open counit is restriction.
Source: Milne, Section 9, Example 9.5 and Ext proof, in the pro-etale topology
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
def SupportedHomOpenEvaluation (A : Type u) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : Prop :=
  ∀ (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
      (g : Scheme.proEtaleFixedConstantModule X A ⟶ M),
    ((constantSheafAdj (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _
        ((openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).homEquiv _ _
          (supportedHomOpenCounit A j ≫ g))) 1 =
      M.obj.map (MorphismProperty.Over.homMk j
        (by exact (Category.comp_id j).trans (Category.id_comp j).symm) :
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
            (Scheme.ProEt.mk (𝟙 U)) ⟶ Scheme.ProEt.mk (𝟙 X)).op
        (((constantSheafAdj (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1} A))
          (MorphismProperty.Over.mkIdTerminal _ _)).homEquiv _ _ g) 1)

/-- The same ordinary constant sheaf on the pro-etale site, before its canonical
identification with the etale-pullback presentation `P.constant`.
Source: Milne, Section 9, Example 9.5; pro-etale constant presentation
(blueprint: lem-pur-supported-hom-cocycle-normalization). -/
abbrev supportedHomNormalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  SupportedHomCocycleNormalization (Scheme.ProEt.topology X) P.Coefficient
    (MorphismProperty.Over.mkIdTerminal _ _) (supportRestrictionArrow i)
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (Scheme.proEtaleFixedConstantModule Z P.Ring))
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} P.Coefficient)
      (ModuleCat.of P.Coefficient P.Coefficient))

end ProEtale

/-- Evaluation at one and the injective-resolution roof normalize supported Hom in
both topologies. On the etale site the comparison to the shifted restriction cone is
inclusion of the evaluated support kernel in the shifted source summand.

Source: Milne, Lectures on Etale Cohomology, Section 9, Example 9.5 and the Ext proof
of Theorem 9.4, pp. 66--67; blueprint lem-amb-closed-support-hom, Hom triangle proof
(blueprint: lem-pur-supported-hom-cocycle-normalization).

Proof, following the ten recorded DAG steps:
1. Use small representatives in the coefficient universe. Ringed-site module sheaves
   are Grothendieck abelian by lem-pur-ringed-site-grothendieck-abelian, so have enough
   injectives by lem-sp-grothendieck-enough-injectives. Derive in module sheaves, without
   assuming that forgetting the scalar action preserves injectives.
2. Evaluation g ↦ g(1) identifies Hom(A_X,M) with M(X). Its inverse sends a section m
   to the map b ↦ b m|_V on each site object V. Semilinearity proves restriction
   compatibility and both inverse identities. The same construction applies over U.
3. The open adjunction identifies the adjunct of g composed with its counit with the
   restriction of g. Evaluation therefore gives precisely restriction of g(1), with
   no scalar factor or sign, as expressed by SupportedHomOpenEvaluation.
4. Use lem-weil-pbc-open-closed-short-exact and the canonical constant pullback on
   the etale site, or lem-pur-proetale-supported-constant-presentation on the pro-etale
   site. The actual constant restriction rho is the cokernel of the open counit.
   Each supported section thus gives a unique factorization f through rho.
   Uniqueness proves additivity and naturality, and fixes theta by evaluation.
5. Apply theta inverse termwise. Naturality for each differential makes this an
   isomorphism of complexes. Supported cocycles go to Hom cocycles; supported
   boundaries go to Hom boundaries.
6. Derive theta inverse using lem-weil-pbc-right-derived-plus-injective and its
   universal property. The inverse derives in the same way; uniqueness makes their
   composites identities. Naturality of the derived units identifies the comparison
   on any specified resolution with the actual unit followed by inverse R(Qe).
7. A bounded-below complex of injectives is K-injective. Apply
   lem-sc-p1-rhom-hom-derived-roof with M=i_*A_Z to obtain exactly the localized
   cocycle map followed by inverse shifted Qe. No sign enters its sole component.
8. Naturality of both comparisons gives naturality of chi. The construction is on
   cohomology before a resolution is chosen; the formula holds for every e and every
   cocycle. Changing a cocycle by a boundary therefore gives the same value, and the
   canonical derived-unit transports compare any two resolutions, also in negative degrees.
9. On the etale site the open constant counit is monic. The extension property of
   each injective makes restriction on sections surjective. Open restriction preserves
   injectives because extension by zero is exact, and preserves quasi-isomorphisms by
   prop-weil-pbc-inverse-image-modules-exact. Thus the section complexes compute the
   two ordinary derived global-section objects and their actual restriction.
10. Apply lem-weil-degreewise-epi-kernel-cocone-qis. The canonical comparison sends
   a supported section s to (0,s). The Hom triangle of lem-amb-closed-support-hom
   realizes its comparison as closedConeLift composed with theta termwise, which
   fixes the comparison and its sign, rather than just its composite to global sections.
   The shifted cone differential is (-d y-r x,d x). Thus the same supported cocycle
   gives the same roof. No quasi-compactness, constructibility, finite-Tor or purity
   hypothesis is used. -/
theorem supportedHom_cocycle_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ e : Etale.supportedHomNormalization P i,
      Nonempty (ProEtale.supportedHomNormalization P i) ∧ e.ConeAgreement ∧
      Etale.SupportedHomOpenEvaluation P.Coefficient i.openComplement.ι ∧
      ProEtale.SupportedHomOpenEvaluation P.Ring i.openComplement.ι := by
  sorry

end AlgebraicGeometry
