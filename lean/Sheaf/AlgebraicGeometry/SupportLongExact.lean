/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Paper.SiteRestrictionInjectives
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.SupportPairChainCoherence
import Sheaf.Paper.SupportPairComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction

/-!
# The long exact sequence of cohomology with support

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4;
Stacks Project, Tags 093X, 03F3, 0117, 070I
(blueprint: thm-pur-with-support-exactness).
-/

@[expose] public section

set_option autoImplicit false

universe c v a w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A]
variable {V W : C} (j : W ⟶ V)

/-- Inclusion of the kernel of restriction into sections on `V`.
Source: Milne, Section 9, definition before Theorem 9.4
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportedSectionsInclusion :
    supportedSectionsFunctor J A j ⟶ (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)) where
  app F := kernel.ι (F.obj.map j.op)
  naturality f := by simp [supportedSectionsFunctor]

variable [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory (Sheaf J A)]
variable [HasDerivedCategory A]

/-- Derived evaluation on an object of a site, followed by integer-indexed cohomology.
For a terminal object this is global hypercohomology; for the open object it is
hypercohomology of the localized site. Source: Stacks, Tag 03F3
(blueprint: thm-pur-with-support-exactness). -/
noncomputable abbrev sectionHypercohomologyFunctor (V : C) (q : ℤ) :
    DerivedCategory.Plus (Sheaf J A) ⥤ A :=
  (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor A q

/-- Derived supported sections followed by cohomology: this specializes exactly to
`Etale.supportHypercohomology` and `ProEtale.supportHypercohomology`.
Source: the support definition and Milne, Section 9, Theorem 9.4
(blueprint: thm-pur-with-support-exactness). -/
noncomputable abbrev supportHypercohomologyFunctor (q : ℤ) :
    DerivedCategory.Plus (Sheaf J A) ⥤ A :=
  (supportedSectionsFunctor J A j).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor A q

/-- The canonical first arrow in the support sequence, obtained by deriving kernel inclusion.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportHypercohomologyInclusion (q : ℤ) :
    supportHypercohomologyFunctor J A j q ⟶ sectionHypercohomologyFunctor J A V q :=
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans
    (supportedSectionsInclusion J A j)) (DerivedCategory.Plus.homologyFunctor A q)

/-- The canonical second arrow in the support sequence, obtained by deriving restriction.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
noncomputable def sectionHypercohomologyRestriction (q : ℤ) :
    sectionHypercohomologyFunctor J A V q ⟶ sectionHypercohomologyFunctor J A W q :=
  Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans
    (F := sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V))
    (G := sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W))
    ((sheafSections J A).map j.op)) (DerivedCategory.Plus.homologyFunctor A q)

/-- The canonical cohomology comparison from a bounded-below injective representative,
including its specified identification with the derived object. Source: Stacks, Tags 05TI,
05TH and 070I (blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportSequenceModelIso (E : Sheaf J A ⥤ A) [E.Additive]
    (I : CochainComplex.Plus (Sheaf J A)) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus (Sheaf J A)) (e : DerivedCategory.Plus.Q.obj I ≅ K)
    (q : ℤ) :
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj)) ≅
      (E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).obj K :=
  (DerivedCategory.Plus.homologyFunctorObjQIso
    (E.mapCochainComplexPlus.obj I) q).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      (asIso (E.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj I))) ≪≫
    (E.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor A q).mapIso e

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory (Sheaf J A)]
variable [HasDerivedCategory A] {V W : C} (j : W ⟶ V)
variable (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A)))

/-- A family of boundary maps natural in the permitted derived coefficients.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
abbrev SupportSequenceBoundary :=
  ∀ q : ℤ, P.ι ⋙ sectionHypercohomologyFunctor J A W q ⟶
    P.ι ⋙ supportHypercohomologyFunctor J A j (q + 1)

/-- Exactness at all three places, in all integer degrees, of the displayed sequence.
The other two maps are the derived kernel inclusion and restriction, not existential maps.
Source: Milne, Section 9, Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
def SupportSequenceExact (δ : SupportSequenceBoundary J A j P) : Prop :=
  ∀ (K : P.FullSubcategory) (q : ℤ),
    ∃ (w₁ : (supportHypercohomologyInclusion J A j q).app K.obj ≫
        (sectionHypercohomologyRestriction J A j q).app K.obj = 0)
      (w₂ : (sectionHypercohomologyRestriction J A j q).app K.obj ≫ (δ q).app K = 0)
      (w₃ : (δ q).app K ≫ (supportHypercohomologyInclusion J A j (q + 1)).app K.obj = 0),
      (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact ∧
        (ShortComplex.mk _ _ w₃).Exact

/-- The boundary on a specified injective representative, transported by the canonical
right-derived-functor unit. Source: Stacks, Tags 05TI, 05TH, 0117
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportSequenceModelBoundary (δ : SupportSequenceBoundary J A j P)
    (I : CochainComplex.Plus (Sheaf J A)) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : P.FullSubcategory) (e : DerivedCategory.Plus.Q.obj I ≅ K.obj) (q : ℤ) :
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).obj
      (((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj)) ⟶
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (q + 1)).obj
      (((supportedSectionsFunctor J A j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj)) :=
  (supportSequenceModelIso J A
    (sheafToPresheaf J A ⋙ (evaluation _ _).obj (op W)) I K.obj e q).hom ≫
    (δ q).app K ≫
    (supportSequenceModelIso J A (supportedSectionsFunctor J A j) I K.obj e (q + 1)).inv

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C D : Type c} [Category.{v} C] [Category.{v} D]
variable (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
variable (A : Type a) [Category.{w} A] [Abelian A]
variable (B : C ⥤ D) [hB : B.IsContinuous J J']

/-- Continuous pushforward acts by precomposition and is additive by definition.
Source: blueprint proof Step 7 (blueprint: thm-pur-with-support-exactness). -/
instance supportSequencePushforward_additive :
    (B.sheafPushforwardContinuous A J J').Additive where

/-- The chain map on sections induced by an adjoint coefficient chain map `b` and
restriction from `B(V)` to `V'`. For base change on scheme sites, this is precisely
`I(V) → L(V ×_X X') → L(V')` in the proof of pair functoriality.
Source: Milne, Section 9, Theorem 9.4; blueprint proof Step 7
(blueprint: thm-pur-with-support-exactness). -/
noncomputable def supportPairComplexSectionMap
    (I : CochainComplex.Plus (Sheaf J A)) (L : CochainComplex.Plus (Sheaf J' A))
    (b : I.obj ⟶ ((B.sheafPushforwardContinuous A J J').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj)
    {V : C} {V' : D} (t : V' ⟶ B.obj V) :
    (((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj) ⟶
    (((sheafToPresheaf J' A ⋙ (evaluation _ _).obj (op V')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj) :=
  ((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op V)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map b ≫
    (NatTrans.mapHomologicalComplex ((sheafSections J' A).map t.op)
      (ComplexShape.up ℤ)).app L.obj

variable [HasSheafify J A] [HasSheafify J' A]
variable [EnoughInjectives (Sheaf J A)] [EnoughInjectives (Sheaf J' A)]
variable [HasDerivedCategory (Sheaf J A)] [HasDerivedCategory (Sheaf J' A)]
variable [HasDerivedCategory A] {V W : C} (j : W ⟶ V) {V' W' : D} (j' : W' ⟶ V')
variable (P : ObjectProperty (DerivedCategory.Plus (Sheaf J A)))
variable (P' : ObjectProperty (DerivedCategory.Plus (Sheaf J' A)))

/-- Pair functoriality on injective representatives, with no choice of support map:
that map is uniquely determined by its kernel-inclusion square. The section maps are
explicitly those of the adjoint chain map, followed by restriction. All representatives
and their identifications with derived coefficients are quantified; thus this also gives
independence of representatives. Identity and composition follow from those of the chain
maps and their homology maps. Source: blueprint proof Steps 6-8; Milne, Section 9,
Theorem 9.4; Stacks, Tags 070I and 0117 (blueprint: thm-pur-with-support-exactness). -/
def SupportSequencePairNatural
    (δ : SupportSequenceBoundary J A j P) (δ' : SupportSequenceBoundary J' A j' P')
    (t : V' ⟶ B.obj V) (s : W' ⟶ B.obj W) : Prop :=
  ∀ (I : CochainComplex.Plus (Sheaf J A)) (L : CochainComplex.Plus (Sheaf J' A))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (L.obj.X n)]
    (K : P.FullSubcategory) (K' : P'.FullSubcategory)
    (e : DerivedCategory.Plus.Q.obj I ≅ K.obj)
    (e' : DerivedCategory.Plus.Q.obj L ≅ K'.obj)
    (b : I.obj ⟶ ((B.sheafPushforwardContinuous A J J').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.obj),
    ∃! z : (((supportedSectionsFunctor J A j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj) ⟶
      (((supportedSectionsFunctor J' A j').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L.obj),
      z ≫ (NatTrans.mapHomologicalComplex (supportedSectionsInclusion J' A j')
          (ComplexShape.up ℤ)).app L.obj =
        (NatTrans.mapHomologicalComplex (supportedSectionsInclusion J A j)
          (ComplexShape.up ℤ)).app I.obj ≫ supportPairComplexSectionMap J J' A B I L b t ∧
      ∀ q : ℤ,
        supportSequenceModelBoundary J A j P δ I K e q ≫
          (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) (q + 1)).map z =
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).map
          (supportPairComplexSectionMap J J' A B I L b s) ≫
            supportSequenceModelBoundary J' A j' P' δ' L K' e' q

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Etale

/-- The existing torsion-cohomology predicate restricted along the inclusion of `D⁺`.
Source: blueprint `def-weil-pbc-etale-sheaves`, final paragraph, and Milne, Section 9,
Theorem 9.4 (blueprint: thm-pur-with-support-exactness). -/
abbrev supportSequenceCoefficients (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  ObjectProperty.inverseImage
    (fun K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ↦
      Scheme.HasTorsionEtaleCohomology K) DerivedCategory.Plus.ι

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry

/-- The long exact support sequence, natural in coefficients and in pairs, on both sites.
The first factor is the etale assertion on the full subcategory of `D⁺` with torsion
cohomology; the second is its pro-etale analogue with finite-torsion coefficients. For
sheaves take the degree-zero single functor: the canonical comparison
`Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso` identifies these groups and
maps with the natural-number right derived functors of the support definition.

The open complement is the actual open subscheme `i.openComplement`. In the pair clause
`t` and `s` are arrows over `X'` from its terminal and open objects to their base changes.
The terminal arrow is unique and exists; the open arrow exists exactly when
`U' ⊆ f⁻¹(U)`. Their displayed square encodes the restriction square. No Cartesian-pair,
quasi-compactness, Noetherian, constructibility, or descent hypothesis is imposed.

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4, with the site argument
of Stacks, Tags 093X, 03F3 and 0117 (blueprint: thm-pur-with-support-exactness).

Proof plan, following the node:
1. By lem-weil-pbc-site-sheaves-enough-injectives and
   lem-weil-pbc-dplus-injective-representative, represent each bounded-below object by a
   bounded-below complex of injective abelian sheaves (of coefficient modules in the
   pro-etale clause). For a sheaf start in degree zero. Torsion is required of cohomology,
   not of injective terms.
2. The support definition is the kernel of restriction on every term. By
   lem-weil-pbc-right-derived-plus-injective, supported, global and open derived sections
   are computed by these three section complexes; the comparison used here is exactly
   the right-derived-functor unit, followed by the specified representative isomorphism.
3. By lem-weil-pbc-injective-sheaf-mono-restriction, restriction of an injective along the
   open monomorphism is surjective. Thus these complexes form a short exact sequence.
   For module coefficients use the same free-module-on-a-monomorphism argument.
4. By lem-weil-pbc-site-restriction-injectives,
   lem-weil-pbc-cohomology-over-object-localization and
   lem-weil-pbc-etale-cohomology-over-open, open evaluation computes the cohomology on the
   open subscheme with restricted coefficients.
5. Apply lem-weil-pbc-complex-ses-homology-long-exact at each integer degree. Its three
   exactness assertions give the three conjuncts of SupportSequenceExact. For sheaves
   use the single-functor comparison to recover R^q and the initial zero term.
6. By lem-weil-pbc-kinjective-hom-derived, a derived coefficient map is represented by a
   chain map, unique up to homotopy. By lem-weil-pbc-complex-ses-long-exact-naturality its
   homology maps commute with the boundary. Evaluation and the support kernel preserve
   homotopies, giving a natural transformation on the torsion full subcategory and
   independence of all choices.
7. For a pair map and a coefficient map f⁻¹K → L, use exactness of inverse image
   (prop-weil-pbc-inverse-image-exact and lem-weil-pbc-site-pullback-abelian-exact) and
   lem-weil-pbc-kinjective-hom-derived to choose the adjoint chain map b : I → f_*J.
   Its section maps are precisely supportPairComplexSectionMap at t and s. Their square
   commutes, so the kernel map exists uniquely and the same long-exact naturality gives
   the boundary square. Homotopies restrict to kernels. Identity maps induce identities;
   for two pair maps, adjunction and lem-weil-pbc-inverse-image-composition (respectively
   lem-weil-pbc-site-morphism-composition) identify the adjoint of the composite with
   I → f_*J → f_*g_*P. Evaluation, restriction and kernel functoriality identify all
   three maps with the composites, hence the identity and composition laws hold.
8. Repeat the identical construction on the small pro-etale site. By
   lem-weil-proetale-weakly-etale-localization and
   lem-weil-pbc-proetale-restriction-injectives the localized site and its coefficient
   restriction are those of U. Steps 1-7 apply directly, including non-descending
   coefficients. Use the specified finite quotient rings A_{E,n}, with their canonical
   universe lift. -/
theorem exists_support_longExact :
    (∃ δ : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        Sheaf.SupportSequenceBoundary X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (Etale.supportRestrictionArrow i) (Etale.supportSequenceCoefficients X),
      (∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        Sheaf.SupportSequenceExact X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (Etale.supportRestrictionArrow i) (Etale.supportSequenceCoefficients X) (δ i)) ∧
      (∀ {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
        (i' : Z' ⟶ X') [IsClosedImmersion i'] (f : X' ⟶ X)
        (t : Scheme.Etale.mk (𝟙 X') ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 X)))
        (s : Scheme.Etale.mk i'.openComplement.ι ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ f).obj
            (Scheme.Etale.mk i.openComplement.ι)),
        s ≫ (MorphismProperty.Over.pullback @Etale ⊤ f).map
            (Etale.supportRestrictionArrow i) = Etale.supportRestrictionArrow i' ≫ t →
        Sheaf.SupportSequencePairNatural X.smallEtaleTopology X'.smallEtaleTopology
          AddCommGrpCat.{u + 1} (MorphismProperty.Over.pullback @Etale ⊤ f)
          (hB := Etale.isContinuous_overPullback f)
          (Etale.supportRestrictionArrow i) (Etale.supportRestrictionArrow i')
          (Etale.supportSequenceCoefficients X) (Etale.supportSequenceCoefficients X')
          (δ i) (δ i') t s)) ∧
    (∀ (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n),
      ∃ δ : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
          Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
            (ProEtale.supportRestrictionArrow i) ⊤,
        (∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
          Sheaf.SupportSequenceExact (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
            (ProEtale.supportRestrictionArrow i) ⊤ (δ i)) ∧
        (∀ {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
          (i' : Z' ⟶ X') [IsClosedImmersion i'] (f : X' ⟶ X)
          (t : Scheme.ProEt.mk (𝟙 X') ⟶
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj (Scheme.ProEt.mk (𝟙 X)))
          (s : Scheme.ProEt.mk i'.openComplement.ι ⟶
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
              (Scheme.ProEt.mk i.openComplement.ι)),
          s ≫ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
              (ProEtale.supportRestrictionArrow i) = ProEtale.supportRestrictionArrow i' ≫ t →
          Sheaf.SupportSequencePairNatural (Scheme.ProEt.topology X) (Scheme.ProEt.topology X')
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)))
            (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
            (hB := Scheme.ProEt.isContinuous_overPullback f)
            (ProEtale.supportRestrictionArrow i) (ProEtale.supportRestrictionArrow i')
            ⊤ ⊤ (δ i) (δ i') t s)) := by
  sorry

end AlgebraicGeometry
