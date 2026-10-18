/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Bounded-below pro-etale comparison

Source: blueprint main-20261015, sec-proetale-coefficients/sk-prop-sf-comparison,
statement and proof; Stacks Tags 099V, 099W and 03Q6 (blueprint: sk-prop-sf-comparison).

The affine formula is stated on bounded-below injective representatives. The source
complex of its comparison map is the termwise filtered colimit, which represents the
filtered derived colimit because filtered colimits of modules are exact.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The canonical global-sections comparison, obtained by applying derived etale sections
to the derived adjunction unit and then the Leray isomorphism. No finiteness or commutativity
is required of the coefficient ring. Source: Stacks 099V and 099W
(blueprint: sk-prop-sf-comparison). -/
noncomputable def boundedBelowComparisonGlobalSections (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] :
    DerivedCategory.Plus.ι ⋙ Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.ι ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X :=
  let L := (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus
  let R := comparisonLowerStar (ModuleCat.{u + 1} Λ) X
  let Γ := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X
  (Functor.leftUnitor (DerivedCategory.Plus.ι ⋙ Γ)).inv ≫
    Functor.whiskerRight (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit
      (DerivedCategory.Plus.ι ⋙ Γ) ≫
    (Functor.associator L R.rightDerivedFunctorPlus (DerivedCategory.Plus.ι ⋙ Γ)).hom ≫
    Functor.whiskerLeft L
      ((Functor.associator R.rightDerivedFunctorPlus DerivedCategory.Plus.ι Γ).inv ≫
        Functor.whiskerRight R.rightDerivedFunctorPlusCompatibility.hom Γ ≫
        (Functor.associator DerivedCategory.Plus.ι R.rightDerivedFunctor Γ).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (comparisonLowerStarCompRightDerivedGlobalSectionsIso
            (ModuleCat.{u + 1} Λ) X).hom)

/-- The derived unit, full faithfulness on D+ and the canonical global-sections comparison.
Source: blueprint main-20261015, sk-prop-sf-comparison; Stacks 099V and 099W
(blueprint: sk-prop-sf-comparison).

Proof:
1. Apply the geometric comparison to addition and each scalar endomorphism. Naturality
makes the adjunction module-linear for any ring. The inverse image preserves kernels
and, as a left adjoint, cokernels. Both functors are additive and inverse image is exact.
The general coefficient unit theorem lem-weil-pbc-comparison-grothendieck-unit gives
invertibility of the underived unit. Exactness preserves D+ by
lem-weil-pbc-exact-functor-bounded-below.
2. Good truncation gives a bounded-below representative of K. Choose a bounded-below
injective resolution I (lem-sc-bounded-below-injective-resolution). The functors of
lem-weil-pbc-right-derived-plus-injective compute right derived direct image and sections
on such resolutions; these module categories have enough injectives.
3. To construct the derived adjunction, resolve N by J. Direct image of J is K-injective
by lem-weil-pbc-right-adjoint-preserves-kinjective. Use
lem-weil-pbc-kinjective-hom-derived and lem-weil-pbc-termwise-adjunction-homotopy to identify
Hom(LM,N) with Hom(M,RRN). A resolution map j:LM -> J transposes to Rj after the unit.
4. Each LI^r is R-acyclic by lem-pe-comparison-injective-left-modules-acyclic (the general
Grothendieck-coefficient upstream interface also states this). Injective terms of J are
acyclic by lemma-weil-pbc-leray-acyclicity. Thus
lem-weil-pbc-leray-acyclicity-quasi-iso makes Rj a quasi-isomorphism. The underived unit
on I is termwise invertible by lem-weil-pbc-comparison-grothendieck-unit. Consequently
the actual derived unit, represented by Rj after that unit, is invertible.
5. The derived adjunction sends Lf to eta_H after f. Since eta_H is invertible, the actual
map on Hom sets is bijective, proving full faithfulness.
6. R preserves injectives because its left adjoint is exact. On a pro-etale injective
resolution J, etale sections of RJ equal pro-etale sections of J: direct image is
restriction and the inclusion preserves the terminal object. The equality respects
differentials and maps, and descends using lem-weil-pbc-kinjective-hom-derived. Composing
this canonical Leray comparison with derived sections of the unit gives precisely
boundedBelowComparisonGlobalSections and proves its invertibility. -/
theorem boundedBelowComparison (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] :
    IsIso (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.unit ∧
      Nonempty (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.FullyFaithful ∧
      IsIso (boundedBelowComparisonGlobalSections X Λ) := by
  sorry

/-- Section complexes, as a functor on the opposite site, constructed by evaluation in
each degree. Source: Stacks 099W and 03Q6 (blueprint: sk-prop-sf-comparison). -/
def comparisonSectionComplexes {C : Type (u + 1)} [Category.{u} C]
    (T : GrothendieckTopology C) (Λ : Type (u + 1)) [Ring Λ]
    (I : CochainComplex (Sheaf T (ModuleCat.{u + 1} Λ)) ℤ) :
    Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} Λ) ℤ :=
  ((sheafToPresheaf T (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj I).asFunctor

/-- The comparison unit followed by a resolution map, at the level of etale sheaf
complexes. Source: Stacks 099V, resolution computation of the unit
(blueprint: sk-prop-sf-comparison). -/
noncomputable def comparisonResolutionUnit (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (j : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    I ⟶ ((comparisonLowerStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J :=
  (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).inv.app I ≫
    (NatTrans.mapHomologicalComplex (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit
      (ComplexShape.up ℤ)).app I ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
        comparisonLowerStar (ModuleCat.{u + 1} Λ) X)) (ComplexShape.up ℤ)).inv.app I ≫
    ((comparisonLowerStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).map j

/-- The sectionwise canonical resolution comparison, natural on the etale site.
Source: Stacks 099V and 099W (blueprint: sk-prop-sf-comparison). -/
noncomputable def comparisonResolutionSections (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (j : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    comparisonSectionComplexes X.smallEtaleTopology Λ I ⟶
      (toProEt X).op ⋙ comparisonSectionComplexes (Scheme.ProEt.topology X) Λ J :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    (((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (comparisonResolutionUnit X Λ I J j))

/-- The canonical restriction cocone on the section complexes of an etale affine
presentation. Its vertex computes pro-etale derived sections when J is injective.
Source: Stacks 099W and 03Q6 (blueprint: sk-prop-sf-comparison). -/
noncomputable def affineComparisonResolutionCocone (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (j : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    {B : Type u} [SmallCategory B] (D : B ⥤ X.Etale)
    (c : Cone (D ⋙ toProEt X)) :
    Cocone (D.op ⋙ comparisonSectionComplexes X.smallEtaleTopology Λ I) :=
  (Cocone.precompose
    (Functor.whiskerLeft D.op (comparisonResolutionSections X Λ I J j))).obj
      ((comparisonSectionComplexes (Scheme.ProEt.topology X) Λ J).mapCocone c.op)

/-- The affine filtered derived-colimit formula, with its cohomology assertion.
Source: blueprint main-20261015, sk-prop-sf-comparison, final two paragraphs; Stacks 03Q6
(blueprint: sk-prop-sf-comparison).

Here I is any bounded-below injective representative of K, and j is any bounded-below
injective resolution of its comparison pullback. Thus the stage section complexes compute
RGamma(U_i,K), and the cocone vertex computes RGamma(U,(nu^*K)|U). Filtered colimits of
module complexes are exact, so their ordinary colimit represents the filtered derived
colimit. The map in the first clause is its canonical map to that vertex. The second
clause says the same restriction cocone induces the colimit on every cohomology group.

Proof: apply det-sf-comparison-affine-continuity, the existing detailed input in step 7
of this node's proof, to X, the arbitrary ring, K and this presentation. Its two canonical
cohomology comparisons give the displayed derived formula. The transition maps are affine:
for a ring map A -> B, the inverse image of D(f) is the affine D(f.map) in Spec B.
The exactness of filtered colimits is lem-weil-pbc-ring-modules-grothendieck-abelian;
applying it to kernels, images and quotients gives the asserted homology colimit.
In the detailed continuity argument, restrict to U using localization of the sites.
Apply the global comparison just stated on U. For a sheaf, continuity of etale cohomology
under affine cofiltered limits (Stacks 03Q6) identifies its cohomology with the filtered
colimit of the stage groups. For a bounded-below complex the hypercohomology spectral
sequence has only finitely many contributions to each total degree. Exactness of filtered
colimits therefore gives continuity in each degree. Consequently the canonical map of
section complexes is a quasi-isomorphism, proving the first clause after localization;
exactness also identifies its cohomology cocones as colimit cocones. -/
theorem affineBoundedBelowComparison (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n : ℤ, Injective (I.X n)]
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
    (hJ : CochainComplex.plus _ J) [∀ n : ℤ, Injective (J.X n)]
    (j : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso j]
    {B : Type u} [SmallCategory B] [IsCofiltered B]
    (D : B ⥤ X.Etale) [∀ b : B, IsAffine (D.obj b).left]
    (c : Cone (D ⋙ toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c)) :
    IsIso ((DerivedCategory.Q (C := ModuleCat.{u + 1} Λ)).map
      (colimit.desc _ (affineComparisonResolutionCocone X Λ I J j D c))) ∧
      ∀ n : ℤ, Nonempty (IsColimit
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} Λ)
          (ComplexShape.up ℤ) n).mapCocone
            (affineComparisonResolutionCocone X Λ I J j D c))) := by
  sorry

end AlgebraicGeometry.ProEtale

