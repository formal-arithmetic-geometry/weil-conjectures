/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSections
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange

/-!
# Resolution model for the torsion pro-étale stalk comparison

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-cor-pbc-torsion-stalk/sk-cor-pbc-torsion-stalk-proetale-point.proof.md,
(3), final sentence (blueprint: lem-pbc-torsion-stalk-proetale-resolution-map).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Canonical Leray identification, derived from the actual direct-image evaluation.
Source: blueprint proof (3), composition of sections and direct image
(blueprint: lem-pbc-torsion-stalk-proetale-resolution-map). -/
noncomputable def torsionStalkProEtaleLerayIso (Λ : Type (u + 1)) [CommRing Λ]
    {Z P : Scheme.{u}} (a : Z ⟶ P) :
    (lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctor ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) P ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z :=
  letI := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorCompIso' _ _
    (globalSectionsLowerStarIso (ModuleCat.{u + 1} Λ) a)

/-- Point sections of the fixed mate, with the canonical source and target Leray
identifications. The point comparison is the derived comparison unit, as defined in
`boundedBelowComparisonGlobalSections`; exact point sections identify it with the
termwise comparison-sections unit at P. Thus this construction uses the specified
unit, not an arbitrary isomorphism of endpoints.
Source: blueprint proof (2), (3), final sentence
(blueprint: lem-pbc-torsion-stalk-proetale-resolution-map). -/
noncomputable def torsionStalkPointSectionsBeta
    (Ω : Type u) [Field Ω] (Λ : Type (u + 1)) [CommRing Λ]
    {Z : Scheme.{u}} (a : Z ⟶ Spec (.of Ω))
    (F : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (DerivedCategory.Plus.ι.obj F) ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (DerivedCategory.Plus.ι.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryPlus.obj F)) :=
  (Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} Λ) a).inv.app (DerivedCategory.Plus.ι.obj F) ≫
    (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).map
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctorPlusCompatibility.inv.app F) ≫
    (boundedBelowComparisonGlobalSections (Spec (.of Ω)) Λ).app
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctorPlus.obj F) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).map
      (DerivedCategory.Plus.ι.map
        ((Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange a (ModuleCat.{u + 1} Λ))).app F)) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).map
      ((lowerStar (ModuleCat.{u + 1} Λ) a).rightDerivedFunctorPlusCompatibility.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryPlus.obj F)) ≫
    (torsionStalkProEtaleLerayIso Λ a).hom.app _

/-- The etale section-resolution identification, using the inverse derived unit on
an injective complex and the terminal-object evaluation isomorphism.
Source: blueprint proof (3), injective section models
(blueprint: lem-pbc-torsion-stalk-proetale-resolution-map). -/
noncomputable def torsionStalkEtaleResolutionIso (Z : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (I : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hI : ∃ n : ℤ, I.IsStrictlyGE n) (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        ((comparisonSectionComplexes Z.smallEtaleTopology Λ I).obj
          (op (Scheme.Etale.mk (𝟙 Z)))) :=
  letI (n : ℤ) := hIinj n
  letI := hI.choose_spec
  letI := CochainComplex.isKInjective_of_injective I hI.choose
  (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorObjQIso I ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
        (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          (Scheme.Etale.isTerminalMkId Z)) (ComplexShape.up ℤ)).app I)

/-- The pro-etale section-resolution identification, with the same derived-unit
normalization as its etale counterpart.
Source: blueprint proof (3), injective section models
(blueprint: lem-pbc-torsion-stalk-proetale-resolution-map). -/
noncomputable def torsionStalkProEtaleResolutionIso (Z : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℤ)
    (hJ : ∃ n : ℤ, J.IsStrictlyGE n) (hJinj : ∀ n : ℤ, Injective (J.X n)) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (DerivedCategory.Q.obj J) ≅
      DerivedCategory.Q.obj
        ((comparisonSectionComplexes (Scheme.ProEt.topology Z) Λ J).obj
          (op (Scheme.ProEt.mk (𝟙 Z)))) :=
  letI (n : ℤ) := hJinj n
  letI := hJ.choose_spec
  letI := CochainComplex.isKInjective_of_injective J hJ.choose
  (Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)).rightDerivedFunctorObjQIso J ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
        (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)
          (Scheme.ProEt.isTerminalMkId Z)) (ComplexShape.up ℤ)).app J)

/-- The target identification for a chosen resolution: compatibility of exact
comparison pullback with localization, the chosen representative, Q(j), and the
inverse derived unit on J. Every isomorphism here is the canonical one specified
in the source; the only resolution data are I, its representative, and j.
Source: blueprint proof (3), injective section models
(blueprint: lem-pbc-torsion-stalk-proetale-resolution-map). -/
noncomputable def torsionStalkResolutionTargetIso (Z : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (I : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (eF : DerivedCategory.Plus.ι.obj F ≅ DerivedCategory.Q.obj I)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℤ)
    (hJ : ∃ n : ℤ, J.IsStrictlyGE n) (hJinj : ∀ n : ℤ, Injective (J.X n))
    (j : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) (hj : QuasiIso j) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (DerivedCategory.Plus.ι.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryPlus.obj F)) ≅
      DerivedCategory.Q.obj
        ((comparisonSectionComplexes (Scheme.ProEt.topology Z) Λ J).obj
          (op (Scheme.ProEt.mk (𝟙 Z)))) :=
  letI := hj
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).mapIso
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryPlusCompatibility.app F ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategory.mapIso eF ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryFactors.app I ≪≫
      asIso (DerivedCategory.Q.map j)) ≪≫
    torsionStalkProEtaleResolutionIso Z Λ J hJ hJinj

/-- The actual displayed section cochain map, transported by the canonical
resolution identifications to derived global sections. Uses the published
`comparisonResolutionSections`, without redefining the comparison unit.
Source: blueprint proof (3), final sentence
(blueprint: lem-pbc-torsion-stalk-proetale-resolution-map). -/
noncomputable def torsionStalkResolutionGlobalSections (Z : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (I : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hI : ∃ n : ℤ, I.IsStrictlyGE n) (hIinj : ∀ n : ℤ, Injective (I.X n))
    (eF : DerivedCategory.Plus.ι.obj F ≅ DerivedCategory.Q.obj I)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℤ)
    (hJ : ∃ n : ℤ, J.IsStrictlyGE n) (hJinj : ∀ n : ℤ, Injective (J.X n))
    (j : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) (hj : QuasiIso j) :
    (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (DerivedCategory.Plus.ι.obj F) ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (DerivedCategory.Plus.ι.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryPlus.obj F)) :=
  (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map eF.hom ≫
    (torsionStalkEtaleResolutionIso Z Λ I hI hIinj).hom ≫
    DerivedCategory.Q.map
      ((comparisonResolutionSections Z Λ I J j).app (op (Scheme.Etale.mk (𝟙 Z)))) ≫
    (torsionStalkResolutionTargetIso Z Λ F I eF J hJ hJinj j hj).inv

/-- Point sections of the specified derived restriction mate equal the displayed
unit-and-resolution section map, and that map is the canonical global comparison.
The last clauses state naturality in every derived morphism and independence of
both resolutions under the preceding canonical identifications.
Source: blueprint proof (3), final sentence
(blueprint: lem-pbc-torsion-stalk-proetale-resolution-map).

Proof: expand the underived restriction mate as epsilon_P after A_P(r eta_Z).
Naturality and the triangle identity give R_P(b) eta_P = r eta_Z. Evaluate at
P and use the comparison-sections unit there, degree by degree. The universal
factorization of rightDerivedFunctorPlusBaseChange identifies the fixed beta
on I with b_I followed by the derived direct-image unit. Naturality at j then
replaces that target by J; the units on injective I and J are invertible.
Exact point sections and direct-image evaluation at P give exactly the section
map on Z. Transposing j through the derived comparison adjunction identifies
R_Z(j) eta_Z with its derived unit, so applying etale derived sections and the
canonical composition isomorphism yields boundedBelowComparisonGlobalSections.
Finally bounded-below injective complexes are K-injective. The Hom-bijection
lifts identities and arbitrary derived morphisms to homotopy classes between
resolutions. The two composites with j are homotopic; additive sections preserve
these homotopies. This proves naturality and resolution independence. -/
theorem torsionStalkProEtaleResolutionMap
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (Λ : Type (u + 1)) [CommRing Λ]
    (Z : Scheme.{u}) (a : Z ⟶ Spec (.of Ω)) [IsProper a]
    (F : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (I : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (hI : ∃ n : ℤ, I.IsStrictlyGE n) (hIinj : ∀ n : ℤ, Injective (I.X n))
    (eF : DerivedCategory.Plus.ι.obj F ≅ DerivedCategory.Q.obj I)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℤ)
    (hJ : ∃ n : ℤ, J.IsStrictlyGE n) (hJinj : ∀ n : ℤ, Injective (J.X n))
    (j : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) (hj : QuasiIso j) :
    torsionStalkPointSectionsBeta Ω Λ a F =
        torsionStalkResolutionGlobalSections Z Λ F I hI hIinj eF J hJ hJinj j hj ∧
      torsionStalkResolutionGlobalSections Z Λ F I hI hIinj eF J hJ hJinj j hj =
        (boundedBelowComparisonGlobalSections Z Λ).app F ∧
      (∀ (F' : DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (φ : F ⟶ F'),
        (Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
            (DerivedCategory.Plus.ι.map φ) ≫ torsionStalkPointSectionsBeta Ω Λ a F' =
          torsionStalkResolutionGlobalSections Z Λ F I hI hIinj eF J hJ hJinj j hj ≫
            (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).map
              (DerivedCategory.Plus.ι.map
                ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapDerivedCategoryPlus.map φ))) ∧
      (∀ (I' : CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
          (hI' : ∃ n : ℤ, I'.IsStrictlyGE n) (hIinj' : ∀ n : ℤ, Injective (I'.X n))
          (eF' : DerivedCategory.Plus.ι.obj F ≅ DerivedCategory.Q.obj I')
          (J' : CochainComplex
            (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ℤ)
          (hJ' : ∃ n : ℤ, J'.IsStrictlyGE n) (hJinj' : ∀ n : ℤ, Injective (J'.X n))
          (j' : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I' ⟶ J') (hj' : QuasiIso j'),
        torsionStalkResolutionGlobalSections Z Λ F I hI hIinj eF J hJ hJinj j hj =
          torsionStalkResolutionGlobalSections Z Λ F I' hI' hIinj' eF' J' hJ' hJinj' j' hj') := by
  sorry

end AlgebraicGeometry.ProEtale
