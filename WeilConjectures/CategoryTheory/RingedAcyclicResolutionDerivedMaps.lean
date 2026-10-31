/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.DerivedSectionsScalarCoherence
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import WeilConjectures.CategoryTheory.KInjectiveDerivedMapComputation
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Acyclic resolutions compute derived section maps

Source: Stacks Project, sites-cohomology.tex, Tag 0D6E and section-derived-functors;
derived.tex, Tag 015E (blueprint: lem-sfb-ringed-acyclic-resolution-derived-maps).

The global-sections identification is pinned by the geometric adjunction on global
elements. The derived composition is pinned by its units. The resolution comparisons
are unique isomorphisms in D+(Ab), normalized on every extension into injectives.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CoefficientDerivedSections

namespace CategoryTheory

set_option maxHeartbeats 600000 in
-- Elaborating the universal pairs and four bounded-below vertices exceeds the default budget.
/-- Acyclic-resolution comparison and its derived-map square for arbitrary ringed topoi.
Source: Stacks Project, sites-cohomology.tex, Tag 0D6E and section-derived-functors;
derived.tex, Tags 013P, 014X, 015E, 070Y
(blueprint: lem-sfb-ringed-acyclic-resolution-derived-maps).

Proof:
1. Global sections are additive and left exact. Choose injective resolutions of M,N.
   Bounded-below injective complexes are K-injective. The ringed-site K-injective
   resolution theorem and def-sfb-right-derived-functor provide universal derived pairs
   and their units, invertible on K-injectives.
2. The nonnegative augmentations are monomorphic quasi-isomorphisms. Extend them
   into the chosen injective resolutions by lem-weil-pbc-lift-along-injective-quasi-iso.
   The extensions are quasi-isomorphisms, and any two are homotopic by
   lem-weil-pbc-lift-to-injective-unique-up-to-homotopy.
3. Injectives are section-acyclic, using the identity case of
   lem-sfb-ringed-topos-injective-pushforward-global-acyclic. Apply
   lem-weil-pbc-leray-acyclicity-quasi-iso to the extensions. Their section images
   are quasi-isomorphisms. Composing their localized images with the inverse
   unit-normalized injective computations gives the two isomorphisms below.
4. Additivity preserves homotopies, so the comparisons do not depend on the extensions.
   Between two injective resolutions use the K-injective Hom bijection and
   lem-sf-kinjective-derived-map-computation. Its transition formula identifies the
   comparisons. Thus the normalization holds for every injective extension and
   determines each comparison uniquely.
5. Resolve f_*I by a bounded-below injective complex T via lambda. Both f_*I and T
   have section-acyclic terms, by the injective-pushforward global-acyclicity lemma
   (also for the identity). Leray acyclicity makes E = Q Gamma(lambda) invertible.
   The normalized ringed-topos composition comparison, applied to global sections,
   is E inverse followed by the injective computation. This gives kappa below.
6. The coefficient map followed by the derived unit is Qw in injective coordinates,
   where w = phi[0] followed by f_*j. Choose beta into T by the K-injective Hom
   bijection. The derived-map computation gives res_f(phi) in coordinates as E^-1 V,
   with V = Q Gamma(beta).
7. The composites lambda (f_*b) u and beta a agree up to homotopy after precomposing
   with r, by the augmentation square. Uniqueness into T makes them homotopic.
   Apply global sections and localization to obtain E Q Gamma(b) Q Gamma(u)
   = V Q Gamma(a), using the adjunction-normalized global-sections identification.
8. Cancel E and substitute the comparisons to get the displayed derived equality.
   All four vertices are bounded below, so this is an equality in the full D+(Ab).
   Identity f gives naturality for every map of resolutions; coefficient-compatible
   pullbacks are substitutions into the same equality, before taking cohomology.
No exactness of module inverse image or injectivity of the acyclic terms is used. -/
theorem ringedAcyclicResolutionDerivedMaps
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasTerminal C] [HasTerminal D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    [EnoughInjectives (coefficientModules A)] [EnoughInjectives (coefficientModules B)]
    [HasDerivedCategory.{w} (coefficientModules A)]
    [HasDerivedCategory.{w} (coefficientModules B)]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)) :
    ∃ (t : f.modules ⋙ coefficientSections B ≅ coefficientSections A)
      (zC : ∀ M : coefficientModules A, (coefficientSections A).obj M →
        (⊤_ (Sheaf J (Type u)) ⟶
          (sheafCompose J (forget AddCommGrpCat)).obj ((SheafOfModules.toSheaf _).obj M)))
      (zD : ∀ M : coefficientModules B, (coefficientSections B).obj M →
        (⊤_ (Sheaf K (Type u)) ⟶
          (sheafCompose K (forget AddCommGrpCat)).obj ((SheafOfModules.toSheaf _).obj M))),
      (∀ (M : coefficientModules A) (x : (coefficientSections A).obj M)
        (U : Cᵒᵖ) (s : (⊤_ (Sheaf J (Type u))).obj.obj U),
        (zC M x).hom.app U s = (Sheaf.ΓRes ((SheafOfModules.toSheaf _).obj M) U) x) ∧
      (∀ (M : coefficientModules B) (x : (coefficientSections B).obj M)
        (U : Dᵒᵖ) (s : (⊤_ (Sheaf K (Type u))).obj.obj U),
        (zD M x).hom.app U s = (Sheaf.ΓRes ((SheafOfModules.toSheaf _).obj M) U) x) ∧
      (∀ (M : coefficientModules A) (x : (coefficientSections B).obj (f.modules.obj M)),
        (f.adj.homEquiv _ _)
          (terminal.from (f.inverse.obj (⊤_ (Sheaf K (Type u)))) ≫
            zC M (t.hom.app M x)) =
          zD (f.modules.obj M) x ≫ f.underlying.hom.app M) ∧
      ∃ (RG : DerivedCategory (coefficientModules B) ⥤ DerivedCategory AddCommGrpCat.{u})
        (RH : DerivedCategory (coefficientModules A) ⥤ DerivedCategory AddCommGrpCat.{u})
        (Rf : DerivedCategory (coefficientModules A) ⥤
          DerivedCategory (coefficientModules B))
        (ηG : (coefficientSections B).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ RG)
        (ηH : (coefficientSections A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ RH)
        (ηf : f.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
          DerivedCategory.Q ⋙ Rf),
        RG.IsRightDerivedFunctor ηG
          (HomologicalComplex.quasiIso (coefficientModules B) (.up ℤ)) ∧
        RH.IsRightDerivedFunctor ηH
          (HomologicalComplex.quasiIso (coefficientModules A) (.up ℤ)) ∧
        Rf.IsRightDerivedFunctor ηf
          (HomologicalComplex.quasiIso (coefficientModules A) (.up ℤ)) ∧
        (∀ I : CochainComplex (coefficientModules B) ℤ,
          I.IsKInjective → IsIso (ηG.app I)) ∧
        (∀ I : CochainComplex (coefficientModules A) ℤ,
          I.IsKInjective → IsIso (ηH.app I) ∧ IsIso (ηf.app I)) ∧
        ∃! κ : Rf ⋙ RG ≅ RH,
          (∀ I : CochainComplex (coefficientModules A) ℤ,
            ηG.app ((f.modules.mapHomologicalComplex (.up ℤ)).obj I) ≫
              RG.map (ηf.app I) ≫ κ.hom.app (DerivedCategory.Q.obj I) =
                DerivedCategory.Q.map
                  ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app I) ≫
                  ηH.app I) ∧
          ∀ (M : coefficientModules B) (N : coefficientModules A)
            (φ : M ⟶ f.modules.obj N)
            (P : CochainComplex (coefficientModules B) ℤ)
            (S : CochainComplex (coefficientModules A) ℤ)
            [P.IsStrictlyGE 0] [S.IsStrictlyGE 0]
            (r : (CochainComplex.singleFunctor (coefficientModules B) 0).obj M ⟶ P)
            (s : (CochainComplex.singleFunctor (coefficientModules A) 0).obj N ⟶ S)
            [QuasiIso r] [QuasiIso s],
            (∀ q : ℤ, (coefficientSections B).rightAcyclic (P.X q)) →
            (∀ q : ℤ, (coefficientSections A).rightAcyclic (S.X q)) →
            ∀ u : P ⟶ (f.modules.mapHomologicalComplex (.up ℤ)).obj S,
              r ≫ u = (CochainComplex.singleFunctor (coefficientModules B) 0).map φ ≫
                (HomologicalComplex.singleMapHomologicalComplex f.modules (.up ℤ) 0).inv.app N ≫
                  (f.modules.mapHomologicalComplex (.up ℤ)).map s →
              ∃ (hM : (DerivedCategory.TStructure.t
                  (C := AddCommGrpCat.{u})).plus
                    (RG.obj (DerivedCategory.Q.obj
                      ((CochainComplex.singleFunctor (coefficientModules B) 0).obj M))))
                (hN : (DerivedCategory.TStructure.t
                  (C := AddCommGrpCat.{u})).plus
                    (RH.obj (DerivedCategory.Q.obj
                      ((CochainComplex.singleFunctor (coefficientModules A) 0).obj N))))
                (hP : (DerivedCategory.TStructure.t
                  (C := AddCommGrpCat.{u})).plus (DerivedCategory.Q.obj
                    (((coefficientSections B).mapHomologicalComplex (.up ℤ)).obj P)))
                (hS : (DerivedCategory.TStructure.t
                  (C := AddCommGrpCat.{u})).plus (DerivedCategory.Q.obj
                    (((coefficientSections A).mapHomologicalComplex (.up ℤ)).obj S))),
                ∃! c :
                  ((⟨DerivedCategory.Q.obj
                      (((coefficientSections B).mapHomologicalComplex (.up ℤ)).obj P), hP⟩ :
                      DerivedCategory.Plus AddCommGrpCat.{u}) ≅
                    ⟨RG.obj (DerivedCategory.Q.obj
                      ((CochainComplex.singleFunctor (coefficientModules B) 0).obj M)), hM⟩) ×
                  ((⟨DerivedCategory.Q.obj
                      (((coefficientSections A).mapHomologicalComplex (.up ℤ)).obj S), hS⟩ :
                      DerivedCategory.Plus AddCommGrpCat.{u}) ≅
                    ⟨RH.obj (DerivedCategory.Q.obj
                      ((CochainComplex.singleFunctor (coefficientModules A) 0).obj N)), hN⟩),
                  (∀ (I : CochainComplex (coefficientModules B) ℤ) [I.IsStrictlyGE 0]
                    [∀ q : ℤ, Injective (I.X q)]
                    (i : (CochainComplex.singleFunctor (coefficientModules B) 0).obj M ⟶ I)
                    [QuasiIso i] (a : P ⟶ I), r ≫ a = i →
                    c.1.hom.hom ≫ RG.map (DerivedCategory.Q.map i) =
                      DerivedCategory.Q.map
                        (((coefficientSections B).mapHomologicalComplex (.up ℤ)).map a) ≫
                          ηG.app I) ∧
                  (∀ (I : CochainComplex (coefficientModules A) ℤ) [I.IsStrictlyGE 0]
                    [∀ q : ℤ, Injective (I.X q)]
                    (j : (CochainComplex.singleFunctor (coefficientModules A) 0).obj N ⟶ I)
                    [QuasiIso j] (b : S ⟶ I), s ≫ b = j →
                    c.2.hom.hom ≫ RH.map (DerivedCategory.Q.map j) =
                      DerivedCategory.Q.map
                        (((coefficientSections A).mapHomologicalComplex (.up ℤ)).map b) ≫
                          ηH.app I) ∧
                  DerivedCategory.Q.map
                      (((coefficientSections B).mapHomologicalComplex (.up ℤ)).map u) ≫
                    DerivedCategory.Q.map
                      ((Functor.mapHomologicalComplexCompIso t (.up ℤ)).hom.app S) ≫
                    c.2.hom.hom =
                    c.1.hom.hom ≫
                      RG.map (DerivedCategory.Q.map
                        ((CochainComplex.singleFunctor (coefficientModules B) 0).map φ ≫
                          (HomologicalComplex.singleMapHomologicalComplex
                            f.modules (.up ℤ) 0).inv.app N) ≫
                        ηf.app
                          ((CochainComplex.singleFunctor (coefficientModules A) 0).obj N)) ≫
                      κ.hom.app (DerivedCategory.Q.obj
                        ((CochainComplex.singleFunctor (coefficientModules A) 0).obj N)) := by
  sorry

end CategoryTheory
