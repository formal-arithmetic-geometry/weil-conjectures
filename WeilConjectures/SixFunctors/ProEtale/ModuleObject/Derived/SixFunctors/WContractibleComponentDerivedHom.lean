/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Affine.AffineComponentSiteProjection
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.WContractibleClopenPartition
import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import WeilConjectures.SixFunctors.Supporting.StoneanCover
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Projective
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationTranspose
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Component pullback on a w-contractible affine

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.2), and proof
(blueprint: lem-sfb-wcontractible-component-derived-hom).

The component inverse image and its termwise derived functor are the recorded ones.
The monoidal localization square fixes the derived tensorator, so the internal-Hom
comparison is the actual mate of pulled-back evaluation. Global sections are rendered
as additive morphisms from the coefficient unit, with their canonical pullback formula.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Additive global sections of internal modules, represented by the coefficient unit.
This is the ordinary global-sections functor, before deriving it.
Source: HRS Section 3 and Proposition 4.3(1); Stacks 08JA
(blueprint: lem-sfb-wcontractible-component-derived-hom). -/
abbrev componentGlobalSections {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{u + 1} C]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A] :=
  preadditiveCoyoneda.obj (op (𝟙_ (Mod (Sheaf J Ab.{u + 1}) A)))

/-- The ordinary tensor structure of component pullback: the existing mapMod tensorator
followed by restriction along the inverse coefficient isomorphism.
Source: HRS (4.1) and Proposition 4.3(1)
(blueprint: lem-sfb-wcontractible-component-derived-hom). -/
instance componentModuleCanonicalMonoidal
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (W : Scheme.{u}) [IsAffine W]
    [(componentTests W).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (Scheme.ProEt.topology W)]
    [(componentInverse W).Braided]
    [PreservesFiniteLimits (componentInverse W)]
    [PreservesFiniteColimits (componentInverse W)]
    (α : (componentInverse W).mapMon.obj
        (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
        Mon.mk (condensedRingObj Λ.X W)) :
    (componentModules Λ.X W α).Monoidal :=
  inferInstanceAs (((componentInverse W).mapMod
    (profiniteCoefficient Λ.X (affineComponentSpace W)) ⋙ Mod.comap α.inv.hom).Monoidal)

/-- Normalization of the component tensorator and unit by the fixed localization maps.
The ordinary comonoidal maps are induced degreewise by the actual module pullback.
Source: HRS (4.1), Section 3 derived pullback, and Proposition 4.3(1)
(blueprint: lem-sfb-wcontractible-component-derived-hom). -/
def ComponentDerivedMonoidalNormalization
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (W : Scheme.{u}) [IsAffine W]
    [(componentTests W).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
      (Scheme.ProEt.topology W)]
    [(componentInverse W).Braided]
    [PreservesFiniteLimits (componentInverse W)]
    [PreservesFiniteColimits (componentInverse W)]
    (α : (componentInverse W).mapMon.obj
        (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
        Mon.mk (condensedRingObj Λ.X W))
    [PreservesFiniteLimits (componentModules Λ.X W α)]
    [PreservesFiniteColimits (componentModules Λ.X W α)]
    [PreservesColimitsOfSize.{0, 0} (componentModules Λ.X W α)]
    [(componentModules Λ.X W α).mapDerivedCategory.Monoidal] : Prop :=
  (∀ P Q : HomotopyCategory
      (Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        Ab.{u + 1}) (profiniteCoefficient Λ.X (affineComponentSpace W)))
      (ComplexShape.up ℤ),
    Functor.LaxMonoidal.μ (componentModules Λ.X W α).mapDerivedCategory
        (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj Q) ≫
      (componentModules Λ.X W α).mapDerivedCategory.map
        (Functor.LaxMonoidal.μ DerivedCategory.Qh P Q) ≫
      (componentModules Λ.X W α).mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
      DerivedCategory.Qh.map
        (Functor.OplaxMonoidal.δ
          ((componentModules Λ.X W α).mapHomotopyCategory (ComplexShape.up ℤ)) P Q) =
      ((componentModules Λ.X W α).mapDerivedCategoryFactorsh.hom.app P ⊗ₘ
        (componentModules Λ.X W α).mapDerivedCategoryFactorsh.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        (((componentModules Λ.X W α).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj P)
        (((componentModules Λ.X W α).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj Q)) ∧
  (Functor.LaxMonoidal.ε (componentModules Λ.X W α).mapDerivedCategory ≫
      (componentModules Λ.X W α).mapDerivedCategory.map
        (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
      (componentModules Λ.X W α).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) ≫
      DerivedCategory.Qh.map (Functor.OplaxMonoidal.η
        ((componentModules Λ.X W α).mapHomotopyCategory (ComplexShape.up ℤ))) =
    Functor.LaxMonoidal.ε DerivedCategory.Qh)

/-- The component inverse image preserves internal Hom on all unbounded derived objects,
is fully faithful, and identifies derived global sections by the pullback map.
Source: HRS Proposition 4.3(1), equation (4.2), and proof
(blueprint: lem-sfb-wcontractible-component-derived-hom).

Proof:
1. The component-site factorization identifies the pulled-back coefficient with p_W^*Λ.
   Geometric inverse image is exact, and the ringed-topos tensor theorem supplies the
   strong symmetric monoidal termwise derived functor and its monoidal localization square.
2. For an extremally disconnected E over S, the component-site construction gives W_E.
   Its closed points are W^c times over S with E, its local rings come from W, and its
   component space is E. Thus W_E is w-contractible, including E empty.
3. Split finite covers on a w-contractible affine U by its clopen partition. Component
   pullback evaluates there as M(π₀U), with the same scalar action. Slice localization and
   exact contractible evaluation give RΓ(U,π* K) = RΓ(π₀U,K) termwise on any complex.
4. Stonean covers detect exactness. Evaluating component direct image on E is evaluation
   on W_E, hence it is exact. The ordinary adjunction unit evaluates to the identity M(E).
5. Localize this exact adjunction. Its unit stays invertible, proving full faithfulness
   on the entire unbounded derived category, also after restriction to each such U.
6. At U=W the exact section comparison has the unit/pullback formula stated below.
   Deriving this very comparison gives the natural isomorphism of full derived sections.
7. Restriction to U commutes with component pullback, since both evaluate on each
   w-contractible V over U by the same component maps and coefficient actions.
8. Apply the internal-Hom sections model and slice evaluation transpose theorem. On U,
   the comparison in cohomological degree n is pullback on Hom(K,L[n]), bijective by
   step 5. This identifies the comparison as the mate of pulled-back evaluation.
9. The cone has zero sections of every cohomology sheaf on the w-contractible basis.
   The sheaf condition kills these sheaves, so the comparison is invertible. All formulas
   come from units, restrictions and evaluation, hence are natural. No bounds or
   finiteness conditions on complexes or coefficients occur. -/
theorem wContractible_component_derived_hom
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (W : Scheme.{u}) [IsAffine W] [IsWContractibleRing Γ(W, ⊤)] :
    ∃ (_ : (componentTests W).IsContinuous
        ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
        (Scheme.ProEt.topology W)),
      ∃ (_ : (componentInverse W).Braided)
        (_ : PreservesFiniteLimits (componentInverse W))
        (_ : PreservesFiniteColimits (componentInverse W)),
      ∃ α : (componentInverse W).mapMon.obj
          (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace W))) ≅
          Mon.mk (condensedRingObj Λ.X W),
        (∃ β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
              (affineComponentSpace W) ⋙ componentInverse W ≅ upperStarFromPoint W,
          NatTrans.IsMonoidal β.hom ∧ α.hom.hom = β.hom.app Λ.X) ∧
        ∃ (_ : PreservesFiniteLimits (componentModules Λ.X W α))
          (_ : PreservesFiniteColimits (componentModules Λ.X W α))
          (_ : PreservesColimitsOfSize.{0, 0} (componentModules Λ.X W α)),
        ∃ (_ : (componentModules Λ.X W α).mapDerivedCategory.Monoidal),
          ComponentDerivedMonoidalNormalization Λ W α ∧
          (∀ K L : Evaluation.D
              ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
              (profiniteCoefficient Λ.X (affineComponentSpace W)),
            IsIso ((Functor.LaxMonoidal.ihomComparison
              (componentModules Λ.X W α).mapDerivedCategory K).natTrans.app L)) ∧
          Nonempty (componentModules Λ.X W α).mapDerivedCategory.FullyFaithful ∧
          ∃ θ : componentGlobalSections
                ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
                (profiniteCoefficient Λ.X (affineComponentSpace W)) ≅
              componentModules Λ.X W α ⋙
                componentGlobalSections (Scheme.ProEt.topology W) (condensedRingObj Λ.X W),
            (∀ (M : Mod
                (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
                  Ab.{u + 1}) (profiniteCoefficient Λ.X (affineComponentSpace W)))
                (f : 𝟙_ _ ⟶ M),
              (θ.hom.app M) f = Functor.LaxMonoidal.ε (componentModules Λ.X W α) ≫
                (componentModules Λ.X W α).map f) ∧
            ∃ γ : (componentGlobalSections
                ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
                (profiniteCoefficient Λ.X (affineComponentSpace W))).rightDerivedFunctor ≅
              (componentModules Λ.X W α).mapDerivedCategory ⋙
                (componentGlobalSections (Scheme.ProEt.topology W)
                  (condensedRingObj Λ.X W)).rightDerivedFunctor,
              ∀ P : HomotopyCategory
                  (Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
                    Ab.{u + 1}) (profiniteCoefficient Λ.X (affineComponentSpace W)))
                  (ComplexShape.up ℤ),
                (componentGlobalSections
                    ((coherentTopology Profinite.{u}).over (affineComponentSpace W))
                    (profiniteCoefficient Λ.X (affineComponentSpace W))).rightDerivedFunctorUnit.app
                      P ≫ γ.hom.app (DerivedCategory.Qh.obj P) =
                  DerivedCategory.Qh.map
                    ((NatTrans.mapHomotopyCategory θ.hom (ComplexShape.up ℤ)).app P) ≫
                  (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
                    (componentModules Λ.X W α)
                    (componentGlobalSections (Scheme.ProEt.topology W)
                      (condensedRingObj Λ.X W))).app P := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
