/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.Paper.ComparisonGlobalResolutionModel
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-!
# The restriction transpose on direct-image resolutions

Source: blueprint main-20261015, prop-pur-gm-relative-kummer.proof.md, opening
paragraph; Stacks Project Tags 099R, 0B65 and 0FND
(blueprint: lem-pur-comparison-direct-image-resolution-mate).

The helpers specify the actual chain maps and the augmentation-normalized resolution
identifications. The statement includes the chain identity, the fixed derived mate,
its derived transpose, and evaluation on arbitrary terminal sections in every degree.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u vC vD uC uD

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] {U V : Scheme.{u}} (f : U ⟶ V)
variable (I : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
variable (J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)))
variable (t : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
  (.up ℤ)).obj I.obj ⟶ J.obj)

/-- The chain adjunct `h` of the supplied comparison resolution map.
Source: Stacks Tags 099R and 0B65; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionAdjunct :
    I.obj ⟶ ((comparisonLowerStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
      (.up ℤ)).obj J.obj :=
  ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
    (.up ℤ)).homEquiv I.obj J.obj t

/-- The chain map `k = δ⁻¹ ∘ u_* h`, using the restriction identity on both sites.
Source: Stacks Tags 099R and 0B65; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionRestriction :
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj I.obj ⟶
      ((comparisonLowerStar (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex (.up ℤ)).obj
        (((lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj J.obj) :=
  ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).map
      (comparisonResolutionAdjunct Λ I J t) ≫
    (NatTrans.mapHomologicalComplex
      (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} Λ)).inv (.up ℤ)).app J.obj

/-- The chain transpose `d` of the specified restriction map `k`.
Source: Stacks Tags 099R and 0B65; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionTranspose :
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex (.up ℤ)).obj
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj
          I.obj) ⟶
      ((lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj J.obj :=
  (((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).mapHomologicalComplex
    (.up ℤ)).homEquiv _ _).symm (comparisonResolutionRestriction Λ f I J t)

/-- The canonical resolution identification, using the derived comparison on `I` followed
by the inverse derived image of the augmentation. No replacement is chosen here.
Source: Stacks Tags 070K and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionIso
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory D]
    [EnoughInjectives C] (G : C ⥤ D) [G.Additive]
    (K L : CochainComplex.Plus C) [∀ n : ℤ, Injective (L.obj.X n)]
    (i : K.obj ⟶ L.obj) [QuasiIso i] :
    DerivedCategory.Plus.Q.obj (G.mapCochainComplexPlus.obj L) ≅
      G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K) :=
  haveI : IsIso (DerivedCategory.Plus.Q.map
      (ObjectProperty.homMk (X := K) (Y := L) i)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
    ((HomotopyCategory.Plus.quotient C).map (ObjectProperty.homMk (X := K) (Y := L) i))
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff i).2
      ((HomologicalComplex.mem_quasiIso_iff i).2 inferInstance))
  asIso (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L)) ≪≫
    G.rightDerivedFunctorPlus.mapIso
      (asIso (DerivedCategory.Plus.Q.map (ObjectProperty.homMk i))).symm


/-- The canonical identification `QC ≅ Ru_et,* K` induced by `i`.
Source: Stacks Tags 070K and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionEtaleIso
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [∀ n : ℤ, Injective (I.obj.X n)] (i : K.obj ⟶ I.obj) [QuasiIso i] :
    DerivedCategory.Plus.Q.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj I) ≅
      (Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        (DerivedCategory.Plus.Q.obj K) :=
  comparisonResolutionIso (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) K I i

/-- The canonical identification `QD ≅ Ru_proet,* A_U K` induced by `t ∘ A_U(i)`.
The final factor is the specified exact-localization identification for `A_U`.
Source: Stacks Tags 070K and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionProEtaleIso
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [∀ n : ℤ, Injective (J.obj.X n)] (i : K.obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    DerivedCategory.Plus.Q.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj J) ≅
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
          (DerivedCategory.Plus.Q.obj K)) :=
  comparisonResolutionIso (lowerStar (ModuleCat.{u + 1} Λ) f)
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.obj K) J
      (((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex
        (.up ℤ)).map i ≫ t) ≪≫
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlusFactorsh.app
        ((HomotopyCategory.Plus.quotient _).obj K)).symm

/-- The localized chain map transported through precisely the two resolution
identifications of the statement. Its direction is `A_V Ru_et,* K → Ru_proet,* A_U K`.
Source: Stacks Tags 099R and 0FND; blueprint resolution refinement
(blueprint: lem-pur-comparison-direct-image-resolution-mate). -/
noncomputable def comparisonResolutionDerivedMap
    (K : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (i : K.obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          (DerivedCategory.Plus.Q.obj K)) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
          (DerivedCategory.Plus.Q.obj K)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus.map
      (comparisonResolutionEtaleIso Λ f I K i).inv ≫
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.quotient _).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj I))) ≫
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
      (X := (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapCochainComplexPlus.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj I))
      (Y := (lowerStar (ModuleCat.{u + 1} Λ) f).mapCochainComplexPlus.obj J)
      (comparisonResolutionTranspose Λ f I J t)) ≫
    (comparisonResolutionProEtaleIso Λ f I J t K i).hom


/-- The restriction transpose on the supplied resolutions is the specified derived mate,
with its ordinary counit identity and its evaluation on all terminal sections.
Source: blueprint main-20261015, prop-pur-gm-relative-kummer.proof.md, opening
paragraph (resolution refinement); Stacks Tags 099R, 0B65, 070K and 0FND
(blueprint: lem-pur-comparison-direct-image-resolution-mate).

Proof: (1) The restriction isomorphism δ is the identity on `G(W ×[V] U)`,
including restriction maps and the constant coefficient action.
(2) Compose the comparison and inverse-image adjunctions in the two orders.
The conjugate-unit equation for the canonical pullback comparison identifies the
resulting Hom bijections after precomposition with `a⁰`.
(3) The adjuncts of `t ∘ A_U(εe_I)` and `εp_J ∘ p(d)` are `u_* h` and `k`.
The equality defining `k` and injectivity of the composite Hom bijection give
the asserted chain identity. This uses the termwise adjunction-homotopy interface.
(4) Exactness of the three inverse images gives their termwise localization
comparisons. The augmentations `i` and `A_U(i) ≫ t` are quasi-isomorphisms;
the K-injective computation of the right derived functors identifies their values
with `QC` and `QD`. These are exactly `comparisonResolutionEtaleIso` and
`comparisonResolutionProEtaleIso`, not arbitrary isomorphisms.
(5) The general pre-derived adjunction representative formula, with the exact
left adjoint unreplaced, computes the two derived transposes using the inverses
of the augmentations followed by the ordinary counits.
(6) Localize the chain identity and use naturality of the pullback comparison.
Cancel the exact comparison image of the etale resolution identification to obtain
that the transpose is `A_U(εe_F) ∘ a⁻¹`. Uniqueness of the adjoint transpose
identifies this map with `fixedComparisonDirectImageMatePlus`, whose counit
normalization is the canonical-mate dependency.
(7) Evaluate δ on the terminal object: it is the identity. Then evaluate the
adjunction equation `η ≫ N_V(d) = k` on a section `z`. This gives both section
identities in every degree, without a cocycle condition. Neither comparison
inverse image is required to preserve injective objects. -/
theorem comparison_direct_image_resolution_mate [Finite Λ]
    [QuasiCompact f] [QuasiSeparated f]
    [I.obj.IsStrictlyGE 0] [J.obj.IsStrictlyGE 0]
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    [I.obj.IsKInjective] [J.obj.IsKInjective]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (i : (comparisonResolutionSingle F).obj ⟶ I.obj) [QuasiIso i] [QuasiIso t] :
    (NatTrans.mapHomologicalComplex
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).inv (.up ℤ)).app
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).obj
          I.obj) ≫
      ((upperStar (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex (.up ℤ)).map
        (comparisonResolutionTranspose Λ f I J t) ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex
        (.up ℤ)).counit.app J.obj =
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).map
        (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).mapHomologicalComplex
           (.up ℤ)).counit.app I.obj) ≫ t ∧
    comparisonResolutionDerivedMap Λ f I J t (comparisonResolutionSingle F) i =
      (fixedComparisonDirectImageMatePlus Λ f).app
        (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)) ∧
    ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).homEquiv _ _).symm
        (comparisonResolutionDerivedMap Λ f I J t (comparisonResolutionSingle F) i) =
      (fixedComparisonPullbackPlus Λ f).inv.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
            (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
             (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) ∧
    ∀ (n : ℤ)
      (z : (((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj (I.obj.X n)).obj.obj
        (op (⊤_ V.Etale)))),
      ((comparisonResolutionRestriction Λ f I J t).f n).hom.app (op (⊤_ V.Etale)) z =
        ((comparisonResolutionAdjunct Λ I J t).f n).hom.app
          (op (f.Etale.obj (⊤_ V.Etale))) z ∧
      ((comparisonResolutionTranspose Λ f I J t).f n).hom.app
          (op ((Scheme.toProEt V).obj (⊤_ V.Etale)))
          (((comparisonAdjunction (ModuleCat.{u + 1} Λ) V).unit.app
            ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj (I.obj.X n))).hom.app
              (op (⊤_ V.Etale)) z) =
        ((comparisonResolutionAdjunct Λ I J t).f n).hom.app
          (op (f.Etale.obj (⊤_ V.Etale))) z := by
  sorry

end AlgebraicGeometry.ProEtale
