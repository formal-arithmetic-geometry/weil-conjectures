/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.ProEtaleClassicalDirectImagePreservation
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageComparisonCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageMateCompatibility
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate
public import Sheaf.AlgebraicGeometry.ComparisonDirectImage
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Direct-image comparison for discrete coefficients

Source: blueprint, sec-proetale-coefficients, sk-thm-pe-direct-image-comparison,
order 730; Stacks Project, Tag 09A6
(blueprint: sk-thm-pe-direct-image-comparison).

The derived pullback comparisons localize the canonical sheaf comparison. The theorem
records exactness, coherence, invertibility of the specified mate and classicality.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Direct-image comparison for arbitrary discrete constant coefficients.
Source: blueprint sk-thm-pe-direct-image-comparison, order 730; Stacks Tag 09A6
(blueprint: sk-thm-pe-direct-image-comparison).

Proof, following the node's six steps:
1. Both restrictions of a pro-etale sheaf to an etale object W/Y evaluate on
   X times_Y W with the same restriction maps. This is
   `comparisonCoefficientDirectImageIso`; its conjugate gives
   `comparisonUpperStarCompUpperStarIso`. The chosen fibre-product identifications
   yield the displayed pullback identity and composition equations
   (lem-weil-pbc-comparison-pullback).
2. Inverse image preserves constant rings: its composite with constant sheaf is
   left adjoint to global sections, hence canonically the target constant sheaf.
   Applying inverse image to scalar endomorphisms transports the module identities.
   Exactness on underlying abelian sheaves and detection of kernels and cokernels
   by forgetting scalars give exactness of all four inverse images, without finiteness.
   Apply the functors termwise and localize the sheaf comparison and its inverse.
   This constructs the asserted unbounded natural isomorphism as
   mapDerivedCategoryCompIso.symm, mapDerivedCategoryNatIso of the sheaf comparison,
   then mapDerivedCategoryCompIso. `directImageComparisonPullbackPlusIso` is its D+ form.
   Exactness commutes with cohomology and preserves each lower bound
   (lem-weil-pbc-site-pullback-abelian-exact and
   lem-weil-pbc-exact-functor-derived-factorization).
3. The canonical derived map beta is the mate of c under the derived adjunctions:
   eta_2, then R_2(c), then R_2 H(epsilon_1). This is the normalization of
   `comparisonDirectImageCanonicalMate` (def-weil-pbc-adjunction-mate).
4. For qcqs g, prop-weil-pbc-comparison-direct-image supplies an isomorphism
   e : G R_1 B = S ≅ T = R_2 H B. Full faithfulness of G and H from
   sk-prop-sf-comparison identifies Hom(G A,S) and Hom(G A,T) with Hom(L_1 A,B).
   Naturality of c and the mate formula identify postcomposition with beta_B
   with the identity under these bijections. At G A = S, surjectivity supplies
   t with t followed by beta_B equal to e. Thus e.inv followed by t is a right
   inverse of beta_B; injectivity on Hom(S,S) makes it a left inverse too.
5. A bounded-below classical M is nu_X^* K for bounded-below etale K, with the
   canonical counit isomorphism (det-pe-classical-derived-equivalence, using the
   current all-degree continuity predicate sk-def-pe-classical-definition).
   Applying Rg_* and the comparison identifies its image with nu_Y^* Rg_* K,
   which is classical by that equivalence. In each degree, naturality of the
   continuity map conjugates it by the cohomology-sheaf isomorphism and its
   colimit of stage components, proving invariance under the derived isomorphism.
6. Substitute the mate formula into the displayed unit and counit equations.
   Naturality moves the inserted maps past eta_2 and c, and the adjunction
   triangle identities cancel eta_1/epsilon_1 and eta_2/epsilon_2. Pasting the
   pullback comparison and applying lem-weil-pbc-mate-pasting gives composition;
   its identity clause gives the displayed derived direct-image identity.
   These equations concern the specified maps, including arbitrary composites. -/
theorem directImageComparison
    (Λ : Type u) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (QuasiCompact g → QuasiSeparated g →
      IsIso (comparisonDirectImageCanonicalMate (ULift.{u + 1, u} Λ) g)) ∧
      PreservesFiniteLimits
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X) ∧
      PreservesFiniteColimits
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X) ∧
      PreservesFiniteLimits
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Y) ∧
      PreservesFiniteColimits
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Y) ∧
      PreservesFiniteLimits
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g) ∧
      PreservesFiniteColimits
        (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g) ∧
      PreservesFiniteLimits
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g) ∧
      PreservesFiniteColimits
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g) ∧
      IsIso
        (((Functor.mapDerivedCategoryCompIso
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Y)
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g)).symm ≪≫
            Functor.mapDerivedCategoryNatIso
              (comparisonUpperStarCompUpperStarIso
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g) ≪≫
            Functor.mapDerivedCategoryCompIso
              (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g)
              (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X)).hom) ∧
      (∀ (U : Scheme.{u})
          (F : Sheaf U.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (𝟙 U)).hom.app F ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).map
            ((Etale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).hom.app F) =
        (ProEtale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).obj F)) ∧
      (∀ {U V W : Scheme.{u}} (f : U ⟶ V) (h : V ⟶ W)
          (F : Sheaf W.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) (f ≫ h)).hom.app F ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).map
            ((Etale.upperStarComp
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f h).hom.app F) =
        (ProEtale.upperStarComp
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f h).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) W).obj F) ≫
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f).map
            ((comparisonUpperStarCompUpperStarIso
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) h).hom.app F) ≫
          (comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f).hom.app
              ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) h).obj F)) ∧
      (∀ A : DerivedCategory.Plus
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Y).mapDerivedCategoryPlus.map
            ((Etale.upperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.unit.app A) ≫
          (comparisonDirectImageCanonicalMate (ULift.{u + 1, u} Λ) g).app
            ((Etale.upperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).mapDerivedCategoryPlus.obj A) =
        (ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.unit.app
            ((comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) Y).mapDerivedCategoryPlus.obj A) ≫
          (ProEtale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).rightDerivedFunctorPlus.map
              ((directImageComparisonPullbackPlusIso (ULift.{u + 1, u} Λ) g).hom.app A)) ∧
      (∀ B : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))),
        (ProEtale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).mapDerivedCategoryPlus.map
            ((comparisonDirectImageCanonicalMate (ULift.{u + 1, u} Λ) g).app B) ≫
          (ProEtale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.counit.app
              ((comparisonUpperStar
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X).mapDerivedCategoryPlus.obj B) =
        (directImageComparisonPullbackPlusIso (ULift.{u + 1, u} Λ) g).hom.app
          ((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).rightDerivedFunctorPlus.obj B) ≫
          (comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) X).mapDerivedCategoryPlus.map
              ((Etale.upperStarLowerStarAdjunction
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).derivedAdjunctionPlus.counit.app B)) ∧
      (∀ (U : Scheme.{u})
          (L : DerivedCategory.Plus
            (Sheaf U.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))),
        (Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange (𝟙 U)
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).app L ≫
          (Functor.rightDerivedFunctorPlusNatIso
            (lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U) ≪≫
              Functor.rightDerivedFunctorPlusIdIso _).hom.app
            (((comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).mapDerivedCategoryPlus).obj L) =
        ((comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).mapDerivedCategoryPlus).map
            ((Functor.rightDerivedFunctorPlusNatIso
              (Etale.lowerStarId (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U) ≪≫
                Functor.rightDerivedFunctorPlusIdIso _).hom.app L)) ∧
      (∀ {U V W : Scheme.{u}} (f : U ⟶ V) (h : V ⟶ W)
          (L : DerivedCategory.Plus
            (Sheaf U.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))),
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) W).mapDerivedCategoryPlus.map
          ((etaleComparisonDirectImageCompIso (ULift.{u + 1, u} Λ) f h).hom.app L) ≫
          (Functor.rightDerivedFunctorPlusBaseChange
            (lowerStarComparisonUpperStarBaseChange (f ≫ h)
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).app L =
        (Functor.rightDerivedFunctorPlusBaseChange
          (lowerStarComparisonUpperStarBaseChange h
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).app
          (((Etale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) f).rightDerivedFunctorPlus).obj L) ≫
          ((ProEtale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) h).rightDerivedFunctorPlus).map
            ((Functor.rightDerivedFunctorPlusBaseChange
              (lowerStarComparisonUpperStarBaseChange f
                (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)))).app L) ≫
          (proEtaleComparisonDirectImageCompIso (ULift.{u + 1, u} Λ) f h).hom.app
            (((comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) U).mapDerivedCategoryPlus).obj L)) ∧
      (QuasiCompact g → QuasiSeparated g →
        ∀ M : Scheme.proEtaleDerivedCategory X Λ,
        (∃ n : ℤ, DerivedCategory.IsGE M n) →
        IsClassicalComplex (X := X) Λ M →
          IsClassicalComplex (X := Y) Λ
            ((Scheme.proEtaleConstantDerivedDirectImage g Λ).obj M)) := by
  have hcoh := inverseImageComparisonCoherence Λ g
  have hmate := directImageMateCompatibility Λ g
  refine ⟨?_, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hcoh.1, hcoh.2,
    hmate.1, hmate.2, ?_, ?_, ?_⟩
  · intro hqc hqs
    let := hqc
    let := hqs
    exact isIso_comparisonDirectImagePlus (ULift.{u + 1, u} Λ) g
  · exact comparisonDirectImagePlus_id (ULift.{u + 1, u} Λ)
  · exact fun f h L ↦ comparisonDirectImagePlus_comp (ULift.{u + 1, u} Λ) f h L
  · intro hqc hqs M hM hc
    let := hqc
    let := hqs
    exact classicalDirectImagePreservation Λ g M hM hc

end AlgebraicGeometry.ProEtale
