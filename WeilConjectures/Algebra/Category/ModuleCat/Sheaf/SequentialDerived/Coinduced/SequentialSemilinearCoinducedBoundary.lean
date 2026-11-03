/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedComplexes
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
public import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedKernel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedEpi
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedCompatibility

/-! # The natural distinguished coinduced resolution triangle

Source: Stacks 0152, 015F and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace SheafOfModules.SequentialDerived.Coinduced

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The explicit ordinary coinduced sequence is short exact.
Source: Stacks 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-boundary).
Proof: augmentation is monic, its image is the compatible-family kernel, and finite
descending recursion proves epimorphy of the adjacent difference. -/
theorem complexSequence_shortExact (K : CochainComplex (StrictRingSystem B) ℤ) :
    (complexSequence B K).ShortExact :=
  ShortComplex.ShortExact.mk' (complexSequence_exact B K)
    (complexAugmentation_mono B K) (complexDifference_epi B K)

/-- The canonical mapping-cone boundary of the ordinary short exact sequence is natural.
Source: Stacks 0152
(blueprint: lem-sf-sequential-semilinear-coinduced-boundary). -/
def complexBoundary : complexRelationsFunctor B ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory (StrictRingSystem B)) (1 : ℤ) where
  app K := DerivedCategory.triangleOfSESδ (complexSequence_shortExact B K)
  naturality {K L} f :=
    (DerivedCategory.triangleOfSESδ_naturality (complexSequence_shortExact B K)
      (complexSequence_shortExact B L) (complexSequenceMap B f)).symm

/-- Transport the canonical mapping-cone boundary through the actual product comparison.
Source: Stacks 015F
(blueprint: lem-sf-sequential-semilinear-coinduced-boundary). -/
def transportedComplexBoundary : DerivedCategory.Q ⋙ relationsFunctor B ⟶
    DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory (StrictRingSystem B)) (1 : ℤ) :=
  (NatIso.ofComponents (fun K ↦ asIso ((relationsComparison B).app K))
    (fun f ↦ (relationsComparison B).naturality f)).inv ≫ complexBoundary B

/-- Descend the transported canonical boundary through localization.
Source: Stacks 015F
(blueprint: lem-sf-sequential-semilinear-coinduced-boundary). -/
def boundary : relationsFunctor B ⟶
    shiftFunctor (DerivedCategory (StrictRingSystem B)) (1 : ℤ) :=
  (Localization.whiskeringLeftFunctor' DerivedCategory.Q
    (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
    (DerivedCategory (StrictRingSystem B))).preimage (transportedComplexBoundary B)

/-- On a complex representative the descended map is the prescribed cone boundary.
Source: Stacks 015F
(blueprint: lem-sf-sequential-semilinear-coinduced-boundary).
Proof: precomposition with localization sends the fully faithful preimage back to
the transported transformation. Evaluate that equality at the given complex. -/
theorem boundary_rep (K : CochainComplex (StrictRingSystem B) ℤ) :
    (boundary B).app (DerivedCategory.Q.obj K) =
      inv ((relationsComparison B).app K) ≫
        DerivedCategory.triangleOfSESδ (complexSequence_shortExact B K) :=
  congr_app (Functor.map_preimage
    (Localization.whiskeringLeftFunctor' DerivedCategory.Q
      (HomologicalComplex.quasiIso (StrictRingSystem B) (.up ℤ))
      (DerivedCategory (StrictRingSystem B))) (transportedComplexBoundary B)) K

/-- The coinduced resolution triangle with its actual augmentation and difference.
Source: Stacks 0152, 015F
(blueprint: lem-sf-sequential-semilinear-coinduced-boundary). -/
def coinducedTriangle (N : DerivedCategory (StrictRingSystem B)) :
    Triangle (DerivedCategory (StrictRingSystem B)) :=
  Triangle.mk (augmentation B N) (difference B N) ((boundary B).app N)

/-- The coinduced resolution triangle is distinguished at every derived object.
Source: Stacks 0152, 015F, 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-boundary).
Proof: at Q(K), compare with the distinguished triangle of the explicit ordinary
short exact sequence, using the canonical comparison isomorphisms. Compatibility
of augmentation and difference gives the first two squares; the definition of the
boundary gives the third. Every derived object is isomorphic to a complex image,
and naturality supplies the isomorphism of triangles. -/
theorem coinducedTriangle_distinguished (N : DerivedCategory (StrictRingSystem B)) :
    coinducedTriangle B N ∈ distTriang (DerivedCategory (StrictRingSystem B)) := by
  have hQ (K : CochainComplex (StrictRingSystem B) ℤ) :
      coinducedTriangle B (DerivedCategory.Q.obj K) ∈
        distTriang (DerivedCategory (StrictRingSystem B)) := by
    let e : DerivedCategory.triangleOfSES (complexSequence_shortExact B K) ≅
        coinducedTriangle B (DerivedCategory.Q.obj K) :=
      Triangle.isoMk _ _ (Iso.refl _)
        (asIso ((productComparison B).app K)) (asIso ((relationsComparison B).app K))
        (by
          change DerivedCategory.Q.map ((complexAugmentationNat B).app K) ≫
            (productComparison B).app K = 𝟙 _ ≫ augmentation B (DerivedCategory.Q.obj K)
          simpa only [Category.id_comp] using augmentation_comparison B K)
        (difference_comparison B K)
        (by
          change DerivedCategory.triangleOfSESδ (complexSequence_shortExact B K) ≫
            (shiftFunctor (DerivedCategory (StrictRingSystem B)) (1 : ℤ)).map (𝟙 _) =
              (relationsComparison B).app K ≫ (boundary B).app (DerivedCategory.Q.obj K)
          erw [CategoryTheory.Functor.map_id, Category.comp_id, boundary_rep]
          simp only [IsIso.hom_inv_id_assoc])
    exact isomorphic_distinguished _
      (DerivedCategory.triangleOfSES_distinguished (complexSequence_shortExact B K)) _ e.symm
  let e := DerivedCategory.Q.objObjPreimageIso N
  let t : coinducedTriangle B (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage N)) ≅
      coinducedTriangle B N :=
    Triangle.isoMk _ _ e ((productFunctor B).mapIso e) ((relationsFunctor B).mapIso e)
      ((augmentationNat B).naturality e.hom).symm
      ((differenceNat B).naturality e.hom).symm
      ((boundary B).naturality e.hom).symm
  exact isomorphic_distinguished _ (hQ _) _ t.symm

end SheafOfModules.SequentialDerived.Coinduced
