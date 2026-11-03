/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import Mathlib.Algebra.Polynomial.Laurent
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Canonical abelian evaluation for Kummer-site cohomology

The abelian helper is evaluation at one on Hom(ℤ[0], K). It is independent of the
site, sheaf, derived adjunction, and cohomological degree used in the item.
(blueprint: prop-pur-gm-relative-kummer)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Site

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}

variable {A : Type (u + 1)} [CommRing A]

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}

private theorem kummer_uliftZMultiples_eval (G : AddCommGrpCat.{u + 1})
    (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ G) :
    G.uliftZMultiplesAddEquiv f = f.hom (ULift.up 1) := by
  have h := (AddEquiv.mk' (uliftZMultiplesHom G) (uliftZMultiplesHom_apply_add G)).apply_symm_apply
    (AddCommGrpCat.homAddEquiv f)
  have h₂ := congrArg (fun φ : ULift.{u + 1} ℤ →+ G ↦ φ (ULift.up 1)) h
  change uliftZMultiplesHom G (G.uliftZMultiplesAddEquiv f) (ULift.up 1) =
    f.hom (ULift.up 1) at h₂
  rw [← h₂]
  simp only [uliftZMultiplesHom]
  exact (one_smul ℤ _).symm

/-- Taking degree-zero homology and evaluating at one identifies morphisms from ℤ[0]
with degree-zero homology for every bounded-below derived abelian group.

Proof: represent K by a bounded-below complex. The single complex ℤ[0] is K-projective,
since the lifted integer group is projective. Morphisms in the derived category are thus
homotopy classes of chain maps from ℤ[0]. A chain map is determined by the image of one,
which is a degree-zero cycle. Two maps are homotopic exactly when these cycles differ by
a boundary. The displayed homology map sends precisely this class to its cycle class.
This proves injectivity and surjectivity, including when K has nonzero negative degrees.
Source: Stacks, 01FT (blueprint: new-pur-kummer-site-abelian-evaluation-formula). -/
theorem kummerDerivedEvaluationAtOne_bijective
    (K : DerivedCategory.Plus AddCommGrpCat.{u + 1}) :
    Function.Bijective
      (fun φ : (DerivedCategory.Plus.singleFunctor AddCommGrpCat.{u + 1} 0).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ K ↦
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} 0).map φ)
          (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
            (C := AddCommGrpCat.{u + 1}) 0).inv.app
              (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (ULift.up 1))) := by
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let : Projective Z := {
    factors := by
      intro E X f e he
      obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective e).mp he (f (ULift.up 1))
      refine ⟨(AddCommGrpCat.uliftZMultiplesAddEquiv E).symm y, ?_⟩
      apply (AddCommGrpCat.uliftZMultiplesAddEquiv X).injective
      have hnat (g : Z ⟶ E) :
          X.uliftZMultiplesAddEquiv (g ≫ e) = e (E.uliftZMultiplesAddEquiv g) := by
        rw [kummer_uliftZMultiples_eval, kummer_uliftZMultiples_eval]
        rfl
      rw [hnat, AddEquiv.apply_symm_apply, kummer_uliftZMultiples_eval]
      exact hy }
  let e₁ := (ObjectProperty.fullyFaithfulι DerivedCategory.TStructure.t.plus).homEquiv
    (X := (DerivedCategory.Plus.singleFunctor _ 0).obj Z) (Y := K)
  let e₂ := DerivedCategory.homSingleEquivOfProjective Z 0 K.obj
  let e₃ := (AddCommGrpCat.uliftZMultiplesAddEquiv
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} 0).obj K)).toEquiv
  have h := e₃.bijective.comp (e₂.bijective.comp e₁.bijective)
  change Function.Bijective
    (fun φ : (DerivedCategory.Plus.singleFunctor _ 0).obj Z ⟶ K ↦
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
        (DerivedCategory.homSingleToHomology Z 0 K.obj (DerivedCategory.Plus.ι.map φ))) at h
  simp only [DerivedCategory.homSingleToHomology, kummer_uliftZMultiples_eval,
    ConcreteCategory.comp_apply, DerivedCategory.Plus.homologyFunctor,
    DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso, Functor.comp_map,
    Iso.app_inv, Z, Functor.comp_obj, DerivedCategory.Plus.ι,
    ObjectProperty.ι_obj, ObjectProperty.ι_map] at h ⊢
  convert h using 1
  rfl

end Site

end AlgebraicGeometry.ProEtale
