/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
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
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Assembly of compatible coefficient-level isomorphisms

Source: Zheng Construction 4.1, module sheaves on the ringed sequence site.
(blueprint: lem-coef-system-iso-assembly)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

section Assembly
variable {M N : Systems.{c, v, max c v r} J B τ}
  (d : ∀ n : ℕ, (evaluation.{c, v, max c v r} J B τ n).obj M ⟶
    (evaluation.{c, v, max c v r} J B τ n).obj N)
  (ht : ∀ {m n : ℕ} (h : n ≤ m),
    (transition.{c, v, max c v r} J B τ h).app M ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (d n) =
      d m ≫ (transition.{c, v, max c v r} J B τ h).app N)

@[irreducible] private def assemble_app (X : (ℕ × C)ᵒᵖ) : M.val.obj X ⟶ N.val.obj X :=
  undoRestriction.{max c v r}
    ((CategoryTheory.evaluation Cᵒᵖ RingCat).obj (op X.unop.2) |>.mapIso
      ((sheafToPresheaf J RingCat).mapIso
        (eqToIso (evaluation_ring.{c, v, max c v r} J B τ X.unop.1).symm)))
    ((d X.unop.1).val.app (op X.unop.2))

include ht in
@[irreducible] private def assemble : M ⟶ N where
  val :=
    { app := assemble_app.{c, v, r} J B τ d
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change assemble_app.{c, v, r} J B τ d Y (M.val.map f x) =
          N.val.map f (assemble_app.{c, v, r} J B τ d X x)
        symm
        let a : X ⟶ op (X.unop.1, Y.unop.2) :=
          (Prod.mkHom (𝟙 X.unop.1) f.unop.2).op
        let b : op (X.unop.1, Y.unop.2) ⟶ Y :=
          (Prod.mkHom f.unop.1 (𝟙 Y.unop.2)).op
        have hab : f = a ≫ b := by
          apply Quiver.Hom.unop_inj
          apply Prod.hom_ext <;> simp [a, b]
        have hM : M.val.map f x = M.val.map b (M.val.map a x) :=
          (M.val.congr_map_apply hab x).trans (M.val.map_comp_apply a b x)
        have hN : N.val.map f (assemble_app.{c, v, r} J B τ d X x) =
            N.val.map b (N.val.map a (assemble_app.{c, v, r} J B τ d X x)) :=
          (N.val.congr_map_apply hab _).trans (N.val.map_comp_apply a b _)
        erw [hM, hN, vertical_natural.{c, v, r} J B τ d X.unop.1 f.unop.2.op x]
        exact horizontal_natural.{c, v, r} J B τ d ht
          (leOfHom f.unop.1) (op Y.unop.2) (M.val.map a x) }

@[irreducible] private def assemble_iso
    (δ : ∀ n : ℕ, (evaluation.{c, v, max c v r} J B τ n).obj M ≅
      (evaluation.{c, v, max c v r} J B τ n).obj N)
    (ht : ∀ {m n : ℕ} (h : n ≤ m),
      (transition.{c, v, max c v r} J B τ h).app M ≫
          (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)).map (δ n).hom =
        (δ m).hom ≫ (transition.{c, v, max c v r} J B τ h).app N) : M ≅ N := by
  let q := assemble.{c, v, r} J B τ (fun n ↦ (δ n).hom) ht
  have hj : JointlyFaithful (evaluation.{c, v, max c v r} J B τ) := by
    constructor
    intro M N f g h
    ext X x
    exact congrArg (fun k ↦ k.val.app (op X.unop.2) x) (h X.unop.1)
  have (n : ℕ) : IsIso ((evaluation.{c, v, max c v r} J B τ n).map q) := by
    have he := assemble_evaluation.{c, v, r} J B τ (fun k ↦ (δ k).hom) ht n
    exact he.symm ▸ (inferInstance : IsIso (δ n).hom)
  have : IsIso q := hj.jointlyReflectsIsomorphisms.isIso q
  exact asIso q

end Assembly

end WeilConjectures.SemilinearSections
