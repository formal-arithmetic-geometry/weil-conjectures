/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
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
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Derived sections over a w-contractible affine pro-etale object

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-wc-sections/det-pe-wc-sections-derived.md;
Stacks Project, Tags 079P, 070K and 070Y (blueprint: det-pe-wc-sections-derived).
-/

@[expose] public section

set_option autoImplicit false

universe t u v wA wB

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

namespace AlgebraicGeometry.Scheme.ProEt

/-- Evaluation is the composite of the existing additive forgetful and presheaf
evaluation functors. Source: the blueprint's sectionwise module category,
Stacks Project, Modules on Sites (blueprint: det-pe-wc-sections-derived). -/
instance moduleEvaluation_additive (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt) :
    (SheafOfModules.evaluation.{max u v (t + 1)} R (op U)).Additive :=
  inferInstanceAs ((SheafOfModules.forget.{max u v (t + 1)} R ⋙
    PresheafOfModules.evaluation R.obj (op U)).Additive)

/-- The K-injective resolution hypothesis for the recorded unbounded right derived
functor, on the original pro-etale module category. This only forgets the additional
monomorphism property of the existing K-injective resolution theorem.
Source: Stacks Project, Tag 079P (blueprint: det-pe-wc-sections-derived). -/
abbrev moduleQuasiIsoKInjectiveResolutions (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) :
    ∀ K : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ,
      ∃ (I : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s :=
  letI := SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, u, v} (topology X) R
  fun K ↦ (Abelian.HasKInjectiveResolutions.exists_isKInjective K).elim
    (fun I hI ↦ hI.elim (fun hKI hs ↦ hs.elim (fun s hs ↦ ⟨I, s, hKI, hs.2⟩)))

end AlgebraicGeometry.Scheme.ProEt
