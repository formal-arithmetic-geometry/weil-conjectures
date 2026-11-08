/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Ordinary direct image with the continuous-function finite coefficient sheaf

Source: blueprint def-weil-pbc-proetale-operations, ordinary K-injective direct image;
Stacks Project, Sections 07A5 and 0735 (blueprint: def-weil-pbc-proetale-operations).

This interface retains the actual finite coefficient ring sheaf. The coefficient map
is induced by precomposition with the first projection of the scheme fibre product,
then by the universal property of ring sheafification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- The coefficient map on an object, by precomposition on connected components with
`U ×[T] S → U`. Source: blueprint ordinary operations; Stacks Section 0735
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def finiteCoefficientPullbackSections (U : T.ProEtᵒᵖ) :
    (finiteCoefficientPresheaf T Λ).obj U ⟶
      (finiteCoefficientPresheaf S Λ).obj ((Scheme.proEtaleBaseChange f).op.obj U) :=
  RingCat.ofHom
    { toFun := fun s ↦ s.comp
        ⟨(pullback.fst U.unop.hom f).continuous.connectedComponentsMap,
          (pullback.fst U.unop.hom f).continuous.connectedComponentsMap_continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The section maps commute with restriction. Source: blueprint ordinary operations;
Stacks Section 0735 (blueprint: def-weil-pbc-proetale-operations).

Proof: the base-change map of a morphism of objects commutes with the first projections
by the universal property of the fibre product. Passing to connected components
preserves composition. Precomposition of continuous functions therefore gives the same
function along both composites, and the pointwise ring operations do not alter it. -/
theorem finiteCoefficientPullbackSections_naturality
    (U V : T.ProEtᵒᵖ) (a : U ⟶ V) :
    (finiteCoefficientPresheaf T Λ).map a ≫ finiteCoefficientPullbackSections f Λ V =
      finiteCoefficientPullbackSections f Λ U ≫
        (finiteCoefficientPresheaf S Λ).map ((Scheme.proEtaleBaseChange f).op.map a) := by
  ext s
  change C(ConnectedComponents U.unop.left, Λ) at s
  apply ContinuousMap.ext
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  change s (ConnectedComponents.mk ((pullback.fst V.unop.hom f ≫ a.unop.left) x)) =
    s (ConnectedComponents.mk
      ((((Scheme.proEtaleBaseChange f).map a.unop).left ≫
        pullback.fst U.unop.hom f) x))
  simp only [Scheme.proEtaleBaseChange, MorphismProperty.Over.pullback_map_left,
    pullback.lift_fst]
  rfl

/-- The actual presheaf coefficient map. Source: blueprint ordinary operations;
Stacks Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def finiteCoefficientPullbackPresheafMap :
    finiteCoefficientPresheaf T Λ ⟶
      (Scheme.proEtaleBaseChange f).op ⋙ finiteCoefficientPresheaf S Λ where
  app := finiteCoefficientPullbackSections f Λ
  naturality := finiteCoefficientPullbackSections_naturality f Λ

/-- Extend the canonical section maps by ring sheafification, with no chosen
coefficient identification. Source: blueprint ordinary operations; Stacks Section 0735
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def finiteCoefficientDirectImageRingMap :
    finiteCoefficientRingSheaf T Λ ⟶
      (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf S Λ) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv _ _).symm
    (finiteCoefficientPullbackPresheafMap f Λ ≫
      Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology S) (finiteCoefficientPresheaf S Λ)))

/-- Ordinary module direct image, with its scalar action through the specified
continuous-function coefficient map. Source: blueprint ordinary operations;
Stacks Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def finiteCoefficientModuleDirectImage :
    FiniteCoefficientModules S Λ ⥤ FiniteCoefficientModules T Λ :=
  SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology T) (K := Scheme.ProEt.topology S)
    (finiteCoefficientDirectImageRingMap f Λ)

/-- Ordinary direct image is additive. Source: Stacks Section 0735
(blueprint: def-weil-pbc-proetale-operations).

Proof: its maps are the original sectionwise linear maps after precomposition with
base change. Addition of module-sheaf morphisms is sectionwise, so precomposition
preserves addition and zero; restriction of scalars does not change these maps. -/
theorem finiteCoefficientModuleDirectImage_additive :
    (finiteCoefficientModuleDirectImage f Λ).Additive := by
  constructor
  intro X Y g h
  rfl

attribute [instance] finiteCoefficientModuleDirectImage_additive

/-- K-injective resolutions are taken in all finite-coefficient module sheaves,
without any boundedness or constructibility restriction. Source: Stacks Section 07A5
(blueprint: def-weil-pbc-proetale-operations).

Proof: transport the site to Scheme.proEtaleSiteModel, which raises only the Hom
universe. Modules over a ring sheaf on this small site form a Grothendieck abelian
category, hence admit functorial K-injective resolutions. Transporting the resolutions
back preserves homotopies and quasi-isomorphisms, since the site equivalence preserves
kernels and cokernels sectionwise. This is the same small-site argument as the recorded
arbitrary-ring-sheaf operations, now keeping the finite coefficient RingCat sheaf. -/
theorem finiteCoefficientModules_hasKInjectiveResolutions (V : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (FiniteCoefficientModules V Λ) := by
  let : IsGrothendieckAbelian.{u + 1} (FiniteCoefficientModules V Λ) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, u + 1}
      (Scheme.ProEt.topology V) (finiteCoefficientRingSheaf V Λ)
  infer_instance

attribute [instance] finiteCoefficientModules_hasKInjectiveResolutions

/-- The ordinary uncompleted derived direct image, using K-injective resolutions in
all modules over the specified finite coefficient ring sheaf. Source: Stacks Section 07A5
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def finiteCoefficientDerivedDirectImage :
    FiniteCoefficientDerivedCategory S Λ ⥤ FiniteCoefficientDerivedCategory T Λ :=
  (finiteCoefficientModuleDirectImage f Λ).rightDerivedFunctor

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Canonical realization is an equivalence, with inverse obtained by forgetting to
fixed scalar sections. Source: Stacks, Modules on Sites, sheafification of modules
(blueprint: def-weil-pbc-proetale-operations).

Proof: the constants-to-functions scalar map is locally bijective by
`finiteCoefficientScalarMap_locallyBijective`. Restrict a module action along constant
scalar sections to obtain a fixed-ring module sheaf. Its action extends uniquely to
locally constant scalar sections, and sheaf gluing supplies the inverse action.
These constructions give the unit and counit isomorphisms of the realization
adjunction. This is exactly the equivalence used in the proof of
`finiteCoefficientRealization_exact`; it applies also to the zero ring and empty scheme. -/
theorem finiteCoefficientRealization_isEquivalence :
    (finiteCoefficientRealization T Λ).IsEquivalence :=
  finiteCoefficientRealizationIsEquivalenceRing.{u} T Λ

attribute [instance] finiteCoefficientRealization_isEquivalence

/-- The inverse of the canonical coefficient realization, rather than a new coefficient
category. Source: Stacks, Modules on Sites, sheafification of modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def finiteCoefficientUnrealization :
    FiniteCoefficientModules T Λ ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) :=
  (finiteCoefficientRealization T Λ).asEquivalence.inverse

/-- The realization inverse is additive, being an inverse equivalence of additive
categories. Source: Stacks, Modules on Sites
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance finiteCoefficientUnrealization_additive :
    (finiteCoefficientUnrealization T Λ).Additive :=
  @Equivalence.inverse_additive _ _ _ _ _ _
    (finiteCoefficientRealization T Λ).asEquivalence (finiteCoefficientRealization_additive T Λ)

/-- Its inverse preserves finite limits. Source: Stacks, Modules on Sites
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance finiteCoefficientUnrealization_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientUnrealization T Λ) :=
  inferInstanceAs (PreservesFiniteLimits (finiteCoefficientRealization T Λ).asEquivalence.inverse)

/-- Its inverse preserves finite colimits. Source: Stacks, Modules on Sites
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance finiteCoefficientUnrealization_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientUnrealization T Λ) :=
  inferInstanceAs (PreservesFiniteColimits (finiteCoefficientRealization T Λ).asEquivalence.inverse)

variable {S : Scheme.{u}} (f : S ⟶ T)

/-- Pullback in the specified coefficient-ring presentation. Its fixed-scalar version
is the module-valued Kan extension and sheafification, so the coefficient identification
is the one induced by constant scalar sections. Source: Stacks,
lemma-adjoint-push-pull-modules (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def finiteCoefficientPullback :
    FiniteCoefficientModules T Λ ⥤ FiniteCoefficientModules S Λ :=
  finiteCoefficientUnrealization T Λ ⋙ upperStar (ModuleCat.{u + 1} Λ) f ⋙
    finiteCoefficientRealization S Λ

/-- Additivity of pullback. Source: Stacks, Modules on Sites
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance finiteCoefficientPullback_additive :
    (finiteCoefficientPullback T Λ f).Additive :=
  inferInstanceAs (finiteCoefficientUnrealization T Λ ⋙
    upperStar (ModuleCat.{u + 1} Λ) f ⋙ finiteCoefficientRealization S Λ).Additive

/-- Exactness of pullback, on finite limits. Source: Stacks, Tag 04JC
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance finiteCoefficientPullback_preservesFiniteLimits :
    PreservesFiniteLimits (finiteCoefficientPullback T Λ f) :=
  inferInstanceAs (PreservesFiniteLimits (finiteCoefficientUnrealization T Λ ⋙
    upperStar (ModuleCat.{u + 1} Λ) f ⋙ finiteCoefficientRealization S Λ))

/-- Exactness of pullback, on finite colimits. Source: Stacks, Tag 04JC
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance finiteCoefficientPullback_preservesFiniteColimits :
    PreservesFiniteColimits (finiteCoefficientPullback T Λ f) :=
  inferInstanceAs (PreservesFiniteColimits (finiteCoefficientUnrealization T Λ ⋙
    upperStar (ModuleCat.{u + 1} Λ) f ⋙ finiteCoefficientRealization S Λ))

/-- Ordinary uncompleted derived pullback is exact termwise descent through localization.
Source: Stacks, Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev finiteCoefficientDerivedPullback :
    FiniteCoefficientDerivedCategory T Λ ⥤ FiniteCoefficientDerivedCategory S Λ :=
  (finiteCoefficientPullback T Λ f).mapDerivedCategory

end AlgebraicGeometry.ProEtale
