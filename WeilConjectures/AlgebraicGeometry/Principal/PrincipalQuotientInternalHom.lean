/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
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
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
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
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses

/-! # Canonical internal Hom comparison for a regular principal quotient

Source: Stacks Project, Tags 08JF and 0BYU; current blueprint,
sec-smooth-purity/sk-lem-sp-tower/lem-coef-integral-hom-reduction.proof.md
(blueprint: lem-sf-principal-quotient-internal-hom).

The extension, internal Hom and bidual map below are the existing ordinary unbounded
small-etale constructions. The tensor comparison of the extension is the canonical one,
`Functor.leftDerivedTensorIsoOfIsLeftDerivedFunctor` of the strong monoidal sheaf extension
of scalars (not the choice-based `derivedExtendScalarsTensorIso`). In particular the comparison
is a real transpose of evaluation, rather than a choice of an unspecified isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

-- As in `WeilConjectures.SixFunctors.Etale.Derived.ReductionHom`: instance search must produce
-- the braidings underlying `AlgebraicGeometry.Etale.derivedTensor`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

/-- The small etale site is essentially small (a local copy of the local instance of
`WeilConjectures.SixFunctors.Etale.Derived.ReductionHom`, which instance search does not find).
Source: Stacks 03NU (blueprint: lem-sf-principal-quotient-internal-hom). -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Sheaves of modules on the small etale site have countable coproducts (local copy of the
local instance of `WeilConjectures.SixFunctors.Etale.Derived.ReductionHom`).
Source: Stacks 03CN (blueprint: lem-sf-principal-quotient-internal-hom). -/
local instance (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _⟩

variable {R : Type (u + 1)} [CommRing R] (r : R) (m : ℕ) (X : Scheme.{u})

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The existing derived coefficient extension along R → R/(r^m).
Source: Stacks 06YY, 08JF
(blueprint: lem-sf-principal-quotient-internal-hom). -/
abbrev principalExtension :
    DerivedCategoryModule R X ⥤ DerivedCategoryModule (R ⧸ Ideal.span {r ^ m}) X :=
  derivedExtendScalars (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m}))
    Ideal.mk_ker X

/-- Exact termwise restriction along the same quotient map.
Source: Stacks 07A6 (blueprint: lem-sf-principal-quotient-internal-hom). -/
abbrev principalRestriction :
    DerivedCategoryModule (R ⧸ Ideal.span {r ^ m}) X ⥤ DerivedCategoryModule R X :=
  Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk _)

/-- The canonical strong tensor comparison `E(K ⊗ M) ≅ E K ⊗ E M` of the derived extension,
natural in `M`: the component at `K` of the derived tensor comparison of the strong monoidal
sheaf extension of scalars, transported to `principalExtension` by uniqueness of left derived
functors (`Functor.leftDerivedTensorIsoOfIsLeftDerivedFunctor`). This is the canonical
comparison, not the `Nonempty.some` of `derivedExtendScalarsTensorIso`.
Source: Stacks 06YY, 08JF (blueprint: lem-sf-principal-quotient-internal-hom). -/
def principalTensorIso (K : DerivedCategoryModule R X) :
    (derivedTensor (ModuleCat.{u + 1} R) X).obj K ⋙ principalExtension r m X ≅
      principalExtension r m X ⋙
        (derivedTensor (ModuleCat.{u + 1} (R ⧸ Ideal.span {r ^ m})) X).obj
          ((principalExtension r m X).obj K) :=
  have := preservesKFlatQuasiIso_extendScalars
    (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m})) Ideal.mk_ker X
  Functor.leftDerivedTensorIsoOfIsLeftDerivedFunctor
    (Sheaf.extendScalars X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {r ^ m})))
    (principalExtension r m X)
    (derivedExtendScalarsCounit (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m}))
      Ideal.mk_ker X) K

/-- The actual tensor-Hom transpose of extended evaluation. Mathlib curries
K tensor H(K,L) → L; symmetry identifies this with the right-evaluation convention.
Source: Stacks 08JF (blueprint: lem-sf-principal-quotient-internal-hom). -/
def principalHomComparison (K L : DerivedCategoryModule R X) :
    (principalExtension r m X).obj ((ihom K).obj L) ⟶
      (ihom ((principalExtension r m X).obj K)).obj ((principalExtension r m X).obj L) :=
  MonoidalClosed.curry
    ((principalTensorIso r m X K).inv.app ((ihom K).obj L) ≫
      (principalExtension r m X).map ((ihom.ev K).app L))

/-- Right evaluation, obtained from the existing evaluation counit by the canonical
Koszul braiding of the derived tensor.
Source: Stacks 08JF (blueprint: lem-sf-principal-quotient-internal-hom). -/
def principalRightEvaluation {A : Type (u + 1)} [CommRing A]
    (K L : DerivedCategoryModule A X) : (ihom K).obj L ⊗ K ⟶ L :=
  ((derivedBraidedCategory A X).braiding _ _).hom ≫ (ihom.ev K).app L

/-- The specified dual comparison, assembled from beta and the chosen dualizing isomorphism.
Source: Stacks 08JF and the blueprint's double-transpose argument
(blueprint: lem-sf-principal-quotient-internal-hom). -/
def principalDualIso
    (b : ∀ K L : DerivedCategoryModule R X,
      (principalExtension r m X).obj ((ihom K).obj L) ≅
        (ihom ((principalExtension r m X).obj K)).obj ((principalExtension r m X).obj L))
    {W : DerivedCategoryModule R X}
    {WB : DerivedCategoryModule (R ⧸ Ideal.span {r ^ m}) X}
    (w : (principalExtension r m X).obj W ≅ WB) (K : DerivedCategoryModule R X) :
    (principalExtension r m X).obj ((ihom K).obj W) ≅
      (ihom ((principalExtension r m X).obj K)).obj WB :=
  b K W ≪≫ (ihom ((principalExtension r m X).obj K)).mapIso w

/-- Canonical Hom reduction, its evaluation normalization, naturality, and the actual
biduality identity for every unbounded input and every choice of W, WB and w.
Source: Stacks 08JF, 0BYU; current blueprint lem-coef-integral-hom-reduction proof
(blueprint: lem-sf-principal-quotient-internal-hom).

Proof:
1. Injectivity of r gives the free two-term resolution [R --r^m--> R] of B.
   Termwise constant realization preserves its quasi-isomorphism to B; bounded-flat
   K-flatness and the tensor/cone comparison give the coefficient triangle for every M.
2. The canonical tensor-Hom action is exact, including the connecting square, and is
   the identity at the tensor unit. Two-out-of-three in the coefficient triangles makes
   H(K,L) tensor B → H(K,L tensor B) an isomorphism, naturally in K and L.
3. Scalar internal-Hom adjunction identifies the restriction of beta with that action:
   both transposes evaluate H(K,L) against K and multiply the B coefficient. Restriction
   is conservative, so beta is invertible. The representing adjunctions give naturality.
4. The transpose definition gives the displayed right-evaluation equation after symmetry.
5. Apply map_toIhomIhom_comp_dualComparison to coefficient extension and w. Its comparison
   is alpha by evaluation normalization. Compose with precomposition by alpha inverse;
   contravariant functoriality cancels alpha and gives the displayed bidual identity.
No boundedness, Tor-amplitude, constructibility, completeness or perfectness is used. -/
theorem principalQuotient_internalHom
    (hr : Function.Injective (fun x : R ↦ r * x)) (hm : 1 ≤ m) :
    ∃ b : ∀ K L : DerivedCategoryModule R X,
      (principalExtension r m X).obj ((ihom K).obj L) ≅
        (ihom ((principalExtension r m X).obj K)).obj ((principalExtension r m X).obj L),
      (∀ K L, (b K L).hom = principalHomComparison r m X K L) ∧
      (∀ K L,
        ((b K L).hom ▷ (principalExtension r m X).obj K) ≫
            principalRightEvaluation X ((principalExtension r m X).obj K)
              ((principalExtension r m X).obj L) =
          (principalTensorIso r m X ((ihom K).obj L)).inv.app K ≫
            (principalExtension r m X).map (principalRightEvaluation X K L)) ∧
      (∀ (K K' L L' : DerivedCategoryModule R X) (f : K' ⟶ K) (g : L ⟶ L'),
        (principalExtension r m X).map
            ((MonoidalClosed.pre f).app L ≫ (ihom K').map g) ≫ (b K' L').hom =
          (b K L).hom ≫
            (MonoidalClosed.pre ((principalExtension r m X).map f)).app
              ((principalExtension r m X).obj L) ≫
            (ihom ((principalExtension r m X).obj K')).map
              ((principalExtension r m X).map g)) ∧
      (∃ a : ∀ K : DerivedCategoryModule R X,
        ihom K ⋙ principalExtension r m X ⋙ principalRestriction r m X ≅
          principalExtension r m X ⋙ principalRestriction r m X ⋙ ihom K,
        ∀ (K K' L : DerivedCategoryModule R X) (f : K' ⟶ K),
          (principalRestriction r m X).map
              ((principalExtension r m X).map ((MonoidalClosed.pre f).app L)) ≫
              (a K').hom.app L =
            (a K).hom.app L ≫ (MonoidalClosed.pre f).app
              ((principalRestriction r m X).obj ((principalExtension r m X).obj L))) ∧
      ∀ (W : DerivedCategoryModule R X)
        (WB : DerivedCategoryModule (R ⧸ Ideal.span {r ^ m}) X)
        (w : (principalExtension r m X).obj W ≅ WB) (K : DerivedCategoryModule R X),
        (derivedHomToIhomIhomNatTrans (ModuleCat.{u + 1} (R ⧸ Ideal.span {r ^ m})) X WB).app
            ((principalExtension r m X).obj K) =
          (principalExtension r m X).map
              ((derivedHomToIhomIhomNatTrans (ModuleCat.{u + 1} R) X W).app K) ≫
            (principalDualIso r m X b w ((ihom K).obj W)).hom ≫
            (MonoidalClosed.pre (principalDualIso r m X b w K).inv).app WB := by
  sorry

end AlgebraicGeometry.Etale
