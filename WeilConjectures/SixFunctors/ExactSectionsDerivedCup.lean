/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.ModulePullbackTensorIso

/-! # Derived cup for exact sections

Source: Stacks Project, Tags 0FPJ (section-cup-product), 0B6C (remark-cup-product),
and 0FPK (lemma-cup-compatible-with-naive).
(blueprint: lem-sf-exact-sections-derived-cup-map).

The normalization includes every total-tensor summand and the native localization
square. Thus the cup is specified on K-flat representatives, rather than being an
unconstrained morphism between the indicated objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a b r w z c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace CategoryTheory

section CupData
variable {B : Type a} [Category.{b} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B]
  [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
  [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  {S : Type r} [CommRing S]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{z} (ModuleCat.{r} S)]
  [MonoidalCategory (DerivedCategory B)]
  [(DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B).LaxMonoidal]
  (G : B ⥤ ModuleCat.{r} S) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The cup, together with its ordinary and total-complex normalizations.
Source: Stacks 0FPJ, 0B6C and 0FPK
(blueprint: lem-sf-exact-sections-derived-cup-map).
The two lax structures record naturality and both unit laws. The localization
square determines the derived tensorator on K-flat representatives. -/
structure ExactSectionsDerivedCup where
  ordinary : G.LaxMonoidal
  derived : G.mapDerivedCategory.LaxMonoidal
  chain : ∀ K L : CochainComplex B ℤ,
    (G.mapHomologicalComplex (.up ℤ)).obj K ⊗
      (G.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L)
  chain_summand : ∀ (K L : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫ (chain K L).f n =
      ordinary.μ (K.X p) (L.X q) ≫ G.map (HomologicalComplex.ιTensorObj K L p q n h)
  chainUnit : 𝟙_ (CochainComplex (ModuleCat.{r} S) ℤ) ⟶
    (G.mapHomologicalComplex (.up ℤ)).obj (𝟙_ (CochainComplex B ℤ))
  chainUnit_zero : chainUnit.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{r} S))).hom ≫
      ordinary.ε ≫ G.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B)).inv
  tensor_normalization : ∀ K L : CochainComplex B ℤ,
    derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
        G.mapDerivedCategoryFactors.hom.app (K ⊗ L) =
      (G.mapDerivedCategoryFactors.hom.app K ⊗ₘ G.mapDerivedCategoryFactors.hom.app L) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map (chain K L)
  unit_normalization :
    derived.ε ≫ G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
        G.mapDerivedCategoryFactors.hom.app (𝟙_ (CochainComplex B ℤ)) =
      Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map chainUnit

end CupData

namespace ExactSectionsDerivedCup

attribute [instance] RingedDerivedNative.monoidal RingedDerivedNative.lax

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

/-- Evaluation with its existing section-ring action, using Mathlib's evaluation functor.
Source: Stacks 0FPJ (blueprint: lem-sf-exact-sections-derived-cup-map). -/
abbrev sectionsAt (e : C) : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R) ⥤
    ModuleCat.{max c v u} (R.obj.obj (op e)) :=
  SheafOfModules.evaluation.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R) (op e)

/-- Additivity is inherited from the existing forgetful and evaluation functors.
Source: Stacks 0FPJ (blueprint: lem-sf-exact-sections-derived-cup-map). -/
instance sectionsAt_additive (e : C) : (sectionsAt.{c, v, u} J R e).Additive :=
  inferInstanceAs ((SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op e)).Additive)

/-- Derived global sections has the canonical natural, unital cup comparison, normalized
by the ordinary section pairing and by the total-complex comparison of Stacks 0FPK.
Source: Stacks 0FPJ and 0B6C (blueprint: lem-sf-exact-sections-derived-cup-map).

Proof plan:
1. The constant-sheaf/evaluation adjunction at the final object, with the restriction
   map from the constant ring R(e), gives the global ringed-topos morphism.
2. Apply lem-weil-pbc-ringed-projection-mate-exact to obtain derived pullback,
   its tensor comparison and its adjunction with derived sections. Exactness
   identifies derived sections with mapDerivedCategory, using the comparison
   of def-sfb-right-derived-exact and the exact-functor localization factors.
3. Transpose the pullback tensor comparison followed by the tensor of counits.
   Counit naturality makes this map natural in both arguments.
4. Stacks 0FPK, lem-sf-ringed-cup-naive-compatibility, identifies this transpose
   with the naive chain pairing. On each summand it is the sheafification unit
   applied to x tensor y, including the signed total differential.
5. The adjunction mate of the pullback unit is identity on R(e). Apply
   lem-sfb-monoidal-adjunction-mates and lem-sfb-ringed-derived-monoidal-comparisons
   for its lax unit laws. The tensorator need not be invertible. -/
theorem exists_sectionwise (e : C) (_he : IsTerminal e)
    [HasDerivedCategory.{w} (RingedDerivedNative.Modules.{c, v, u} J R)]
    [HasDerivedCategory.{z} (ModuleCat.{max c v u} (R.obj.obj (op e)))]
    [PreservesFiniteLimits (sectionsAt.{c, v, u} J R e)]
    [PreservesFiniteColimits (sectionsAt.{c, v, u} J R e)] :
    ∃ d : ExactSectionsDerivedCup (sectionsAt.{c, v, u} J R e),
      (∀ (M N : RingedDerivedNative.Modules.{c, v, u} J R)
          (x : M.val.obj (op e)) (y : N.val.obj (op e)),
        (d.ordinary.μ M N).hom (x ⊗ₜ[R.obj.obj (op e)] y) =
          ((SheafOfModules.tensorObjIsoSheafification M N).inv.val.app (op e))
            ((((PresheafOfModules.sheafificationAdjunction (𝟙
              ((sheafCompose J (forget₂ CommRingCat.{max c v u}
                RingCat.{max c v u})).obj R).obj)).unit.app
                (M.val ⊗ N.val)).app (op e)) (x ⊗ₜ[R.obj.obj (op e)] y))) ∧
      ∀ a : R.obj.obj (op e), d.ordinary.ε.hom a = a := by
  sorry

section Internal

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable [(J.W (A := AddCommGrpCat.{max c v u})).IsMonoidal]

open InternalAbelianSheafModule

/-- The tensor coproducts use the already published coproducts of internal modules.
Source: Stacks 012Z, via lem-pe-internal-section-tensor-comparison
(blueprint: lem-sf-exact-sections-derived-cup-map). -/
instance internalGradedTensor {D : Type c} [Category.{v} D]
    (K : GrothendieckTopology D) [UnivLE.{max c v, r}]
    [HasSheafify K AddCommGrpCat.{r}] [(K.W (A := AddCommGrpCat.{r})).IsMonoidal]
    (A : Sheaf K AddCommGrpCat.{r}) [MonObj A] [IsCommMonObj A]
    (X Y : GradedObject ℤ (Mod (Sheaf K AddCommGrpCat.{r}) A)) :
    X.HasTensor Y :=
  fun _ ↦ (comparison_internalColimits.{r, c, v} K A).has_colimits_of_shape _
    |>.has_colimit _

/-- The section-preserving equivalence followed by ordinary module evaluation.
Source: Stacks 0FPJ and the internal/section module equivalence
(blueprint: lem-sf-exact-sections-derived-cup-map). -/
abbrev internalSectionsAt (A : Sheaf J AddCommGrpCat.{max c v u})
    [MonObj A] [IsCommMonObj A] (e : C) :
    Mod (Sheaf J AddCommGrpCat.{max c v u}) A ⥤
      ModuleCat.{max c v u} ((sectionRingSheaf.{max c v u, c, v} J A).obj.obj (op e)) :=
  (sectionModuleEquivalence.{max c v u, c, v} J A).functor ⋙
    sectionsAt.{c, v, u} J (sectionRingSheaf.{max c v u, c, v} J A) e

/-- The section-preserving equivalence and evaluation are additive.
Source: Stacks 0FPJ (blueprint: lem-sf-exact-sections-derived-cup-map). -/
instance internalSectionsAt_additive (A : Sheaf J AddCommGrpCat.{max c v u})
    [MonObj A] [IsCommMonObj A] (e : C) :
    (internalSectionsAt.{c, v, u} J A e).Additive :=
  inferInstanceAs (((sectionModuleEquivalence.{max c v u, c, v} J A).functor ⋙
    sectionsAt.{c, v, u} J (sectionRingSheaf.{max c v u, c, v} J A) e).Additive)

/-- The same normalized cup data for the native internal relative derived tensor.
The closed structure is supplied by its existing tensor-Hom universal property;
the Grothendieck structure is the existing essentially-small-site theorem.
The resolution functor ρ and quasi-isomorphism π are the assumed functorial K-flat
resolutions. Their derivability structure supplies the native derived tensor.
Source: Stacks 0FPJ and def-sfb-derived-tensor-modules
(blueprint: lem-sf-exact-sections-derived-cup-map). -/
abbrev InternalCupStatement (A : Sheaf J AddCommGrpCat.{max c v u})
    [MonObj A] [IsCommMonObj A] (e : C)
    [HasDerivedCategory.{w} (Mod (Sheaf J AddCommGrpCat.{max c v u}) A)]
    [HasDerivedCategory.{z}
      (ModuleCat.{max c v u} ((sectionRingSheaf.{max c v u, c, v} J A).obj.obj (op e)))]
    [PreservesFiniteLimits (internalSectionsAt.{c, v, u} J A e)]
    [PreservesFiniteColimits (internalSectionsAt.{c, v, u} J A e)] : Prop :=
  letI : HasSheafify ((equivSmallModel.{max c v u} C).inverse.inducedTopology J)
      AddCommGrpCat.{max c v u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  letI : IsGrothendieckAbelian.{max c v u} (Sheaf J AddCommGrpCat.{max c v u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall J AddCommGrpCat.{max c v u}
  letI : MonoidalClosed (Sheaf J AddCommGrpCat.{max c v u}) :=
    (sfbSheafTensor_properties.{c, v, (max c v u) + 1, max c v u, 0, 0}
      (A := AddCommGrpCat.{max c v u}) J).2.1.some
  ∀ (ρ : CochainComplex (Mod (Sheaf J AddCommGrpCat.{max c v u}) A) ℤ ⥤
        CochainComplex (Mod (Sheaf J AddCommGrpCat.{max c v u}) A) ℤ)
      (π : ρ ⟶ 𝟭 _) (hπ : ∀ K, QuasiIso (π.app K))
      (hρ : ∀ K, (HomotopyCategory.quasiIso
        (Mod (Sheaf J AddCommGrpCat.{max c v u}) A) (.up ℤ)).kFlat
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (ρ.obj K))),
  letI : ((HomotopyCategory.quasiIso
      (Mod (Sheaf J AddCommGrpCat.{max c v u}) A) (.up ℤ)
    ).localizerMorphismKFlat).IsLeftDerivabilityStructure :=
    HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _ π hπ hρ
  ∃ d : ExactSectionsDerivedCup (internalSectionsAt.{c, v, u} J A e),
    (∀ (M N : Mod (Sheaf J AddCommGrpCat.{max c v u}) A)
        (x : M.X.obj.obj (op e)) (y : N.X.obj.obj (op e)),
      (d.ordinary.μ M N).hom
          (x ⊗ₜ[(sectionRingSheaf.{max c v u, c, v} J A).obj.obj (op e)] y) =
        comparison_internalTmul.{max c v u, c, v} J A M N (op e) x y) ∧
    ∀ a : (sectionRingSheaf.{max c v u, c, v} J A).obj.obj (op e), d.ordinary.ε.hom a = a

/-- The exact-sections cup for native internal module objects, with the same section
pairing and the native relative derived tensor rather than a transported tensor.
Source: Stacks 0FPJ, 0B6C and 0FPK
(blueprint: lem-sf-exact-sections-derived-cup-map).

Proof plan: use the six steps of exists_sectionwise. For the last internal-module
step, lem-pe-internal-section-tensor-comparison says the recorded equivalence
is exact, preserves the section groups identically, identifies the pure tensors
and the signed total tensors, and preserves and reflects K-flat complexes.
Its localization therefore identifies the native relative derived tensors and
units with the sectionwise ones. Conjugate the sectionwise cup by those
comparisons. The summand and unit normalizations remain unchanged, so the
localization square gives the native internal cup. -/
theorem exists_internal (A : Sheaf J AddCommGrpCat.{max c v u})
    [MonObj A] [IsCommMonObj A] (e : C) (_he : IsTerminal e)
    [HasDerivedCategory.{w} (Mod (Sheaf J AddCommGrpCat.{max c v u}) A)]
    [HasDerivedCategory.{z}
      (ModuleCat.{max c v u} ((sectionRingSheaf.{max c v u, c, v} J A).obj.obj (op e)))]
    [PreservesFiniteLimits (internalSectionsAt.{c, v, u} J A e)]
    [PreservesFiniteColimits (internalSectionsAt.{c, v, u} J A e)] :
    InternalCupStatement.{w, z, c, v, u} J A e := by
  sorry

end Internal
end ExactSectionsDerivedCup
end CategoryTheory
