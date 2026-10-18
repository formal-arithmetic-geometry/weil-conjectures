/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.FormalClosedSupport

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.CondensedFiniteFreeTensorExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-!
# Closed support, truncation and sequential derived limits

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-lem-formal-closed-support-ii`, and Stacks Tags 09AA and 08TC
(blueprint: sk-lem-formal-closed-support-ii).

The assertion predicate records left t-exactness and the image of every Roos triangle,
using an isomorphism normalized by the product projections. It makes no choice of cones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u vA vB uA uB wA wB


open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The two conclusions of the closed-support lemma for one of its three functors.
The product isomorphism is the canonical comparison, specified by all projections;
the boundary uses its inverse and the functor's shift comparison.
Source: blueprint sk-lem-formal-closed-support-ii, final Roos-triangle convention;
Stacks Tag 08TC (blueprint: sk-lem-formal-closed-support-ii). -/
def ClosedSupportIIAssertions
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] : Prop :=
  (∀ K : DerivedCategory A, DerivedCategory.TStructure.t.ge 0 K →
    DerivedCategory.TStructure.t.ge 0 (F.obj K)) ∧
  (∀ (K : ℕ → DerivedCategory A) [HasProduct K]
      [HasProduct (fun n ↦ F.obj (K n))],
    ∃ e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n ↦ F.obj (K n)),
      (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) ∧
      ∀ (t : ∀ n : ℕ, K (n + 1) ⟶ K n)
        (H : DerivedCategory A) (p : H ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ H⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle t H p δ →
          IsDerivedLimitTriangle (fun n ↦ F.map (t n)) (F.obj H)
            (F.map p ≫ e.hom)
            (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app H))

/-- The canonical tensor shift comparison, specialized to the recorded derived-tensor wrapper.
Source: blueprint sk-lem-formal-closed-support-ii, derived tensor clause
(blueprint: sk-lem-formal-closed-support-ii). This reuses the existing comparison induced
from K-flat representatives; it does not choose a new shift structure. -/
instance formalClosedSupportIITensor_commShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u})
    (K : DerivedCategory (FormalSupportModules Λ S)) :
    ((derivedTensor Λ S).obj K).CommShift ℤ :=
  DerivedCategory.commShiftTensorLeft (FormalSupportModules Λ S) K

/-- The closed support functor, its open restriction, and finite locally free tensor
are left t-exact and take Roos triangles to Roos triangles for the image tower.
The coefficient disjunction uses finite-subextension-valued sections for Qbar.
The last comparison identifies derived tensor with ordinary termwise tensor.

Source: blueprint main-20261015, sk-lem-formal-closed-support-ii, all clauses;
Stacks Tags 09AA, 013K, 070J, 079P, 0BK6, 07KC and 08TC
(blueprint: sk-lem-formal-closed-support-ii).

Proof plan:
1. Cartesian coefficients identify module pullback with exact inverse image.
   The immersion limit-preservation theorem gives countable products for i*, j*, u*.
   The module adjunction makes j_* preserve limits. Kernels commute with products
   and finite limits, so G = i* ker(id -> j_*j*) is additive and left exact.
2. Module categories are Grothendieck abelian. Degreewise-injective K-injective
   resolutions give enough injectives. Resolve a nonnegative representative by a
   bounded-below injective complex; it is K-injective (Tags 013K and 070J).
   Applying G retains the lower bound, proving left t-exactness of RG.
3. Products of K-injectives are K-injective (Tag 0BK6). Compute RG on their product;
   the underived product comparison identifies it with the product of G(I_n).
   Derived products on the closed site are represented termwise (det-pe-products-derived).
4. Open restriction is exact and preserves products. Its termwise derived functor
   commutes with cohomology, so the same conclusions hold after u*.
5. Finite locally free tensor preserves finite limits by the condensed finite-free
   tensor theorem, and colimits by tensor-Hom adjunction. Thus it is exact and its
   termwise functor commutes with cohomology. L[0] is K-flat. The derived-tensor
   descent theorem identifies L[0] tensor^L - naturally with termwise tensor.
6. On a trivializing pro-etale cover, the tensor/product comparison is the finite
   coordinate-reindexing isomorphism, including rank zero. Restriction commutes with
   products and tensor (localized-site tensor restriction); the local inverses glue.
7. Termwise derived products and step 6 give countable-product preservation for tensor.
   Additive right derivation and exact termwise descent give triangulated functors.
8. For a tower with shift s, normalize the product comparison phi by projections.
   The product universal property gives phi F(s) = s' phi, hence the same identity
   for 1-s. Apply F to the Roos triangle and transport its product vertices by phi.
   This is precisely the image tower's Roos triangle. No canonical comparison
   between arbitrary cones is asserted.
-/
theorem formalClosedSupportII
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {X Z V S : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) (a : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [IsOpenImmersion a]
    (_hij : Set.range i = (Set.range j)ᶜ)
    (L : FormalSupportModules Λ S)
    (_hL : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ S))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ S)).obj L)) :
    ClosedSupportIIAssertions (formalClosedSupport Λ i j).rightDerivedFunctor ∧
    ClosedSupportIIAssertions ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
      (upperStar Λ a).mapDerivedCategory) ∧
    ClosedSupportIIAssertions ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) ∧
    Exists fun [_h : PreservesFiniteLimits (MonoidalCategory.tensorLeft L)] ↦
      Nonempty (((derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) ≅
          (MonoidalCategory.tensorLeft L).mapDerivedCategory) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
