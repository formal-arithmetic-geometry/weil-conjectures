/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FormalClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Closed support and sequential derived limits

Source: Stacks Project, Tag 09AA; blueprint
`sec-six-functors-basics/sk-lem-formal-closed-support-ii`, node
`det-formal-closed-support-ii-limits`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical commutation with shifts of the derived tensor functor
`K ⊗ᴸ_{Λ_X} -` on `D(X_proét, Λ)`, induced from the tensor product of complexes
(`DerivedCategory.commShiftTensorLeft`); this is the shift structure with which
`L[0] ⊗ᴸ -` is a triangulated functor. Source: Stacks Project, Tag 06YU
(definition-derived-tor); blueprint `def-sfb-derived-tensor-modules`,
used by `det-formal-closed-support-ii-limits` (blueprint:
det-formal-closed-support-ii-limits). -/
noncomputable instance derivedTensorObjCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (K : DerivedCategory (FormalSupportModules Λ X)) :
    ((derivedTensor Λ X).obj K).CommShift ℤ :=
  DerivedCategory.commShiftTensorLeft (FormalSupportModules Λ X) K

/--
The properties required of each functor in the closed-support limits statement, for a
functor `F` with its given (canonical) commutation with shifts.
Source: Stacks Project, Tag 09AA; blueprint
`det-formal-closed-support-ii-limits`.
-/
structure ClosedSupportLimitFunctorProperties
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] : Prop where
  additive : F.Additive
  triangulated : F.IsTriangulated
  products : ∀ (I : Type (max u v w x)),
    PreservesLimitsOfShape (Discrete I) F
  fibers : ∀ (T : Triangle C), T ∈ distTriang C →
    F.mapTriangle.obj T ∈ distTriang D
  sequential_limits :
    ∀ {K : ℕ → C} [HasProduct K]
      (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (L : C) (p : L ⟶ ∏ᶜ K)
      (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ →
      ∀ [HasProduct (fun n : ℕ => F.obj (K n))],
      ∃ e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n : ℕ => F.obj (K n)),
        (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) ∧
        IsDerivedLimitTriangle (fun n : ℕ => F.map (f n))
          (F.obj L) (F.map p ≫ e.hom)
          (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
  comparison_isIso :
    ∀ {K : ℕ → C} [HasProduct K]
      (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (L : C) (p : L ⟶ ∏ᶜ K)
      (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ →
      ∀ [HasProduct (fun n : ℕ => F.obj (K n))]
      (L' : D) (p' : L' ⟶ ∏ᶜ (fun n : ℕ => F.obj (K n)))
      (δ' : (∏ᶜ (fun n : ℕ => F.obj (K n))) ⟶ L'⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle (fun n : ℕ => F.map (f n)) L' p' δ' →
      (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n : ℕ => F.obj (K n))) →
      (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) →
      (ψ : F.obj L ⟶ L') →
      (ψ ≫ p' = F.map p ≫ e.hom) →
      ((e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
        (shiftFunctor D (1 : ℤ)).map ψ = δ') →
      IsIso ψ

/-- Assertions that closed support and finite-free tensoring preserve products,
fibers, and sequential derived limits. Source: Stacks Project, Tag 09AA;
blueprint `det-formal-closed-support-ii-limits`.

Proof: the support kernel is computed sectionwise and commutes with products and
finite limits; the inverse-image and direct-image module functors preserve these
limits and their derived functors are triangulated. K-injective resolutions and
termwise products identify the derived products, and the Roos triangle is carried
to the Roos triangle of the image tower. On a covering trivializing the finite
locally free module, tensor is a finite direct-sum functor, hence exact and
product preserving; the same termwise calculation gives its derived statement.
The product comparison is the one commuting with every projection, and every
Roos-triangle completion with those product comparisons is invertible by TR3.
-/
structure ClosedSupportIILimitsAssertions
    {Z V X S : Scheme.{u}} (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : Z ⟶ X) (j : V ⟶ X) (u : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion u]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : FormalSupportModules Λ S) : Prop where
  j_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ j).mapDerivedCategory)
  u_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ u).mapDerivedCategory)
  u_star_closed_support : ClosedSupportLimitFunctorProperties
    ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
      (formalSupportPullback Λ u).mapDerivedCategory)
  i_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ i).mapDerivedCategory)
  rj_star : ClosedSupportLimitFunctorProperties
    ((lowerStar Λ j).rightDerivedFunctor)
  closed_support : ClosedSupportLimitFunctorProperties
    ((formalClosedSupport Λ i j).rightDerivedFunctor)
  tensor : ClosedSupportLimitFunctorProperties
    ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L))

/-- Closed support commutes with derived limits of sequences.
Source: Stacks Project, Tag 09AA; blueprint
`sec-six-functors-basics/sk-lem-formal-closed-support-ii`, node
`det-formal-closed-support-ii-limits` (blueprint: det-formal-closed-support-ii-limits).

Proof plan from the node:
1. The coefficient comparison identifies every module pullback with the transported
inverse-image functor. Apply `lem-weil-pbc-proetale-immersion-limit-preservation` to
`i`, `j`, and `u`; these functors are additive, exact, triangulated, and preserve
products. The derived product comparison is computed termwise by
`det-pe-products-derived`.
2. The adjunction in `def-sfb-module-upper-lower-adjunction` makes `j_*` a right
adjoint, so `lem-weil-pbc-right-adjoint-preserves-limits` gives products. The unit
kernel is computed sectionwise using `sk-lem-formal-closed-support` and
`lem-weil-pbc-module-sheaves-limits-sectionwise`; applying `i^*` gives the closed
support functor and its finite-limit and product preservation.
3. Resolve a small family by K-injectives using
`prop-pur-kinjective-resolutions-exist`. The product of the resolutions is
K-injective by `lem-pc-ringed-space-product-kinjective`, so the definition in
`def-sfb-right-derived-functor` and `det-pe-products-derived` identify derived
products for `Rj_*` and `RΓ_Z`.
4. Apply `lem-pc-right-derived-functor-triangulated` to the additive functors
`j_*` and the support kernel. Together with the exact pullbacks this gives the
triangulated and fiber clauses for all restriction, direct-image, and support
functors.
5. On a cover trivializing the finite locally free `L`, tensor is a finite direct
sum and is exact and product preserving by
`lem-weil-pbc-condensed-finite-free-tensor-exact` and
`lem-pc-sheaf-modules-tensor-closed`. The derived tensor API
`def-sfb-derived-tensor-modules` and `lem-sfb-derived-monoidal` identify its
termwise derived functor, so it is triangulated, preserves fibers and products.
6. For every tower, write its Roos triangle using `def-weil-derived-limit`. The
canonical product comparison identifies the image of `1 - s` with the transition
endomorphism of the image tower. Applying the triangulated functor gives the image
Roos triangle, and hence the sequential derived-limit clause. The comparison is
projection-compatible by the product universal property.
7. For any second Roos triangle, rotate both triangles and use TR3 from
`def-weil-triangulated-category` to complete the identity on the two product terms.
`lem-sf-triangle-morphism-iso` then makes the third component invertible. No
canonical cone or comparison is selected.
-/
theorem formalClosedSupportIILimitsAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {Z V X S : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : V ⟶ X) (u : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion u]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : FormalSupportModules Λ S)
    (hL : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ c : 𝒰.I₀, ∃ n : ℕ,
        Nonempty
          ((formalSupportPullback Λ (𝒰.f c)).obj L ≅
            Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n)) :
    Nonempty (ClosedSupportIILimitsAssertions Λ i j u hij L) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
