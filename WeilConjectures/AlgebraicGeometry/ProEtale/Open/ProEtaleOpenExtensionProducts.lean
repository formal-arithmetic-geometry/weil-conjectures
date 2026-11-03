/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjectProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.CategoryTheory.Exact.ExactLocalizationDerivedTriangle

/-!
# Products and sequential derived limits of open extensions

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
`det-sf-open-closed-extension-zero-limits`, clauses (1)--(3); Stacks Project,
Tags 09BN, 0152, 070I and 08TC
(blueprint: det-sf-open-closed-extension-zero-limits).

The ring sheaf is an arbitrary monoid object in abelian sheaves. The module functors
are the recorded open-closed module-object functors, without commutative or constant
coefficient hypotheses. Derived categories use the standard localization universe.
The closed localization is descended as a composite, so no independent choice of a
localization on the closed stratum is needed.

## Main definitions

* `ringSheafDerivedCategory`: the existing derived category in its standard universe.
* `ringSheafDerivedOpenExtension`: termwise descent of the recorded exact open extension.
* `ringSheafDerivedDirectImage`: the recorded total right derived functor of direct image.
* `ringSheafDerivedClosedLocalization`: termwise descent of the exact composite `i_* i^*`.

## Main statement

* `proEtale_openExtension_products_derivedLimits`: the natural triangle, preservation of
  derived products and sequential Roos limits, and preservation of sheaf products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The unbounded derived category of modules over an arbitrary pro-etale ring sheaf,
using the standard localization of the recorded module category. This is only a transparent
specialization of `DerivedCategory`, not a new localization or module category.
Source: Stacks, Tag 05RU; blueprint clause (1)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
abbrev ringSheafDerivedCategory (X : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  @DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
    _ _ (HasDerivedCategory.standard _)

/-- Exact open extension applied termwise and descended through quasi-isomorphisms.
Its coefficients on the open are the actual inverse image of `B`.
Source: Stacks, Tags 03DI, 03DJ and 015F; blueprint clauses (1)--(2)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
def ringSheafDerivedOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B) ⥤
      ringSheafDerivedCategory X B :=
  letI := HasDerivedCategory.standard
    (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) ((upperStar Ab.{u + 1} j).obj B))
  letI := HasDerivedCategory.standard (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
  (ringSheafOpenExtension j B).mapDerivedCategory

/-- Total right derived direct image over the inverse-image ring. The existence proof
passed to the recorded universal-pair construction uses the functorial K-injective
replacement in the Grothendieck abelian module category. Thus the result is determined
up to its unique unit-compatible isomorphism and computed on every K-injective resolution.
Source: Stacks, Tags 070K and 070Y; blueprint clause (1)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
def ringSheafDerivedDirectImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafDerivedCategory T ((upperStar Ab.{u + 1} f).obj B) ⥤
      ringSheafDerivedCategory X B :=
  letI := HasDerivedCategory.standard
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ((upperStar Ab.{u + 1} f).obj B))
  letI := HasDerivedCategory.standard (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
  letI := Mod.isGrothendieckAbelian.{u + 1} ((upperStar Ab.{u + 1} f).obj B)
  (ringSheafDirectImage f B).rightDerivedFunctorOfQuasiIsoResolutions
    (fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u + 1} _).obj K,
      (CochainComplex.toKInjectiveResolution.{u + 1} _).app K, inferInstance,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} _ K).2⟩)

/-- Termwise descent of `i_* i^*` for the specified complementary immersions. Exactness
of `i_*` is the recorded open-closed sequence theorem; inverse image is exact on carriers.
On every representative this is exactly the third term in the blueprint's triangle,
with the ring on the closed stratum equal to the inverse image of `B`.
Source: Stacks, Tags 09BM, 09AH and 015F; blueprint clause (1)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
def ringSheafDerivedClosedLocalization {X Z U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafDerivedCategory X B ⥤ ringSheafDerivedCategory X B :=
  letI := HasDerivedCategory.standard (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
  letI : PreservesFiniteColimits (ringSheafDirectImage i B) :=
    (proEtale_openClosed_sequence_ring_sheaf i j hU B).2.2.2.2.2.2.1
  letI : PreservesFiniteLimits (ringSheafInverseImage i B ⋙ ringSheafDirectImage i B) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (ringSheafInverseImage i B ⋙ ringSheafDirectImage i B) :=
    comp_preservesFiniteColimits _ _
  (ringSheafInverseImage i B ⋙ ringSheafDirectImage i B).mapDerivedCategory

private theorem products_of_essSurj
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : Type*) [HasProductsOfShape I C]
    (Q : C ⥤ D) [Q.EssSurj] (F : D ⥤ E)
    [PreservesLimitsOfShape (Discrete I) Q]
    [PreservesLimitsOfShape (Discrete I) (Q ⋙ F)] :
    PreservesLimitsOfShape (Discrete I) F := by
  classical
  have h (K : I → D) : PreservesLimit (Discrete.functor K) F := by
    let K' := fun n ↦ Q.objPreimage (K n)
    let e : Discrete.functor K' ⋙ Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ Q.objObjPreimageIso (K n.as))
    have : PreservesLimit (Discrete.functor K' ⋙ Q) F :=
      preservesLimit_of_preserves_limit_cone
        (isLimitOfPreserves Q (limit.isLimit (Discrete.functor K')))
        (isLimitOfPreserves (Q ⋙ F) (limit.isLimit (Discrete.functor K')))
    exact preservesLimit_of_iso_diagram F e
  let := h
  exact preservesLimitsOfShape_of_discrete F

private theorem derived_products_of_Q
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : Type*) [HasProductsOfShape I C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete I) F]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := C))]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := D))] :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  have : PreservesLimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact products_of_essSurj I DerivedCategory.Q F.mapDerivedCategory

private theorem open_directImage_counit_iso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    IsIso (ringSheafAdjunction j B).counit := by
  have h : IsIso (upperStarLowerStarAdjunction Ab.{u + 1} j).counit := by
    let adj := openImmersionRestrictionLowerStarAdjunction Ab.{u + 1} j
    let : (lowerStar Ab.{u + 1} j).Full := adj.fullyFaithfulROfIsIsoCounit.full
    let : (lowerStar Ab.{u + 1} j).Faithful := adj.fullyFaithfulROfIsIsoCounit.faithful
    exact (upperStarLowerStarAdjunction Ab.{u + 1} j).counit_isIso_of_R_fully_faithful
  have h' (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      ((upperStar Ab.{u + 1} j).obj B)) :
      IsIso ((ringSheafAdjunction j B).counit.app N) := by
    have : IsIso ((Mod.forget _).map ((ringSheafAdjunction j B).counit.app N)) := by
      change IsIso
        ((((upperStarLowerStarAdjunction Ab.{u + 1} j).mapModAdjunction B).counit.app N).hom)
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact NatIso.isIso_of_isIso_app _

private theorem map_isDerivedLimit
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    {K : ℕ → C} [HasProduct K]
    [PreservesLimit (Discrete.functor K) F]
    (t : ∀ n : ℕ, K (n + 1) ⟶ K n) (L : C) (hL : IsDerivedLimit t L) :
    Exists fun [_hP : HasProduct (fun n : ℕ ↦ F.obj (K n))] ↦
      IsDerivedLimit (K := fun n : ℕ ↦ F.obj (K n))
        (fun n : ℕ ↦ F.map (t n)) (F.obj L) := by
  classical
  let : HasProduct (fun n : ℕ ↦ F.obj (K n)) :=
    ⟨⟨Fan.mk _ (fun n ↦ F.map (Pi.π K n)),
      isLimitOfHasProductOfPreservesLimit F K⟩⟩
  refine ⟨inferInstance, ?_⟩
  obtain ⟨p, δ, h⟩ := hL
  let e := PreservesProduct.iso F K
  have hs₀ : F.map (towerProductShift t) ≫ e.hom =
      e.hom ≫ towerProductShift (fun n ↦ F.map (t n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, e, PreservesProduct.iso_hom, piComparison_comp_π]
    rw [← F.map_comp, towerProductShift, Pi.lift_π, F.map_comp]
    simp [towerProductShift]
  have hs : F.map (towerTransitionEndomorphism t) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ F.map (t n)) := by
    dsimp only [towerTransitionEndomorphism]
    rw [F.map_sub, F.map_id, Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id, hs₀]
  refine ⟨F.map p ≫ e.hom,
    e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L, ?_⟩
  exact isomorphic_distinguished _ (F.map_distinguished _ h) _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm
      (by change (F.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map p; simp)
      (by
        change towerTransitionEndomorphism (fun n ↦ F.map (t n)) ≫ e.inv =
          e.inv ≫ F.map (towerTransitionEndomorphism t)
        rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
        exact hs.symm)
      (by
        change (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
          (shiftFunctor D (1 : ℤ)).map (𝟙 _) =
          e.inv ≫ (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
        simp))

/-- Open extension has a distinguished triangle natural in the input, preserves small
products on both derived categories and module sheaves, and sends every sequential Roos
limit to a sequential Roos limit. The existential product instance in the sequential clause
asserts existence of the image product; it imposes no additional hypothesis on the sequence.

Source: Weil blueprint, det-sf-open-closed-extension-zero-limits, clauses (1)--(3);
Stacks, Tags 09BN, 0152, 070I and 08TC
(blueprint: det-sf-open-closed-extension-zero-limits).

Proof:
1. The size convention fixes the sites and coefficient universes. The module categories
   are Grothendieck abelian (lem-weil-pbc-ring-sheaves-grothendieck), so
   lem-sfb-grothendieck-k-injective gives a K-injective representative J of K.
   def-sfb-right-derived-functor computes Rj_*K by j_*J. The exact sheaf functors from
   det-sf-open-closed-sequence-ring-sheaf and det-sf-open-closed-pullback-limits descend
   termwise and are triangulated by lem-sf-exact-functor-derived-triangulated.
2. Apply the open-closed sheaf sequence in each degree to j_*J. On every open-site
   object V, V times_X U = V, naturally and compatibly with the coefficient actions;
   hence j^*j_*J = J. The resulting short exact sequence of complexes gives the displayed
   triangle by lem-weil-pbc-complex-ses-triangle. Its boundary is natural on complexes.
   Compute derived morphisms on K-injectives using lem-weil-pbc-kinjective-hom-derived;
   additive functors preserve homotopies, so the three arrows are natural on D(U).
3. The same sheaf sequence identifies j_!N with the kernel of j_*N to i_*i^*j_*N.
   Sheaf products are sectionwise. Direct image j_* preserves them by evaluation on
   fibre products, i_* preserves them by its adjunction, and i^* preserves them by
   det-sf-open-closed-pullback-limits. Naturality identifies the product of the unit maps
   with the unit on the product. Kernels commute with products sectionwise, giving
   the canonical product comparison isomorphism, including the empty product.
4. det-pe-products-derived identifies derived products with termwise products on both
   sites. Apply the sheaf comparison degreewise to representatives. Its naturality in
   the differentials makes it a chain isomorphism, and its composites with every
   projection identify its localization with the canonical derived product comparison.
5. For any sequence put P = product K_n and let s be its transition shift. The canonical
   comparison phi: j_!P to product j_!K_n commutes with s: compose with each projection
   and use pr_n s = pr_(n+1) followed by t_n. Additivity gives compatibility with 1-s.
   Apply the triangulated j_! to any Roos triangle of L and transport its two product
   terms through phi. This is the Roos triangle of j_!L, as in def-weil-derived-limit.
   Products give existence by lem-weil-derived-limit-existence; any other chosen image
   Roos limit is isomorphic, with no canonical choice of cone asserted. -/
theorem proEtale_openExtension_products_derivedLimits
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    (∃ (a : ringSheafDerivedOpenExtension j B ⟶ ringSheafDerivedDirectImage j B)
      (b : ringSheafDerivedDirectImage j B ⟶ ringSheafDerivedDirectImage j B ⋙
        ringSheafDerivedClosedLocalization i j hU B)
      (c : ringSheafDerivedDirectImage j B ⋙ ringSheafDerivedClosedLocalization i j hU B ⟶
        ringSheafDerivedOpenExtension j B ⋙ shiftFunctor (ringSheafDerivedCategory X B) (1 : ℤ)),
      ∀ K, Triangle.mk (a.app K) (b.app K) (c.app K) ∈
        distTriang (ringSheafDerivedCategory X B)) ∧
    (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I)
      (ringSheafDerivedOpenExtension j B)) ∧
    (∀ (K : ℕ → ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B))
      (t : ∀ n : ℕ, K (n + 1) ⟶ K n) [HasProduct K]
      (L : ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B)),
      IsDerivedLimit t L →
      Exists fun [hP : HasProduct (fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).obj (K n))] ↦
        IsDerivedLimit (K := fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).obj (K n))
          (fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).map (t n))
          ((ringSheafDerivedOpenExtension j B).obj L)) ∧
    (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) (ringSheafOpenExtension j B)) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    ((upperStar Ab.{u + 1} j).obj B)
  let D := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  let seq := proEtale_openClosed_sequence_ring_sheaf i j hU B
  let F := ringSheafOpenExtension j B
  let S := ringSheafInverseImage j B
  let G := ringSheafDirectImage j B
  let H := ringSheafInverseImage i B ⋙ ringSheafDirectImage i B
  let : PreservesFiniteColimits (ringSheafDirectImage i B) := seq.2.2.2.2.2.2.1
  let : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits H := comp_preservesFiniteColimits _ _
  let : IsIso (ringSheafAdjunction j B).counit := open_directImage_counit_iso j B
  let a : S ⋙ F ⟶ 𝟭 D := (ringSheafOpenAdjunction j B).counit
  let b : 𝟭 D ⟶ H := (ringSheafAdjunction i B).unit
  have hab (M : D) : a.app M ≫ b.app M = 0 :=
    ((seq.2.2.2.2.2.2.2.2.2.1 M).2.2.sc 0).zero
  have hseq (M : D) : (ShortComplex.mk (a.app M) (b.app M) (hab M)).ShortExact := by
    have hm := seq.2.2.2.2.2.2.2.2.2.1 M
    let : Mono (a.app M) := hm.1
    let : Epi (b.app M) := hm.2.1
    exact ⟨hm.2.2.exact 0 (by omega)⟩
  let := Mod.isGrothendieckAbelian.{u + 1} ((upperStar Ab.{u + 1} j).obj B)
  let h := fun K : CochainComplex C ℤ ↦
    (show ∃ (J : CochainComplex C ℤ) (s : K ⟶ J), J.IsKInjective ∧ QuasiIso s from
      ⟨(CochainComplex.kInjectiveResolutionFunctor.{u + 1} C).obj K,
        (CochainComplex.toKInjectiveResolution.{u + 1} C).app K, inferInstance,
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} C K).2⟩)
  have htri := exactLocalization_derived_triangle F S G (ringSheafAdjunction j B)
    H a b hab hseq h
  have hp (I : Type (u + 1)) : PreservesLimitsOfShape (Discrete I)
      (ringSheafDerivedOpenExtension j B) := by
    let := proEtale_moduleObject_products_exact U ((upperStar Ab.{u + 1} j).obj B) I
    let := proEtale_moduleObject_products_exact X B I
    let := sheaf_openExtension_products i j hU B I
    exact derived_products_of_Q I F
  refine ⟨htri, hp, ?_, sheaf_openExtension_products i j hU B⟩
  let : (ringSheafDerivedOpenExtension j B).Additive := by
    dsimp only [ringSheafDerivedOpenExtension]
    infer_instance
  let : (ringSheafDerivedOpenExtension j B).CommShift ℤ := by
    dsimp only [ringSheafDerivedOpenExtension]
    infer_instance
  let : (ringSheafDerivedOpenExtension j B).IsTriangulated := by
    dsimp only [ringSheafDerivedOpenExtension]
    infer_instance
  intro K t _ L hL
  let : PreservesLimitsOfShape (Discrete ℕ) (ringSheafDerivedOpenExtension j B) :=
    preservesLimitsOfShape_of_equiv
      (Discrete.equivalence Equiv.ulift) _
  exact map_isDerivedLimit (ringSheafDerivedOpenExtension j B) t L hL

set_option linter.unusedVariables false in
end AlgebraicGeometry.ProEtale
