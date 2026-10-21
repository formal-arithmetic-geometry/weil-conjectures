/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.InverseImageModule
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import Sheaf.AlgebraicGeometry.SupportedProductSupportCongruence
import Sheaf.AlgebraicGeometry.SupportedFullSupportProduct
import Sheaf.AlgebraicGeometry.ProEtaleSupportedProductNaturality
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
import Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing
import Sheaf.AlgebraicGeometry.SupportSiteComparison
import Sheaf.AlgebraicGeometry.SupportedProductLocalization

/-!
# Kunneth for cohomology with closed support

Source: blueprint, sec-smooth-purity/sk-prop-an,
`lem-pur-kunneth-supported`, order 1939 (blueprint: lem-pur-kunneth-supported).

The coefficient ring is the existing finite extension quotient. Its discrete topology
and finiteness instances implement the coefficient convention for origin witnesses.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] HomologicalComplex₂.total

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- Finiteness of the specified positive-level coefficient ring, from its existing
finiteness theorem. Source: blueprint `def-weil-finite-field-fiber`, coefficient clause
(blueprint: lem-pur-kunneth-supported). -/
noncomputable instance supportedKunnethCoefficient_finite
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)

/-- Finite coefficients carry the discrete topology.
Source: blueprint `def-weil-pbc-etale-origin-witness`, finite coefficient convention
(blueprint: lem-pur-kunneth-supported). -/
instance supportedKunnethCoefficient_topology
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    TopologicalSpace (Padic.coefficientExtensionRing l E n) := ⊥

/-- Discreteness of the coefficient convention.
Source: blueprint `def-weil-pbc-etale-origin-witness`
(blueprint: lem-pur-kunneth-supported). -/
instance supportedKunnethCoefficient_discrete
    (l : ℕ) [Fact l.Prime] (E : Type v) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    DiscreteTopology (Padic.coefficientExtensionRing l E n) := ⟨rfl⟩

private theorem isGE_tensor_right
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {a b : ℤ} {L : DerivedCategory C} (hL : _root_.DerivedCategory.torAmplitudeIn C a b L)
    (K : DerivedCategory C) (c : ℤ) [K.IsGE c] : (K ⊗ L).IsGE (a + c) := by
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory C
  have := DerivedCategory.isGE_tensor_of_torAmplitudeIn hL K c
  exact DerivedCategory.TStructure.t.isGE_of_iso (β_ L K) (a + c)

/-- A bounded-below first factor and a finite-Tor-amplitude second factor have a
bounded-below external product. Source: blueprint Kunneth proof, first paragraph
(blueprint: lem-pur-supported-product-bounded-below).

Proof: exact pullback preserves the lower bound c of K and the Tor interval [a,b]
of L. The general Tor-amplitude tensor estimate places the reversed tensor in
D≥a+c. The derived braiding gives the bound for the specified external product.
-/
theorem supportedExternalProduct_boundedBelow
    (A : Type (u + 1)) [CommRing A] {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategoryModule A Y)
    (hL : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L) :
    ∃ q : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L).IsGE q := by
  obtain ⟨c, hc⟩ := K.property
  obtain ⟨a, b, hL⟩ := hL
  have : K.obj.IsGE c := hc
  have hP : ((upperStar (ModuleCat.{u + 1} A)
      (pullback.fst f g)).mapDerivedCategory.obj K.obj).IsGE c :=
    Functor.isGE_mapDerivedCategory_obj _ _ c
  have hP' : ((upperStar (ModuleCat.{u + 1} A)
      (pullback.fst f g)).leftDerivedFunctor.obj K.obj).IsGE c :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).app K.obj).symm c
  have hQ := torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} A)
    (pullback.snd f g) a b
    (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hL)
  exact ⟨a + c, isGE_tensor_right hQ
    ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.obj K.obj) c⟩

-- Keep the actual pairings folded while comparing their arguments and instances.
attribute [local irreducible] supportedExteriorProduct ordinaryGlobalKunnethMap
  ProEtale.supportedExteriorProduct

private theorem intersection_id_complement {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (supportIntersection (𝟙 X) i).openComplement = i.openComplement := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_openComplement, supportIntersection,
    Scheme.Pullback.range_fst_comp]
  change (Set.range id ∩ Set.range i)ᶜ = (Set.range i)ᶜ
  simp

private theorem localizeFirst
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ q : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE q)
    (h₂ : IsIso (supportedExteriorProduct A f g (𝟙 X) j K.obj L.obj))
    (h₃ : IsIso (supportedExteriorProduct A (i.openComplement.ι ≫ f) g
      (supportOnOpen (𝟙 X) i.openComplement) j
      ((upperStar (ModuleCat.{u + 1} A) i.openComplement.ι).mapDerivedCategory.obj K.obj)
      L.obj)) : IsIso (supportedExteriorProduct A f g i j K.obj L.obj) := by
  obtain ⟨hS, hT, m, hm₁, hm₂, hm₃⟩ :=
    supportedProductLocalizationFirst k A f g (𝟙 X) i j K L hF
  have h₂' : IsIso m.hom₂ := by rw [hm₂]; exact h₂
  have h₃' : IsIso m.hom₃ := by
    rw [hm₃]
    unfold supportedFirstLocalizationComponent₃
    infer_instance
  have h₁ := Pretriangulated.isIso₁_of_isIso₂₃ m hS hT h₂' h₃'
  rw [hm₁] at h₁
  dsimp only [supportedFirstLocalizationComponent₁,
    supportedSecondLocalizationComponent₁] at h₁
  let := h₁
  have h₁' : IsIso (supportedExteriorProduct A f g (supportIntersection (𝟙 X) i) j
      K.obj L.obj) := by
    exact IsIso.of_isIso_comp_right _
      ((derivedSupportCongruence A _ _ (supportedFirstIntersection_complement f g
        (𝟙 X) i j)).hom.app (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj))
  exact (isIso_supportedExteriorProduct_iff_supportComplement_eq A f g
    (supportIntersection (𝟙 X) i) i j j (intersection_id_complement i) rfl K.obj L.obj).1 h₁'

private theorem localizeSecond
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ q : ℤ, (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE q)
    (h₂ : IsIso (supportedExteriorProduct A f g i (𝟙 Y) K.obj L.obj))
    (h₃ : IsIso (supportedExteriorProduct A f (j.openComplement.ι ≫ g)
      i (supportOnOpen (𝟙 Y) j.openComplement) K.obj
      ((upperStar (ModuleCat.{u + 1} A) j.openComplement.ι).mapDerivedCategory.obj L.obj))) :
    IsIso (supportedExteriorProduct A f g i j K.obj L.obj) := by
  obtain ⟨hS, hT, m, hm₁, hm₂, hm₃⟩ :=
    supportedProductLocalizationSecond k A f g i j (𝟙 Y) K L hF
  have h₂' : IsIso m.hom₂ := by rw [hm₂]; exact h₂
  have h₃' : IsIso m.hom₃ := by
    rw [hm₃]
    unfold supportedSecondLocalizationComponent₃
    infer_instance
  have h₁ := Pretriangulated.isIso₁_of_isIso₂₃ m hS hT h₂' h₃'
  rw [hm₁] at h₁
  dsimp only [supportedFirstLocalizationComponent₁,
    supportedSecondLocalizationComponent₁] at h₁
  let := h₁
  have h₁' : IsIso (supportedExteriorProduct A f g i (supportIntersection (𝟙 Y) j)
      K.obj L.obj) := by
    exact IsIso.of_isIso_comp_right _
      ((derivedSupportCongruence A _ _ (supportedSecondIntersection_complement f g
        i j (𝟙 Y))).hom.app (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj))
  exact (isIso_supportedExteriorProduct_iff_supportComplement_eq A f g i i
    (supportIntersection (𝟙 Y) j) j rfl (intersection_id_complement j) K.obj L.obj).1 h₁'

private theorem fullFirst_supportedKunneth
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hOrd : ∀ {T U : Scheme.{u}} (f : T ⟶ Spec (.of k)) (g : U ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
      (K : DerivedCategoryModule A T) (L : DerivedCategoryModule A U),
      IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A)
        (pullback.fst f g) (pullback.snd f g) K L))
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsIso i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L.obj) :
    IsIso (supportedExteriorProduct A f g i j K.obj L.obj) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsIso (supportOnOpen (𝟙 Y) j.openComplement) := by
    unfold supportOnOpen
    infer_instance
  apply localizeSecond k A f g i j K L (supportedExternalProduct_boundedBelow A f g K L.obj hL)
  · exact isIso_supportedExteriorProduct_of_fullSupport A f g i (𝟙 Y) K.obj L.obj
      (hOrd f g K.obj L.obj)
  · exact isIso_supportedExteriorProduct_of_fullSupport A f (j.openComplement.ι ≫ g)
      i (supportOnOpen (𝟙 Y) j.openComplement) K.obj
      ((upperStar (ModuleCat.{u + 1} A) j.openComplement.ι).mapDerivedCategory.obj L.obj)
      (hOrd f (j.openComplement.ι ≫ g) K.obj _)

private theorem closed_supportedKunneth
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hOrd : ∀ {T U : Scheme.{u}} (f : T ⟶ Spec (.of k)) (g : U ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
      (K : DerivedCategoryModule A T) (L : DerivedCategoryModule A U),
      IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A)
        (pullback.fst f g) (pullback.snd f g) K L))
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L.obj) :
    IsIso (supportedExteriorProduct A f g i j K.obj L.obj) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsIso (supportOnOpen (𝟙 X) i.openComplement) := by
    unfold supportOnOpen
    infer_instance
  apply localizeFirst k A f g i j K L (supportedExternalProduct_boundedBelow A f g K L.obj hL)
  · exact fullFirst_supportedKunneth k A hOrd f g (𝟙 X) j K L hL
  · exact fullFirst_supportedKunneth k A hOrd (i.openComplement.ι ≫ f) g
      (supportOnOpen (𝟙 X) i.openComplement) j
      ((upperStar (ModuleCat.{u + 1} A) i.openComplement.ι).mapDerivedCategoryPlus.obj K)
      L hL

private theorem characteristic_eq (D : WeilConjectures.FiniteFieldDatum.{u}) :
    ringChar D.k = D.p := by
  have hchar0 : ringChar D.k₀ = D.p := by
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have hc : Fintype.card D.k₀ = D.q := by
      simpa only [Nat.card_eq_fintype_card] using D.card_base
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
    exact ringChar.eq D.k₀ D.p
  exact (Algebra.ringChar_eq D.k₀ D.k).symm.trans hchar0

set_option backward.isDefEq.respectTransparency true

private theorem over_mk_predicate
    {C : Type*} [Category C] {S : C}
    (P : ∀ X Y : C, (X ⟶ S) → (Y ⟶ S) → Prop)
    (h : ∀ T U : Over S, P T.left U.left T.hom U.hom)
    {X Y : C} (f : X ⟶ S) (g : Y ⟶ S) : P X Y f g :=
  h (Over.mk f) (Over.mk g)

attribute [local instance 2000] CommRing.toRing

private theorem ordinaryFiniteCoefficientIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    ∀ {T U : Scheme.{u}} (f : T ⟶ Spec (.of D.k))
      (g : U ⟶ Spec (.of D.k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
      (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) T)
      (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) U),
      IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (pullback.fst f g) (pullback.snd f g) K L) := by
  apply over_mk_predicate (fun T U f g ↦
    ∀ [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
      (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) T)
      (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) U),
      IsIso (ordinaryGlobalKunnethMap
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (pullback.fst f g) (pullback.snd f g) K L))
  intro T U _ _ _ _ _ _ K L
  exact isIso_ordinaryGlobalKunnethMap_finiteCoefficientRing D l
    (by simpa only [characteristic_eq D] using hl) E n Fact.out T U K L

private theorem supportComparisonUnbounded_isIso
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T Z : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (i : Z ⟶ T) [IsClosedImmersion i]
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (ProEtale.supportComparisonUnbounded A i K) := by
  have := ProEtale.supportComparison_isIso A i k
  let e :=
    (Functor.rightDerivedFunctorNatIso (ProEtale.supportKernelEvaluationIso A i)).app K.obj ≪≫
    ((ProEtale.etaleSupportKernel A i).rightDerivedFunctorPlusCompatibility.app K).symm ≪≫
    DerivedCategory.Plus.ι.mapIso ((asIso (ProEtale.supportComparison A i)).app K) ≪≫
    (ProEtale.supportSections i A).rightDerivedFunctorPlusCompatibility.app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj K)
  change IsIso e.hom
  infer_instance

private theorem canonical_proEtale_product_isIso
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z W : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ q : ℤ, (externalProduct (ModuleCat.{u + 1} A)
      (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) K.obj L.obj).IsGE q)
    (hκ : IsIso (supportedExteriorProduct A (X ↘ Spec (.of k))
      (Y ↘ Spec (.of k)) i j K.obj L.obj)) :
    IsIso (ProEtale.supportedExteriorProductOverField A k
      (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj)
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L.obj)) := by
  let f := X ↘ Spec (.of k)
  let g := Y ↘ Spec (.of k)
  let : (pullback f g).Over (Spec (.of k)) := ⟨pullback.fst f g ≫ f⟩
  have : LocallyOfFiniteType (pullback f g ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pullback.fst f g ≫ f)
    infer_instance
  have : QuasiCompact (pullback f g ↘ Spec (.of k)) := by
    change QuasiCompact (pullback.fst f g ≫ f)
    infer_instance
  have : IsSeparated (pullback f g ↘ Spec (.of k)) := by
    change IsSeparated (pullback.fst f g ≫ f)
    infer_instance
  let F : DerivedCategory.Plus
      (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj, hF⟩
  have h := ProEtale.supportComparison_exterior A k i j K L F (Iso.refl _)
  have := supportComparisonUnbounded_isIso k A i K
  have := supportComparisonUnbounded_isIso k A j L
  have := supportComparisonUnbounded_isIso k A (supportedProductImmersion f g i j) F
  let := hκ
  let κp := ProEtale.supportedExteriorProductOverField A k f g i j
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj)
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L.obj)
  have hcomp : IsIso (tensorHom (ProEtale.supportComparisonUnbounded A i K)
      (ProEtale.supportComparisonUnbounded A j L) ≫ κp) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (tensorHom (ProEtale.supportComparisonUnbounded A i K)
      (ProEtale.supportComparisonUnbounded A j L)) κp

@[irreducible]
private noncomputable def witnessTransportIso
    (A : Type (u + 1)) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (T : Scheme.{u}) (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus T A)
    (w : ProEtale.EtaleOriginWitness T A Kp)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : w.L.obj ≅ K) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K ≅
      (ProEtale.fixedRingDerivedTransport T A).obj Kp.obj :=
  let G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := ProEtale.finiteCoefficientRealization T A
  G.mapDerivedCategory.mapIso hK.symm ≪≫
    R.mapDerivedCategory.asEquivalence.unitIso.app (G.mapDerivedCategory.obj w.L.obj) ≪≫
    R.mapDerivedCategory.inv.mapIso
      ((Functor.mapDerivedCategoryCompIso G R).symm.app w.L.obj ≪≫
        DerivedCategory.Plus.ι.mapIso w.alpha)


private theorem supportedKunneth_generic
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (hOrd : ∀ {T U : Scheme.{u}} (f : T ⟶ Spec (.of k)) (g : U ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
      (K : DerivedCategoryModule A T) (L : DerivedCategoryModule A U),
      IsIso (ordinaryGlobalKunnethMap (ModuleCat.{u + 1} A)
        (pullback.fst f g) (pullback.snd f g) K L))
    {X Y Z W : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Bounded
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hL : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b
      L.obj) :
    IsIso (supportedExteriorProduct A
      (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)) i j K.obj L.obj) ∧
    ∀ (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus X A)
      (Lp : ProEtale.FiniteCoefficientDerivedCategoryPlus Y A)
      (wx : ProEtale.EtaleOriginWitness X A Kp)
      (wy : ProEtale.EtaleOriginWitness Y A Lp)
      (_hx : wx.L.obj ≅ K.obj) (_hy : wy.L.obj ≅ L.obj),
      IsIso (ProEtale.supportedExteriorProductOverField A k
        (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)) i j
        ((ProEtale.fixedRingDerivedTransport X A).obj Kp.obj)
        ((ProEtale.fixedRingDerivedTransport Y A).obj Lp.obj))
          := by
  let Kplus : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K.obj, K.property.1⟩
  let Lplus : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨L.obj, L.property.1⟩
  have hκ := closed_supportedKunneth k A hOrd
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j Kplus Lplus _hL
  refine ⟨hκ, ?_⟩
  have hcanon := canonical_proEtale_product_isIso k A i j Kplus Lplus
    (supportedExternalProduct_boundedBelow A (X ↘ Spec (.of k))
      (Y ↘ Spec (.of k)) Kplus L.obj _hL) hκ
  intro Kp Lp wx wy hx hy
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  dsimp only [ProEtale.supportedExteriorProductOverField] at hcanon ⊢
  exact ProEtale.isIso_supportedExteriorProduct_of_iso A
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j
    (witnessTransportIso A X Kp wx K.obj hx)
    (witnessTransportIso A Y Lp wy L.obj hy) hcanon


/-- The supported exterior product is an isomorphism for bounded complexes with the
second factor of finite Tor amplitude, including every specified pro-etale realization.
Source: blueprint `lem-pur-kunneth-supported`, order 1939
(blueprint: lem-pur-kunneth-supported).

Proof:
1. Set U = X minus Z, V = Y minus W, and F = p_X^*K tensor^L p_Y^*L.
Finite-type schemes over the field are Noetherian. Finite basic-open covers show U,V
are finite type, and restricting the closed diagonals shows they are separated. The
same affine-chart and diagonal argument applies to X times Y. Choose a lower bound c
for K and Tor bounds a,b for L. Exact pullback preserves the lower bound c and the
Tor interval [a,b]. The general derived-tensor estimate, followed by the derived
braiding, gives lower bound a+c for the external product. The same estimate applies
after restricting K to each open complement. Thus all support triangles apply.
2. Apply lem-pur-support-restriction-triangle on Y for W, tensor with RΓ(X,K),
and compare with the support triangle of X times W. The actual supported and ordinary
exterior products form a morphism of triangles, including the connecting map, by
lem-pur-supported-product-localization. Ordinary Kunneth for (X,Y) and (X,V), from
lem-pur-ordinary-kunneth-finite-ring, makes the other two components isomorphisms.
lem-sf-triangle-morphism-iso gives the supported product for X times W.
3. Repeat step 2 with U in place of X to obtain the supported product for U times W.
4. Tensor the support triangle for Z in X with RΓ_W(Y,L). Compare with the triangle
for the supports Z times W inside X times W in X times Y. Its three components are
exactly the supported products for (Z,W), (X,W), and (U,W), by the localization
compatibility. Steps 2 and 3 and the triangle isomorphism lemma give the first clause.
5. For canonical etale-origin witnesses, lem-pur-support-site-comparison identifies
the pro-etale product with the etale product conjugated by the supported comparison
isomorphisms and the external-product comparison. Every factor is invertible. For
arbitrary specified witnesses alpha,beta, naturality of supported sections, pullback,
and tensor identifies the product with that for the canonical witnesses conjugated
by RΓ_Z(alpha) tensor RΓ_W(beta) and RΓ_{Z times W}(alpha external beta).
These are isomorphisms, proving the second clause for the actual pro-etale product.
-/
theorem isIso_supportedExteriorProduct
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y Z W : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (L : DerivedCategory.Bounded
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))))
    (_hL : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b
      L.obj) :
    IsIso (supportedExteriorProduct (Padic.coefficientExtensionRing l E n)
      (X ↘ Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) i j K.obj L.obj) ∧
    ∀ (Kp : ProEtale.FiniteCoefficientDerivedCategoryPlus X (Padic.coefficientExtensionRing l E n))
      (Lp : ProEtale.FiniteCoefficientDerivedCategoryPlus Y (Padic.coefficientExtensionRing l E n))
      (wx : ProEtale.EtaleOriginWitness X (Padic.coefficientExtensionRing l E n) Kp)
      (wy : ProEtale.EtaleOriginWitness Y (Padic.coefficientExtensionRing l E n) Lp)
      (_hx : wx.L.obj ≅ K.obj) (_hy : wy.L.obj ≅ L.obj),
      IsIso (ProEtale.supportedExteriorProductOverField (Padic.coefficientExtensionRing l E n) D.k
        (X ↘ Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) i j
        ((ProEtale.fixedRingDerivedTransport X (Padic.coefficientExtensionRing l E n)).obj Kp.obj)
        ((ProEtale.fixedRingDerivedTransport Y (Padic.coefficientExtensionRing l E n)).obj Lp.obj))
          := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact supportedKunneth_generic D.k (Padic.coefficientExtensionRing l E n)
    (fun {T U : Scheme.{u}} ↦
      ordinaryFiniteCoefficientIso D l _hl E n (T := T) (U := U)) i j K L _hL

end AlgebraicGeometry.Etale
