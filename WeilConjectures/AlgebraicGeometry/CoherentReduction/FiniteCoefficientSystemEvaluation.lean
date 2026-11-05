/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentIntegralReduction
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility

/-! # Finite-coefficient presentations of the genuine system evaluations

Source: Zheng, Construction 4.1; Bhatt--Scholze, finite coefficient comparison.
(blueprint: def-sfb-finite-coefficient-system-evaluation)

The functors change only the presentation of the same module sheaves. In
particular the horizontal arrows below are those of the actual sequence topos.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.CoherentReduction

attribute [local instance] proEtSmall sequenceSmall

/-- Proof alias of the existing exactness-reflection criteria for scalar restriction.
The underlying abelian sheaf is unchanged; no new exactness theorem is postulated.
Source: Stacks 03D7 (blueprint: def-sfb-finite-coefficient-system-evaluation).
Proof: compose with the faithful exact forgetful functor to abelian sheaves, which
reflects finite limits and finite colimits, and use the corresponding forgetful
functor on the source ring. -/
private abbrev ringRestriction_exact (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} a) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} a) := by
  let U := SheafOfModules.toSheaf.{u + 1} R
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} a ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} S))
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} a ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

/-- The existing equivalence from constant-ring module sheaves to fixed-ring sheaves.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedEquivalence (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constant_ring_module_sheaves.{u + 1, u} (Scheme.ProEt.topology X) A).1.choose

/-- Its forward maps are the original scalar restrictions.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEquivalence_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (fixedEquivalence X A).functor.Additive :=
  (constant_ring_module_sheaves.{u + 1, u}
    (Scheme.ProEt.topology X) A).1.choose_spec.2.1

/-- Its inverse retains the original additive sections and maps.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEquivalence_inverse_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (fixedEquivalence X A).inverse.Additive :=
  (constant_ring_module_sheaves.{u + 1, u}
    (Scheme.ProEt.topology X) A).1.choose_spec.2.2.1

/-- Canonical finite realization on the pro-etale site, through the constant-section iso.
Source: finite coefficient comparison
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def finiteRealization (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤
      WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A) :=
  (fixedEquivalence X A).inverse ⋙
    SheafOfModules.restrictScalars (realizationRingIso.{u + 1, u}
      (Scheme.ProEt.topology X) A).hom ⋙
    res.{u + 1, u, u + 1} (finiteConstantIso X A).inv

/-- The inverse finite presentation, with its unchanged underlying additive maps.
Source: finite coefficient comparison
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def finiteUnrealization (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  res.{u + 1, u, u + 1} (finiteConstantIso X A).hom ⋙
    CategoryTheory.ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) A

/-- Finite realization is additive.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteRealization_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteRealization X A).Additive := by
  unfold finiteRealization
  infer_instance

/-- Finite realization preserves finite limits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteRealization_limits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteLimits (finiteRealization X A) := by
  unfold finiteRealization
  have h := ringRestriction_exact X
    (realizationRingIso.{u + 1, u} (Scheme.ProEt.topology X) A).hom
  let := h.1
  let := h.2
  infer_instance

/-- Finite realization preserves finite colimits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteRealization_colimits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteColimits (finiteRealization X A) := by
  unfold finiteRealization
  have h := ringRestriction_exact X
    (realizationRingIso.{u + 1, u} (Scheme.ProEt.topology X) A).hom
  let := h.1
  let := h.2
  infer_instance

/-- The inverse presentation is additive.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_additive (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteUnrealization X A).Additive := by
  let := CategoryTheory.ConstantScalarRestriction.additive (Scheme.ProEt.topology X) A
  unfold finiteUnrealization
  change (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
    (finiteConstantIso X A).hom ⋙ _).Additive
  infer_instance

/-- The inverse presentation preserves finite limits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_limits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteLimits (finiteUnrealization X A) := by
  let r := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (finiteConstantIso X A).hom
  have hr : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} r) :=
    (ringRestriction_exact X r).1
  have hs : PreservesFiniteLimits
      (CategoryTheory.ConstantScalarRestriction.restriction.{u + 1, u}
        (Scheme.ProEt.topology X) A) :=
    (CategoryTheory.ConstantScalarRestriction.exact.{u + 1, u}
      (Scheme.ProEt.topology X) A).1
  change PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} r ⋙ _)
  infer_instance

/-- The inverse presentation preserves finite colimits.
Source: Stacks 03DA (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_colimits (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    PreservesFiniteColimits (finiteUnrealization X A) := by
  let r := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (finiteConstantIso X A).hom
  have hr : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} r) :=
    (ringRestriction_exact X r).2
  have hs : PreservesFiniteColimits
      (CategoryTheory.ConstantScalarRestriction.restriction.{u + 1, u}
        (Scheme.ProEt.topology X) A) :=
    (CategoryTheory.ConstantScalarRestriction.exact.{u + 1, u}
      (Scheme.ProEt.topology X) A).2
  change PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} r ⋙ _)
  infer_instance

/-- The finite presentation is an exact equivalence, with its original section maps.
Source: Stacks 03CY (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance finiteUnrealization_isEquivalence (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteUnrealization X A).IsEquivalence := by
  let t := (SheafOfModules.ringIso_tensor_transport (finiteConstantIso X A)).some
  have : (res.{u + 1, u, u + 1} (finiteConstantIso X A).hom).IsEquivalence := by
    change (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (finiteConstantIso X A).hom).IsEquivalence
    rw [← t.functor_eq]
    infer_instance
  let := CategoryTheory.ConstantScalarRestriction.isEquivalence (Scheme.ProEt.topology X) A
  unfold finiteUnrealization
  infer_instance

/-- The ordinary tensor comparison sends local pure tensors to the same pure tensors.
Both factors use published, proved tensor-transport constructions.
Source: Stacks 03CY, 06YT
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
@[instance_reducible]
def finiteUnrealizationMonoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    (finiteUnrealization X A).Monoidal := by
  let t := (SheafOfModules.ringIso_tensor_transport (finiteConstantIso X A)).some
  letI : (res.{u + 1, u, u + 1} (finiteConstantIso X A).hom).Monoidal :=
    t.monoidal.toMonoidal
  letI := CategoryTheory.ConstantScalarRestriction.restrictionBraided (Scheme.ProEt.topology X) A
  unfold finiteUnrealization
  infer_instance

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary fixed-module evaluation of the actual system.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedEvaluation (X : Scheme.{u}) (n : ℕ) :
    Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) ⥤
      Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n)) :=
  evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X) (transitions l E X) n ⋙
      finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)

/-- Fixed evaluation preserves addition through the exact finite presentation.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEvaluation_additive (X : Scheme.{u}) (n : ℕ) :
    (fixedEvaluation l E X n).Additive := by unfold fixedEvaluation; infer_instance

/-- Fixed evaluation preserves finite limits through the exact finite presentation.
Source: Stacks 0941 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEvaluation_limits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (fixedEvaluation l E X n) := by
  unfold fixedEvaluation
  infer_instance

/-- Fixed evaluation preserves finite colimits through the exact finite presentation.
Source: Stacks 0941 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
instance fixedEvaluation_colimits (X : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (fixedEvaluation l E X n) := by
  unfold fixedEvaluation
  infer_instance

/-- Its exact derived evaluation, without choosing level objects.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedDerivedEvaluation (X : Scheme.{u}) (n : ℕ) :
    DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n))) :=
  e.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X) (transitions l E X) n ⋙
      (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)).mapDerivedCategory

/-- Exact derived etale-to-pro-etale comparison with the original fixed coefficients.
Source: Bhatt--Scholze, finite coefficient comparison
(blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def nu (X : Scheme.{u}) (n : ℕ) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E n))
    X).mapDerivedCategory

/-- The canonical derived comparison between scalar extension and `nu^*`.
Source: Stacks 09B1 and 0F63, via the scalar-restriction comparison square
(blueprint: def-sfb-finite-coefficient-system-evaluation).
The map is the mate of the existing comparison isomorphism, hence it is tied
to the derived scalar-extension adjunction and is not an arbitrary natural map. -/
noncomputable def nuFixedScalarExtensionComparisonMap (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
      CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
        (Scheme.ProEt.topology X) φ ⟶
    CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
      X.smallEtaleTopology φ ⋙
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory := by
  letI := CategoryTheory.Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint
    (Scheme.ProEt.topology X) φ
  letI := CategoryTheory.Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint
    X.smallEtaleTopology φ
  exact ((mateEquiv
    (G := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory)
    (H := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
    ).symm (TwoSquare.mk _ _ _ _ (Scheme.comparisonRestrictScalarsIso X A φ).hom)).natTrans

/-- The scalar-restriction comparison map of `DerivedMorphismSheafComparison` is the inverse of
the conjugate comparison `pbcComparisonRestrict`: both are the unique comparison of left adjoints
of the composite of comparison direct image and coextension of scalars. -/
lemma comparisonRestrictScalarsMap_eq_pbcComparisonRestrict_inv_app (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    Scheme.comparisonRestrictScalarsMap X A φ M = (pbcComparisonRestrict X φ).inv.app M := by
  let adj₁ := (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X)
  let adj₂ := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).comp
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
  have h : (pbcComparisonRestrict X φ).inv.app M =
      (Adjunction.leftAdjointUniq adj₁ adj₂).hom.app M := rfl
  rw [h]
  apply (adj₁.homEquiv _ _).injective
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂ M).symm
  change (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).homEquiv _ _
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ _
        (Scheme.comparisonRestrictScalarsMap X A φ M)) = adj₂.unit.app M
  rw [Scheme.comparisonRestrictScalarsMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  dsimp only [adj₂]
  rw [Adjunction.comp_unit_app]
  exact ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.naturality
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M)).symm

/-- The derived scalar-restriction comparison is the inverse of `pbcDerivedComparisonRestrict`. -/
lemma comparisonRestrictScalarsIso_eq_pbcDerivedComparisonRestrict_symm (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    Scheme.comparisonRestrictScalarsIso X A φ = (pbcDerivedComparisonRestrict X φ).symm := by
  have h : Scheme.comparisonRestrictScalarsSheafIso X A φ = (pbcComparisonRestrict X φ).symm := by
    refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
    exact comparisonRestrictScalarsMap_eq_pbcComparisonRestrict_inv_app X φ M
  ext1
  simp only [Scheme.comparisonRestrictScalarsIso, pbcDerivedComparisonRestrict, h,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    Category.assoc]

/-- The canonical `nu^*`/scalar-extension comparison is invertible.
Source: Stacks 09B1 and 0F63 (blueprint: def-sfb-finite-coefficient-system-evaluation).
Proof: compute derived scalar extension on K-flat complexes. Exact comparison
pullback preserves flat sheaves and commutes with sheafified scalar tensor.
The ordinary scalar tensor comparison is an isomorphism on every term. Passing
to the localization gives the displayed mate, because its restriction mate is
exactly comparisonRestrictScalarsIso. Hence the derived mate is invertible. -/
theorem nuFixedScalarExtensionComparisonMap_isIso (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsIso (nuFixedScalarExtensionComparisonMap X φ) := by
  have := pbcComparisonReductionMap_isIso X φ
  rw [pbcComparisonReductionMap, ← Iso.symm_hom,
    ← comparisonRestrictScalarsIso_eq_pbcDerivedComparisonRestrict_symm] at this
  exact this

/-- The canonical comparison isomorphism used by the finite reduction maps.
Source: Stacks 09B1 and 0F63 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
noncomputable def nuFixedScalarExtensionComparison (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
      CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
        (Scheme.ProEt.topology X) φ ≅
    CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
      X.smallEtaleTopology φ ⋙
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory := by
  letI := nuFixedScalarExtensionComparisonMap_isIso X φ
  exact asIso (nuFixedScalarExtensionComparisonMap X φ)

/-- The constant-section homomorphisms commute with the composite coefficient maps of the
finite coefficient system. -/
theorem constantSections_comp_coefficientMap (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    constantSections X (Etale.FiniteProperQuotient.Ring l E m) ≫
        WeilConjectures.SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
          (coefficients l E X) (transitions l E X) h =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E h)) ≫
        constantSections X (Etale.FiniteProperQuotient.Ring l E n) := by
  induction m, h using Nat.le_induction with
  | base =>
    have hid : WeilConjectures.SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) (le_refl n) = 𝟙 (coefficients l E X n) :=
      (WeilConjectures.SemilinearSections.rings (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X)).map_id (op n)
    rw [hid, Category.comp_id, Etale.FiniteProperQuotient.quotient_refl,
      CommRingCat.ofHom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  | succ m hnm ih =>
    have hsplit : WeilConjectures.SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) (hnm.trans (Nat.le_add_right m 1)) =
        transitions l E X m ≫
          WeilConjectures.SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
            (coefficients l E X) (transitions l E X) hnm := by
      rw [← Functor.ofOpSequence_map_homOfLE_succ (transitions l E X) m]
      exact (WeilConjectures.SemilinearSections.rings (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X)).map_comp
          (homOfLE (Nat.le_add_right m 1)).op (homOfLE hnm).op
    rw [hsplit, transitions, ← Category.assoc, constantSections_comp_sectionMap,
      Category.assoc, ih, ← Category.assoc, ← Functor.map_comp, ← CommRingCat.ofHom_comp,
      Etale.FiniteProperQuotient.quotient_comp_quotient]

/-- The constant-ring sheafification unit commutes with the constant-sheaf map of a ring
homomorphism, after forgetting commutativity. -/
theorem constantCommuteCompose_inv_toSheafify_naturality (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (q : A →+* B) (U : X.ProEtᵒᵖ) (a : A) :
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom q))).hom.app U
        (((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of A)).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a)) =
      ((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of B)).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B))).app U (q a)) := by
  have h1 := congrArg (fun g ↦ g.hom.app U ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a))
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.naturality (CommRingCat.ofHom q))
  have h2 := congrArg (fun g ↦ g.app U a)
    (toSheafify_naturality (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom q)))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h1 h2
  exact h1.symm.trans (congrArg (fun y ↦ ConcreteCategory.hom
    (((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of B)).hom.app U) y)
    h2.symm)

/-- A semilinear map of section-ring module sheaves, over a ring map compatible with the
constant sections, as a map of fixed-coefficient module sheaves at a single object. -/
noncomputable def finiteUnrealizationHomApp (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] (q : A →+* B)
    {N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A)}
    {N' : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X B)}
    (φ : sectionRing X A ⟶ sectionRing X B)
    (hφ : constantSections X A ≫ φ =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom q) ≫ constantSections X B)
    (f : N ⟶ (res.{u + 1, u, u + 1} φ).obj N') (U : X.ProEtᵒᵖ) :
    ((finiteUnrealization X A).obj N).obj.obj U ⟶
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) q).obj
        ((finiteUnrealization X B).obj N')).obj.obj U :=
  ModuleCat.ofHom (R := A) (X := ((finiteUnrealization X A).obj N).obj.obj U)
    (Y := ((Sheaf.restrictScalars (Scheme.ProEt.topology X) q).obj
        ((finiteUnrealization X B).obj N')).obj.obj U)
    { toFun := fun x ↦ f.val.app U x
      map_add' := fun x y ↦ map_add _ x y
      map_smul' := fun a x ↦ by
        have h3 := congrArg (fun g ↦ g.hom.app U
          (((constantCommuteCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of A)).hom.app U
            ((toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a))) hφ
        simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
          ConcreteCategory.comp_apply] at h3
        refine ((f.val.app U).hom.map_smul _ x).trans ?_
        exact congrArg (fun r : (WeilConjectures.SemilinearSections.ring
            (Scheme.ProEt.topology X) (sectionRing X B)).obj.obj U ↦
              r • @id (N'.val.obj U) ((f.val.app U).hom x))
          (h3.trans (congrArg (fun y ↦ ConcreteCategory.hom ((constantSections X B).hom.app U) y)
            (constantCommuteCompose_inv_toSheafify_naturality X q U a))) }

/-- A semilinear map of section-ring module sheaves, over a ring map compatible with the
constant sections, as a map of fixed-coefficient module sheaves. -/
noncomputable def finiteUnrealizationHom (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] (q : A →+* B)
    {N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A)}
    {N' : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X B)}
    (φ : sectionRing X A ⟶ sectionRing X B)
    (hφ : constantSections X A ≫ φ =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom q) ≫ constantSections X B)
    (f : N ⟶ (res.{u + 1, u, u + 1} φ).obj N') :
    (finiteUnrealization X A).obj N ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) q).obj
        ((finiteUnrealization X B).obj N') :=
  ⟨{ app := finiteUnrealizationHomApp X q φ hφ f
     naturality := fun _ _ g ↦ by
       ext x
       exact PresheafOfModules.naturality_apply f.val g x }⟩

/-- The fixed-coefficient map has the original underlying map of abelian sheaves. -/
theorem finiteUnrealizationHom_heq (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] (q : A →+* B)
    {N : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A)}
    {N' : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X B)}
    (φ : sectionRing X A ⟶ sectionRing X B)
    (hφ : constantSections X A ≫ φ =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom q) ≫ constantSections X B)
    (f : N ⟶ (res.{u + 1, u, u + 1} φ).obj N') :
    HEq ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map
          (finiteUnrealizationHom X q φ hφ f))
      ((SheafOfModules.toSheaf (WeilConjectures.SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (sectionRing X A))).map f) :=
  heq_of_eq (by
    ext U x
    rfl)

/-- The fixed-coefficient presentation of semilinear maps is natural. -/
theorem finiteUnrealizationHom_naturality (X : Scheme.{u}) {A B : Type (u + 1)} [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [CommRing B] [Finite B]
    [TopologicalSpace B] [DiscreteTopology B] (q : A →+* B)
    {N₁ N₂ : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X A)}
    {N₁' N₂' : WeilConjectures.SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (sectionRing X B)}
    (φ : sectionRing X A ⟶ sectionRing X B)
    (hφ : constantSections X A ≫ φ =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom q) ≫ constantSections X B)
    (f₁ : N₁ ⟶ (res.{u + 1, u, u + 1} φ).obj N₁') (f₂ : N₂ ⟶ (res.{u + 1, u, u + 1} φ).obj N₂')
    (g : N₁ ⟶ N₂) (g' : N₁' ⟶ N₂') (hg : g ≫ f₂ = f₁ ≫ (res.{u + 1, u, u + 1} φ).map g') :
    (finiteUnrealization X A).map g ≫ finiteUnrealizationHom X q φ hφ f₂ =
      finiteUnrealizationHom X q φ hφ f₁ ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) q).map
          ((finiteUnrealization X B).map g') := by
  ext U x
  exact congrArg (fun k ↦ k.val.app U x) hg

/-- The fixed-coefficient presentation of the horizontal transition of module systems. -/
noncomputable def fixedTransitionMap (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) m ⋙
      finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E m) ⟶
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) n ⋙
      finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n)) ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology X)
        (Etale.FiniteProperQuotient.quotient l E h) where
  app M := finiteUnrealizationHom X (Etale.FiniteProperQuotient.quotient l E h)
    (WeilConjectures.SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) h)
    (constantSections_comp_coefficientMap l E X h)
    ((transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) h).app M)
  naturality _ _ g := finiteUnrealizationHom_naturality X
    (Etale.FiniteProperQuotient.quotient l E h)
    (WeilConjectures.SemilinearSections.coefficientMap (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) h)
    (constantSections_comp_coefficientMap l E X h) _ _
    ((evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) m).map g)
    ((evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) n).map g)
    ((transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) h).naturality g)

/-- The fixed coefficient transition is the original horizontal additive map.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation).

Proof: evaluate a module system at m and n. Its horizontal map is linear over
A_m through the original quotient A_m to A_n. The constant-section maps commute
with continuous postcomposition. Consequently forgetting the two constant-ring
presentations turns this into precisely a map of fixed A_m-module sheaves.
The naturality square is the square already present in the module system.
Conversely the faithful forgetful functor to additive sheaves determines every
component and hence the natural transformation uniquely. No flatness is used.
-/
theorem fixedTransition_existsUnique (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    ∃! δ : fixedEvaluation l E X m ⟶ fixedEvaluation l E X n ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology X)
          (Etale.FiniteProperQuotient.quotient l E h),
      ∀ M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (coefficients l E X) (transitions l E X),
        HEq ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E m))
            AddCommGrpCat.{u + 1})).map (δ.app M))
          ((SheafOfModules.toSheaf (ring.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (coefficients l E X m))).map
              ((transition.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
                (coefficients l E X) (transitions l E X) h).app M)) := by
  refine ⟨fixedTransitionMap l E X h, fun M ↦ finiteUnrealizationHom_heq X _ _ _ _,
    fun δ' hδ' ↦ ?_⟩
  ext M : 2
  apply (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (Etale.FiniteProperQuotient.Ring l E m))
      AddCommGrpCat.{u + 1})).map_injective
  exact eq_of_heq ((hδ' M).trans (finiteUnrealizationHom_heq X _ _ _ _).symm)

/-- The uniquely normalized fixed-coefficient horizontal map.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedTransition (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  (fixedTransition_existsUnique l E X h).exists.choose

/-- Derived descent of the original horizontal map, including the localization compositors.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedDerivedTransition (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    fixedDerivedEvaluation l E X m ⟶ fixedDerivedEvaluation l E X n ⋙
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
        (Etale.FiniteProperQuotient.quotient l E h) :=
  (Functor.mapDerivedCategoryCompIso
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) m)
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E m))).inv ≫
  Functor.mapDerivedCategoryNatTrans (fixedTransition l E X h) ≫
  (Functor.mapDerivedCategoryCompIso
    (fixedEvaluation l E X n)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h))).hom ≫
  Functor.whiskerRight (Functor.mapDerivedCategoryCompIso
    (evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X) n)
    (finiteUnrealization X (Etale.FiniteProperQuotient.Ring l E n))).hom
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h))

/-- Scalar-adjunction transpose of that map: the actual derived reduction of a system.
Source: Zheng 4.1 (blueprint: def-sfb-finite-coefficient-system-evaluation). -/
def fixedReduction (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : DS.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
      (coefficients l E X) (transitions l E X)) :
    (CategoryTheory.Sheaf.fixedCoefficientDerivedScalarExtension
      (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h)).obj
        ((fixedDerivedEvaluation l E X m).obj M) ⟶
      (fixedDerivedEvaluation l E X n).obj M :=
  letI := CategoryTheory.Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint
    (Scheme.ProEt.topology X) (Etale.FiniteProperQuotient.quotient l E h)
  ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
      (Etale.FiniteProperQuotient.quotient l E h))).homEquiv _ _).symm
    ((fixedDerivedTransition l E X h).app M)

end AlgebraicGeometry.ProEtale.CoherentReduction
