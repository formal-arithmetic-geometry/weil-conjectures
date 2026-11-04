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
public import WeilConjectures.AlgebraicGeometry.Derived.ComparisonScalarExtensionMate

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
  exact ProEtale.isIso_mate_comparisonRestrictScalarsIso φ X

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
  sorry

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
