/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.EtaleSumStalks
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap
import Sheaf.Paper.EtaleSumTensorTotalization
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap

/-!
# Compatibility of the etale proper-support comparison

Source: Stacks Project, Tags 0F4L, 0F4Y, 0GKM, 03S6, 0F7L, 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility).

The auxiliary arrows transport the existing derived tensor comparison to the exact
inverse-image functor and take its projection mate under the existing sum adjunction.
The statement characterizes its comparisons by graph extension and the derived unit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Tensor comparison for termwise exact inverse image. This is the existing derived
pullback tensor comparison transported through `L(e^*) ≅ D(e^*)` in both variables.
Source: Stacks Project, Tags 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility). -/
noncomputable def etaleSupportExactUpperTensorIso
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (e : V ⟶ T) :
    (((Functor.whiskeringLeft₂ _).obj
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
        (derivedTensor (ModuleCat.{u + 1} A) V) ≅
      (Functor.postcompose₂.obj (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
        (derivedTensor (ModuleCat.{u + 1} A) T) :=
  (((Functor.whiskeringLeft₂ _).mapIso
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm).app
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).app
          (derivedTensor (ModuleCat.{u + 1} A) V) ≪≫
    (((Functor.whiskeringLeft₂ _).obj
      (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor).mapIso
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm).app
          (derivedTensor (ModuleCat.{u + 1} A) V) ≪≫
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) e).symm ≪≫
    (Functor.postcompose₂.mapIso
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e)).app
        (derivedTensor (ModuleCat.{u + 1} A) T)

/-- The reverse sum-extension projection arrow. It is the projection mate of the
sum/evaluation adjunction, using the canonical exact pullback tensor comparison above.
Its inverse is the map `(s,m) ⊗ k ↦ (s,m ⊗ s^*k)` of Tag 0GKF: transposing this rule
sends the summand generator to the unit inclusion tensored with the restricted section.
Thus the normalization below specifies a particular map, not an arbitrary isomorphism.
Source: Stacks Project, Tags 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility). -/
noncomputable def etaleSupportSumProjectionReverse
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (e : V ⟶ T) [Etale e] :
    (Functor.postcompose₂.obj
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory).obj
      ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
          (derivedTensor (ModuleCat.{u + 1} A) V)) ⟶
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        derivedTensor (ModuleCat.{u + 1} A) T :=
  ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).mapDerivedCategoryAdjunction).projectionMap
    (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
    (derivedTensor (ModuleCat.{u + 1} A) V) (derivedTensor (ModuleCat.{u + 1} A) T)
    (etaleSupportExactUpperTensorIso A e).hom

/-- The canonical proper-support comparison for separated etale finite-type maps
intertwines the specified exchange and projection transformations, on the entire unbounded
categories and for every compactification. The existential families are characterized by
sheaf and homotopy normalization equations; they are not unconstrained comparisons.
The final equation is the compatibility with proper-refinement identifications.

Source: Stacks Project, Tags 0F4L, 0F4Y, 0GKM, 03S6, 0F7L, 0GKF and 0GL5
(blueprint: lem-pur-etale-support-map-compatibility).

Proof:
1. In each compactification the graph of a lift is open and closed: it is open by
   etaleness and closed as a section of the separated proper morphism. Extend the input
   section by zero on its complement and sheafify the sum-presheaf map. The proper-support
   identification of lem-sfb-quasifinite-compact-support-exact makes this an isomorphism.
2. Apply this sheaf map degreewise, followed by the total-derived direct-image unit.
   On a K-injective resolution j_!P → I its transpose is represented by
   I composed with the sheaf counit after pullback of the graph map. Naturality of the
   counit and localization show that this is the descended evaluation map on all P.
3. The inverse of the specified conjugate sum-extension base-change map pulls a sheet
   section to its pulled-back sheet section. This is checked from its unit, ordinary
   exchange and counit, using the restriction/unit formulas. Inverse-image sections are
   only locally represented by source sections; no descent of all lifts is asserted.
   Graph extension commutes with pullback, giving equality of the two evaluation maps.
4. Transpose the exchange identity under r'^* ⊣ Rr'_*. The defining proper-exchange
   mate equation identifies its left side with the first evaluation map in step 3 and
   its right side with the second. The adjunction bijection proves the equality.
5. The sum projection sends (s,m) ⊗ k to (s,m ⊗ s^*k). Its inverse is the projection
   mate defined above, as follows by transposing the sum inclusion on each generator.
   Stalks identify it with distribution of tensor over sums, hence an isomorphism.
   Exact sum extension preserves flat and K-flat complexes by this same formula and
   commutes with sum totalization. Use flat K-flat representatives separately on the
   two sites and descend first in one variable and then in the other.
6. Evaluate on graph-supported tensor generators. Both evaluation composites are
   m ⊗ s^*k on the graph and zero off it. The sheaf axiom, linearity and sheafification
   give equality. On total tensor complexes the differentials have identical signs.
   K-flat tensor descent and localization give equality on the full derived categories.
7. Transpose the projection identity under r^* ⊣ Rr_*. The counit definition of the
   proper projection map gives the first evaluation composite in step 6 and naturality
   gives the second. The adjunction bijection and cancellation of the comparison prove
   the identity. The displayed L(e^*) to D(e^*) transport only records exactness.
8. The proper-refinement identity of lem-sfb-quasifinite-compact-support-exact follows
   from the same graph sections and derived units. Substitute it into the two identities
   to obtain their compatibility with each refinement, including nonfinite proper parts.
-/
theorem etaleSupportMapCompatibility
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ (a : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
        (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
        (c : Compactification e),
        etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⟶
          openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
            lowerStar (ModuleCat.{u + 1} A) c.g),
      ∃ (n : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
          (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
          (c : Compactification e),
          rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
            (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory),
        ∃ (p : ∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e],
            (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
                derivedTensor (ModuleCat.{u + 1} A) T ≅
              (Functor.postcompose₂.obj
                (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory).obj
                ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
                  (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
                    (derivedTensor (ModuleCat.{u + 1} A) V))),
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c : Compactification e),
            IsIso (a e c) ∧
              (∀ M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
                (a e c).app M ≫ (compactificationSheafToDirectImage A c).app M =
                  etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) ∧
              (∀ P : HomotopyCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
                  (ComplexShape.up ℤ),
                (n e c).inv.app (DerivedCategory.Qh.obj P) =
                  compactSupportComparisonOnHomotopy A e c (a e c) P)) ∧
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e],
            (p e).inv = etaleSupportSumProjectionReverse A e) ∧
          (∀ {V T T' : Scheme.{u}}
            [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T] [IsLocallyNoetherian T'] [CompactSpace T']
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c : Compactification e) (g : T' ⟶ T),
            exactCompactSupportExchange A c g ≫
                Functor.whiskerLeft
                  (upperStar (ModuleCat.{u + 1} A) (pullback.snd g e)).mapDerivedCategory
                  (n (pullback.fst g e)
                    (c.ofIsPullback (IsPullback.of_hasPullback g e).flip)).hom =
              Functor.whiskerRight (n e c).hom
                  (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
                (exactEtaleSumExchange A e g).hom) ∧
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c : Compactification e)
            (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))),
            ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
                (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
                  (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
                    ((leftDerivedUpperStarIsoMapDerivedCategory
                      (ModuleCat.{u + 1} A) e).hom.app K)) ≫
                (n e c).hom.app (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
                  ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) =
              ((derivedTensor (ModuleCat.{u + 1} A) T).map ((n e c).hom.app M)).app K ≫
                ((p e).hom.app M).app K) ∧
          (∀ {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
            [IsLocallyNoetherian T] [CompactSpace T]
            (e : V ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
            (c d : Compactification e) (_r : c.Refinement d),
            (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫ (n e d).hom =
              (n e c).hom) := by
  sorry

end AlgebraicGeometry.Etale
