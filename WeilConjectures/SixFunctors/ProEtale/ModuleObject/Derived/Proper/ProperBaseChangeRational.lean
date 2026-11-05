/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalExchange

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-!
# Proper direct image with rational condensed coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.md, clauses 1--3
(blueprint: det-thm-sfb-proper-base-change-rational).

The three coefficient comparisons are the existing derived push mates. Bounded
constructibility is the recorded ambient internal-module predicate. Base change uses the
recorded conditional restriction with its preservation proof supplied by the existing
finiteness-coefficient interface. Projection uses the existing canonical module-object mate.
The rational cases are expressed by equality of bundled coefficient ring objects.
This fixes the ring operations as well as the underlying sheaf.

## Main statements

* `isIso_rationalizationPushHom_boundedBelow`: localization commutes with proper pushforward.
* `isIso_finiteCoefficientPushHom_boundedBelow` and
  `isIso_algClCoefficientPushHom_boundedBelow`: the other two coefficient comparisons.
* `properPushforward_boundedConstructible_rational`: preservation of bounded constructibility.
* `isIso_properBaseChange_boundedConstructible_rational`: the specified exchange components.

The helper `rationalCoefficientPushforwardPreservation` supplies the existing preservation
proof by the displayed ring equality; it introduces no preservation assumption.

For compile time the module is split: clauses 1--2 are in
`Derived.Proper.ProperBaseChangeRationalPushforward`,
proper base change is in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalExchange`,
and this module (projection formula) imports both publicly.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedPushSource derivedPushTarget derivedPushHom
  moduleObjectProjectionMap boundedConstructibleBaseChangeOfPreserves
  DerivedCategory HasDerivedCategory.standard CategoryTheory.Mod.monoidalCategory

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] rationalizationPushHom
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.mapDerivedCategory
set_option allowUnsafeReducibility true in
attribute [local irreducible] rationalCoefficientPushforwardPreservation
  rationalFinitenessPushforwardPreservation
  ContinuousMapRingObj.rationalFinitenessPushforwardPreservation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projection_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X))}
    {M M' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))}
    (eK : K ≅ K') (eM : M ≅ M')
    (h : IsIso (moduleObjectProjectionMap R f K M)) :
    IsIso (moduleObjectProjectionMap R f K' M') := by
  let π := (derivedUpperStarLowerStarAdjunction R f).rightAdjointProjectionMap
    (T_C := derivedTensor R X) (T_D := derivedTensor R Y)
    (leftDerivedUpperStarTensor R f)
  unfold moduleObjectProjectionMap moduleObjectProjectionData at h ⊢
  change IsIso ((π.app K).app M) at h
  change IsIso ((π.app K').app M')
  have hi := (NatTrans.isIso_app_iff_of_iso (π.app K) eM).mp h
  exact (NatTrans.isIso_app_iff_of_iso (NatTrans.flipApp π M') eK).mp hi

attribute [local irreducible] derivedTensor

private theorem isIso_of_square {C : Type*} [Category* C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ D) (d : D ⟶ E)
    [IsIso a] [IsIso b] [IsIso d] (h : a ≫ b = c ≫ d) : IsIso c := by
  have : IsIso (c ≫ d) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right c d

private theorem isIso_of_six_sides {C : Type*} [Category* C]
    {A B D E F G : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ G)
    (d : A ⟶ E) (e : E ⟶ F) (f : F ⟶ G)
    [IsIso a] [IsIso b] [IsIso d] [IsIso e] [IsIso f]
    (h : a ≫ b ≫ c = d ≫ e ≫ f) : IsIso c := by
  have hi : IsIso (a ≫ b ≫ c) := h.symm ▸ inferInstance
  have hj : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a (b ≫ c)
  exact IsIso.of_isIso_comp_left b c

private theorem push_iso
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} (adj₁ : E₁ ⊣ U₁)
    {E₂ : C ⥤ D} {U₂ : D ⥤ C} (adj₂ : E₂ ⊣ U₂)
    {F : A ⥤ C} {G : B ⥤ D} (e : G ⋙ U₂ ≅ U₁ ⋙ F)
    [IsIso adj₁.unit] [IsIso adj₂.counit] :
    IsIso (Adjunction.pushHomOfComapIso adj₁ adj₂ e) := by
  unfold Adjunction.pushHomOfComapIso
  dsimp [mateEquiv, TwoSquare.natTrans, TwoSquare.mk]
  infer_instance

-- Keep the bundled category and endpoints abstract after the generic comparison helpers.
attribute [local irreducible] moduleObjectProjectionData

private noncomputable def integerIso (ℓ : ℕ) [Fact ℓ.Prime]
    (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F) ≅
      Mon.mk (DerivedNakayama.integerRing ℓ (ULift.{u} F.val)) := by
  let eR := integerRingSheafIso.{u} ℓ ⟨F.val, F.property⟩
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom e.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom e.hom
      inv := Mon.ofHom e.inv
      hom_inv_id := Mon.Hom.ext e.hom_inv_id
      inv_hom_id := Mon.Hom.ext e.inv_hom_id }

attribute [local irreducible] integerIso

private theorem integer_predicate (ℓ : ℕ) [Fact ℓ.Prime]
    (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (Z : Scheme.{u}) [CompactSpace Z] [IsLocallyNoetherian Z] :
    ∀ K, boundedConstructible (condensedRingObj
        (DerivedNakayama.integerRing ℓ (ULift.{u} F.val)) Z) K →
      constantModelBoundedConstructible
        (DerivedNakayama.integerRing ℓ (ULift.{u} F.val)) Z K := by
  have hmod := comparison_transport (integerIso ℓ F) Z
    (adicConstructibilityPredicateComparison ℓ Z
      (Profinite.padicIntegersRingObj ℓ F.val) (.integral F.val)).1
  intro K hK
  exact ⟨hK.1, fun n ↦ (hmod _).mp (hK.2 n)⟩

private theorem bounded_scalar
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) (Z : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj R Z))) (hK : boundedConstructible (condensedRingObj R Z) K) :
    boundedConstructible (condensedRingObj S Z)
      ((internalScalarExtension e.hom.hom Z).obj K) := by
  have ht := (NormedCoefficientRealization.transport_property e).1 Z
  obtain ⟨eT⟩ := ht.1
  have h := (ht.2.2.2.2.2.2.2.1 K).mpr hK
  let eK := eT.symm.app K
  refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso eK h.1, fun n ↦ ?_⟩
  exact constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso eK) (h.2 n)

private theorem finite_model (Z : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [TopologicalSpace.NoetherianSpace Z] (K : PadicAlgClConstructible Z l) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField l) (L : PadicSubfieldConstructible Z l E),
      Nonempty ((constructibleToPadicAlgCl Z l E).obj L ≅ K) :=
  constructibleCocone_essSurjObj Z l K

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.ProEtale.CondensedRing
