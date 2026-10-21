/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.SixFunctors.OpenTensorNormalization

/-!
# Tensor-action and open-counit identities for finite-level projection maps

Source: blueprint sec-smooth-purity, lem-pur-projection-purity-agreement, expanded Step 6;
Stacks Project Tags 0B56, 0E8I and 0GL1
(blueprint: lem-pur-finite-projection-action-laws).

The eight statements give the proper, open, open-counit and chosen-compactification
identities on each of the pro-etale and ordinary etale sites. All projection maps are
actual canonical maps, with no invertibility, boundedness or constructibility assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the lifted positive-level quotient used in the projection identities.
Source: the finite coefficient convention and coefficient-extension finiteness
(blueprint: lem-pur-finite-projection-action-laws). -/
noncomputable instance projectionAction_coefficientFinite (P : PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  @Finite.of_equiv P.Coefficient P.Ring
    (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos)
    Equiv.ulift.symm

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

/-- The canonical reassociation of the derived tensor bifunctor, exposed before
specializing the coefficient category to avoid comparing two monoidal instance terms.
Source: Stacks Tag 0FPT, reassociation on total tensors
(blueprint: lem-pur-finite-projection-action-laws). -/
noncomputable def projectionActionAssociator
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (K M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    ((derivedTensor B X).obj (((derivedTensor B X).obj K).obj M)).obj N ≅
      ((derivedTensor B X).obj K).obj (((derivedTensor B X).obj M).obj N) :=
  α_ K M N

end AlgebraicGeometry.ProEtale


namespace AlgebraicGeometry.ProEtale


/-- Proper projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_proper
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsProper f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y (R((f)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      R((f)_*[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} P.Coefficient) f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  sorry


/-- Open projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_open
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y (D((f)_!open[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        M).app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      M).app N₁)).app N₂ ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  sorry


/-- Chosen-compactification projection tensor action, with reassociation and the canonical pullback
  tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_compactification
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj M) N₁
      N₂).hom ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (projectionActionAssociator (ModuleCat.{u + 1} P.Coefficient) X M
            (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app N₁)).app N₂ ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app (((derivedTensor
        (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  sorry


/-- Open-counit tensor compatibility, using the mixed exact/derived restriction
comparison to display the canonical identification of exact inverse image with Lf*.
Source: blueprint expanded Step 6, Stacks Tags 0E8I and 0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: Cancel the invertible open tensor map. Transpose through the open adjunction.
The left side transposes to the inverse restriction/tensor comparison. The inverse
open tensor normalization makes the right transpose the same comparison followed
by restriction of the counit tensor identity and the unit tensor identity. The
triangle identity cancels those last two maps. Injectivity of the adjunction
bijection gives equality; recompose with the open tensor isomorphism. The same
argument on each site uses its exact degreewise unit and counit, for unbounded
complexes, without assuming that any proper projection map is invertible. -/
theorem finiteProjectionAction_open_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (F N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient))) :
    (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      (D((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj F)).app N) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          F).app N) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        f).counit.app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj F).obj N) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      f).counit.app F)).app N := by
  sorry

end AlgebraicGeometry.ProEtale


namespace AlgebraicGeometry.Etale


/-- Proper projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_proper
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsProper f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) Y (R((f)_*[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      R((f)_*[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) X M (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} P.Coefficient) f).app M).app N₁)).app N₂ ≫
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} P.Coefficient) f).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  sorry


/-- Open projection tensor action, with reassociation and the canonical pullback tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_open
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) Y (D((f)_!open[(ModuleCat.{u + 1}
      P.Coefficient)]).obj M) N₁ N₂).hom ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        M).app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) X M (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      M).app N₁)).app N₂ ≫
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  sorry


/-- Chosen-compactification projection tensor action, with reassociation and the canonical pullback
  tensor
comparison written explicitly. Source: blueprint expanded Step 6, Stacks 0B56/0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: First normalize pullback/tensor comparisons on K-flat representatives; both
three-factor comparisons are total-tensor reassociation, with no permutation signs.
The K-flat localization equivalence descends these equalities. For proper projection,
transpose through the pullback/direct-image adjunction: the counit composite is
counit tensor identity. The iterated map and the single map both transpose to counit
tensor two identities, by naturality and the triangle identity. For open projection,
transpose the inverse maps through extension by zero and exact restriction. Their
transposes are the open unit tensor two identities, by the canonical open tensor
normalization. Injectivity of the adjunction bijection, followed by inversion, proves
the open identity. Finally expand the compactification map as proper projection
followed by proper image of the open projection. Naturality moves the first open
map across the second proper projection; the preceding two identities combine the
two factors. Pullback composition identifies the composite with the pullback of f.
On the ordinary etale site the same calculation uses its own exact inverse image,
open adjunction and K-flat total tensor; no comparison of sites is used. -/
theorem finiteProjectionAction_compactification
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).obj M) N₁
      N₂).hom ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app M).app
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj N₁).obj N₂)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
        (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj M).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) f N₁ N₂).hom ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) X M (L((f)^*[(ModuleCat.{u + 1}
            P.Coefficient)]).obj N₁) (L((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj N₂)).inv) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map (((projectionMapOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).app M).app N₁)).app N₂ ≫
      (((projectionMapOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).app (((derivedTensor
        (ModuleCat.{u + 1} P.Coefficient) X).obj M).obj (L((f)^*[(ModuleCat.{u + 1}
        P.Coefficient)]).obj N₁))).app N₂) := by
  sorry


/-- Open-counit tensor compatibility, using the mixed exact/derived restriction
comparison to display the canonical identification of exact inverse image with Lf*.
Source: blueprint expanded Step 6, Stacks Tags 0E8I and 0GL1
(blueprint: lem-pur-finite-projection-action-laws).
Proof: Cancel the invertible open tensor map. Transpose through the open adjunction.
The left side transposes to the inverse restriction/tensor comparison. The inverse
open tensor normalization makes the right transpose the same comparison followed
by restriction of the counit tensor identity and the unit tensor identity. The
triangle identity cancels those last two maps. Injectivity of the adjunction
bijection gives equality; recompose with the open tensor isomorphism. The same
argument on each site uses its exact degreewise unit and counit, for unbounded
complexes, without assuming that any proper projection map is invertible. -/
theorem finiteProjectionAction_open_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
  [Y.Over (Spec (CommRingCat.of P.field.k))]
  [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of P.field.k))] [IsOpenImmersion f]
    (F N : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
      (D((f)^*[(ModuleCat.{u + 1} P.Coefficient)]).obj F)).app N) ≫
      D((f)_!open[(ModuleCat.{u + 1} P.Coefficient)]).map
        (((mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          F).app N) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        f).counit.app (((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).obj F).obj N) =
    ((derivedTensor (ModuleCat.{u + 1} P.Coefficient) Y).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      f).counit.app F)).app N := by
  sorry

end AlgebraicGeometry.Etale
