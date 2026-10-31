/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceResidueRestriction
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier

/-! # Native Cartier realization data

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-trace.proof.md, clause (1), and
sk-prop-diagonal-tower-limit.proof.md, clauses (1)--(3).
(blueprint: def-pur-native-cartier-realization-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.NativeCartier

/-- The pulled-back finite-subextension-valued condensed coefficient ring's module
category. Source: qlbar-colimit-x, pulled-back coefficients
(blueprint: def-pur-native-cartier-realization-data). -/
abbrev Modules (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) T)

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  (T₀ : Scheme.{u}) [T₀.Over (Spec (CommRingCat.of k₀))]

/-- Geometric Galois Frobenius on the actual condensed module category.
Source: native Weil framework, Frobenius paragraph
(blueprint: def-pur-native-cartier-realization-data). -/
abbrev frobenius :
    Modules ℓ (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⥤
      Modules ℓ (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
    (T₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom

/-- Native equivariant module sheaves, before passage to the derived category.
Source: native Weil framework (blueprint: def-pur-native-cartier-realization-data). -/
abbrev WeilModules := IsoAlgebra (frobenius k₀ ℓ T₀)

/-- The native equivariant category is Grothendieck abelian, by the standard
IsoAlgebra instance for an exact autoequivalence. Source: native framework
(blueprint: def-pur-native-cartier-realization-data). -/
instance weilModulesGrothendieck : IsGrothendieckAbelian.{u + 1} (WeilModules k₀ ℓ T₀) :=
  IsoAlgebra.isGrothendieckAbelian _

/-- Canonical descent equivariance of geometric-fibre inverse image. Its components
come from F followed by the projection being the projection, so no invariant derived
arrow is selected. Source: trace proof (1), descent of Cartier data
(blueprint: def-pur-native-cartier-realization-data). -/
def descentStructure :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ⋙ frobenius k₀ ℓ T₀ ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj.{u} ℓ)
    (T₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
    (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).symm ≪≫
  CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj.{u} ℓ)
    (T₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius_hom_comp_geometricFiberProj

/-- Exact geometric-fibre descent, defined on module sheaves and their actual maps.
Source: trace proof (1), descent of the Cartier extension
(blueprint: def-pur-native-cartier-realization-data). -/
def descent : Modules ℓ T₀ ⥤ WeilModules k₀ ℓ T₀ where
  obj M := IsoAlgebra.mk
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
      (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).obj M)
    ((descentStructure k₀ ℓ T₀).app M)
  map f := ObjectProperty.homMk
    { f := (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).map f
      h := (descentStructure k₀ ℓ T₀).hom.naturality f }

/-- Descent retains addition because its underlying inverse image does.
Source: trace proof (1) (blueprint: def-pur-native-cartier-realization-data). -/
instance descentAdditive : (descent k₀ ℓ T₀).Additive where
  map_add := by
    intros
    apply (IsoAlgebra.forget _).map_injective
    exact (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
      (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).map_add

/-- Exactness of descent on kernels, reflected by equivariant forgetting.
Source: trace proof (1) (blueprint: def-pur-native-cartier-realization-data). -/
instance descentFiniteLimits : PreservesFiniteLimits (descent k₀ ℓ T₀) := by
  have : PreservesFiniteLimits (descent k₀ ℓ T₀ ⋙ IsoAlgebra.forget _) :=
    inferInstanceAs (PreservesFiniteLimits
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

/-- Exactness of descent on cokernels, reflected by equivariant forgetting.
Source: trace proof (1) (blueprint: def-pur-native-cartier-realization-data). -/
instance descentFiniteColimits : PreservesFiniteColimits (descent k₀ ℓ T₀) := by
  have : PreservesFiniteColimits (descent k₀ ℓ T₀ ⋙ IsoAlgebra.forget _) :=
    inferInstanceAs (PreservesFiniteColimits
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (T₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

/-- The canonical native coefficient unit, descended before localization.
Source: trace proof (1) (blueprint: def-pur-native-cartier-realization-data). -/
abbrev unit := (descent k₀ ℓ T₀).obj
  (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) T₀))

/-- The root-limit Tate line with its canonical descent structure. The existing
spQbarTwist first takes the inverse limit of roots, inverts ell, and takes the
finite-subextension colimit. Source: Tate twists and trace proof (1)
(blueprint: def-pur-native-cartier-realization-data). -/
abbrev tate := (descent k₀ ℓ T₀).obj (spQbarTwist T₀ ℓ)

end AlgebraicGeometry.ProEtale.NativeCartier

namespace AlgebraicGeometry.ProEtale.NativeCartier
open SpTowerClasses DiagonalCoefficients

/-- The standard localization of constant integral module sheaves, at the same
size as the published strict-system localization. Source: limit proof (1)
(blueprint: def-pur-native-cartier-realization-data). -/
instance constantModulesDerived (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (DiagonalMod ℓ X) := HasDerivedCategory.standard _

/-- The standard localization of strict constant-integral towers.
Source: limit proof (1) (blueprint: def-pur-native-cartier-realization-data). -/
instance constantSystemsDerived (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (DiagonalSystems ℓ X) := HasDerivedCategory.standard _

/-- The base-field finite extension used to present the cyclic coefficient tower.
Source: trace proof (1), E = Q_l (blueprint: def-pur-native-cartier-realization-data). -/
abbrev primeField (ℓ : ℕ) [Fact ℓ.Prime] := ULift.{u} (Padic ℓ)

/-- Normalized integral reduction into the cyclic coefficient tower. The second
coefficient system is identical, so the unused scalar factor is the identity.
Source: trace proof (1), strict Cartier construction
(blueprint: def-pur-native-cartier-realization-data). -/
abbrev IntegralData (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :=
  ChernData ℓ X (Arings ℓ (primeField ℓ) X) (Arings ℓ (primeField ℓ) X) (𝟙 _)

/-- Both normalizations are those of the published derived-extension adjunction:
insertion of one and the positive shifted Kummer boundary.
Source: trace proof (1), strict system normalization
(blueprint: def-pur-native-cartier-realization-data). -/
def IntegralData.Normalized {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
    (c : IntegralData ℓ X) : Prop :=
  c.reduction.model.sourceNormalization c.unitIso
      (integerGenerator X (Arings ℓ (primeField ℓ) X) c.reduction.forget) ∧
  c.reduction.model.targetNormalization
    (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
    c.kummer.exact c.rootIso c.rootForget

/-- One coherent Cartier arrow, obtained by one simultaneous derived reduction of
the positive Picard extension. Source: trace proof (1)
(blueprint: def-pur-native-cartier-realization-data). -/
def IntegralData.class {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
    (c : IntegralData ℓ X) (L : X.Pic) :=
  c.unitIso.inv ≫ c.reduction.derived.map (lineBundleClass X L) ≫ c.rootIso.hom

/-- The common strict system, its positive root normalization, its total derived
limit, and the unique completed-coefficient lift. No class is inferred from its
separate finite evaluations. Source: trace proof (1) and limit proof (1)--(3)
(blueprint: def-pur-native-cartier-realization-data). -/
structure IntegralRoute (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (L : X.Pic) where
  chern : IntegralData ℓ X
  normalized : chern.Normalized
  restriction : DiagonalTrace.Restriction ℓ (primeField ℓ) X
  underlying : restriction.F ⋙
      (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod ℓ X) (DiagonalAb X)).obj
        (diagonalForget ℓ X) ≅ chern.reduction.forget.F
  underlying_normalization : ∀ (M : Systems X (Arings ℓ (primeField ℓ) X))
      (n : ℕ) (U : X.ProEtᵒᵖ),
    HEq (((underlying.hom.app M).app (op n)).hom.app U)
      (𝟙 (AddCommGrpCat.of (M.val.obj (op (n, U.unop)))))
  rlim : DiagonalRlim (DiagonalMod ℓ X)
  source : (diagonalCompletedRestriction ℓ X).obj
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ))) ≅
    limit (restriction.F.obj (coefficient X (Arings ℓ (primeField ℓ) X)))
  source_normalization : ∀ (n : ℕ) (U : X.ProEtᵒᵖ),
    HEq (((source.hom ≫ limit.π _ (op n)).hom.app U)
        (1 : (Scheme.purTwistZlCompletion X ℓ).obj.obj U))
      (1 : ((Arings ℓ (primeField ℓ) X).obj (op n)).obj.obj U)
  root : (diagonalCompletedRestriction ℓ X).obj (Scheme.purTwistZlModule X ℓ) ≅
    limit (restriction.F.obj chern.rootModule)
  root_normalization :
    HEq ((diagonalForget ℓ X).map root.hom ≫
      (diagonalRootLimitComparison ℓ X (restriction.F.obj chern.rootModule)
        (underlying.app chern.rootModule ≪≫ chern.rootForget)).hom)
      (𝟙 (Scheme.purTwistZlOne X ℓ))

/-- Canonical source comparison from the ordinary limit and the universal
right-derived unit. Source: limit proof (1)--(3)
(blueprint: def-pur-native-cartier-realization-data). -/
def IntegralRoute.sourceMap {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} {L : X.Pic}
    (c : IntegralRoute ℓ X L) :=
  diagonalSingleLimitComparison (diagonalCompletedRestriction ℓ X) c.rlim _ _ _ c.source
    ((c.restriction.F.mapDerivedCategorySingleFunctor 0).app
      (coefficient X (Arings ℓ (primeField ℓ) X)))

/-- Canonical shifted target comparison, retaining the shift and the actual root
projections. Source: limit proof (1)--(3)
(blueprint: def-pur-native-cartier-realization-data). -/
def IntegralRoute.rootMap {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} {L : X.Pic}
    (c : IntegralRoute ℓ X L) :=
  diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction ℓ X) c.rlim _ _ _
    c.root
    ((c.restriction.F.mapDerivedCategory.commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((c.restriction.F.mapDerivedCategorySingleFunctor 0).app c.chern.rootModule))

/-- The equation fixing the completed lift in its coefficient-linear derived
category. Source: limit proof (3), full faithfulness on complete objects
(blueprint: def-pur-native-cartier-realization-data). -/
def IntegralRoute.Lifts {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} {L : X.Pic}
    (c : IntegralRoute ℓ X L)
    (g : (DerivedCategory.singleFunctor (DiagonalCompleted ℓ X) 0).obj
        (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ))) ⟶
      ((DerivedCategory.singleFunctor (DiagonalCompleted ℓ X) 0).obj
        (Scheme.purTwistZlModule X ℓ))⟦(2 : ℤ)⟧) : Prop :=
  IsIso c.sourceMap ∧ IsIso c.rootMap ∧
    (diagonalCompletedRestriction ℓ X).mapDerivedCategory.map g ≫ c.rootMap =
      c.sourceMap ≫ c.rlim.R.map
        (c.restriction.F.mapDerivedCategory.map (c.chern.class L))

/-- The positive Cartier line is the dual Cartier ideal, using the recorded
invertibility theorem. Source: divisor-line-bundle
(blueprint: def-pur-native-cartier-realization-data). -/
def divisorPic {X : Scheme.{u}} (J : X.IdealSheafData) (hJ : J.IsInvertible) : X.Pic :=
  @Scheme.Pic.ofIsInvertible X (Scheme.Modules.dual J.toModules)
    hJ.isInvertible_dual_toModules

end AlgebraicGeometry.ProEtale.NativeCartier

namespace AlgebraicGeometry.ProEtale.NativeCartier
open SpTowerClasses DiagonalCoefficients

/-- One scalar step, with the scalar adjoints fixing both endpoint maps.
Source: trace proof (1), inversion and coefficient extension
(blueprint: def-pur-native-cartier-realization-data). -/
structure ScalarStep
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    (M : DiagonalCoefficients.Modules Λ X) (N : DiagonalCoefficients.Modules Λ' X)
    (m : M.X ⟶ N.X) where
  source : Endpoint a (Mod.regular (condensedRingObj Λ X))
    (Mod.regular (condensedRingObj Λ' X)) (coefficientMap a X)
  target : Endpoint a M N m

/-- Apply an actual derived scalar extension to an arrow, using the normalized
unit and Tate endpoints. Source: trace proof (1)
(blueprint: def-pur-native-cartier-realization-data). -/
def ScalarStep.map
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    {a : Λ ⟶ Λ'} [IsMonHom a] {X : Scheme.{u}}
    {M : DiagonalCoefficients.Modules Λ X} {N : DiagonalCoefficients.Modules Λ' X}
    {m : M.X ⟶ N.X} (s : ScalarStep a M N m)
    (h : DiagonalCoefficients.unit Λ X ⟶
      ((DerivedCategory.singleFunctor (DiagonalCoefficients.Modules Λ X) 0).obj M)⟦(2 : ℤ)⟧) :=
  s.source.iso.inv ≫ (derivedScalars a X).map h ≫ s.target.shift

/-- A complete ordinary Cartier realization, retaining the strict system, its
unique coefficient-linear limit lift, the actual condensed coefficient realization,
and the normalized scalar steps. Source: trace proof (1), limit proof (1)--(3)
(blueprint: def-pur-native-cartier-realization-data). -/
structure OrdinaryRoute (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (L : X.Pic) where
  integral : IntegralRoute ℓ X L
  completed : (DerivedCategory.singleFunctor (DiagonalCompleted ℓ X) 0).obj
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X ℓ))) ⟶
    ((DerivedCategory.singleFunctor (DiagonalCompleted ℓ X) 0).obj
      (Scheme.purTwistZlModule X ℓ))⟦(2 : ℤ)⟧
  lifts : integral.Lifts completed
  unique : ∀ g, integral.Lifts g → g = completed
  realization : CompletedRealization ℓ X
  toIntegral : ScalarStep (integralMap ℓ (bottomField ℓ)) (zlLine ℓ X)
    (spIntegralTwist X ℓ (bottomField ℓ)) (integralLineMap ℓ (bottomField ℓ) X)
  toRational : ScalarStep (padicIntegersRingObjToContinuousMapRingObj ℓ (bottomField ℓ))
    (spIntegralTwist X ℓ (bottomField ℓ)) (spRationalTwist X ℓ (bottomField ℓ))
    (rationalLineMap ℓ (bottomField ℓ) X)
  toClosure : ScalarStep (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ (bottomField ℓ))
    (spRationalTwist X ℓ (bottomField ℓ)) (spQbarTwist X ℓ)
    (closureLineMap ℓ (bottomField ℓ) X)

/-- Realize the unique completed arrow over pulled-back condensed Z_l.
Source: limit proof (3) and trace proof (1)
(blueprint: def-pur-native-cartier-realization-data). -/
def OrdinaryRoute.integralClass {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} {L : X.Pic}
    (c : OrdinaryRoute ℓ X L) :
    DiagonalCoefficients.unit (Profinite.continuousMapRingObj.{u} ℤ_[ℓ]) X ⟶
      ((DerivedCategory.singleFunctor
        (DiagonalCoefficients.Modules (Profinite.continuousMapRingObj.{u} ℤ_[ℓ]) X) 0).obj
          (zlLine ℓ X))⟦(2 : ℤ)⟧ :=
  (DerivedCategory.singleFunctor _ 0).map c.realization.unitIso.inv ≫
    mapSingleArrow c.realization.F (2 : ℤ) c.completed ≫
    ((DerivedCategory.singleFunctor _ 0).map c.realization.lineIso.hom)⟦(2 : ℤ)⟧'

/-- The ordinary positive first Chern class is the whole strict-tower route,
followed by completion, inversion of ell, and extension to Qbar_l.
Source: trace proof (1) (blueprint: def-pur-native-cartier-realization-data). -/
def OrdinaryRoute.class {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} {L : X.Pic}
    (c : OrdinaryRoute ℓ X L) :
    DiagonalCoefficients.unit (Profinite.padicAlgClRingObj.{u} ℓ) X ⟶
      ((DerivedCategory.singleFunctor (Modules ℓ X) 0).obj (spQbarTwist X ℓ))⟦(2 : ℤ)⟧ :=
  c.toClosure.map (c.toRational.map (c.toIntegral.map c.integralClass))

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  (T₀ : Scheme.{u}) [T₀.Over (Spec (CommRingCat.of k₀))]

/-- The native arrow is computed by a functor defined on equivariant module
complexes before localization. Source: native refinement of trace proof (1)
(blueprint: def-pur-native-cartier-realization-data). -/
def nativeClass {L : T₀.Pic} (c : OrdinaryRoute ℓ T₀ L) :
    (DerivedCategory.singleFunctor (WeilModules k₀ ℓ T₀) 0).obj (unit k₀ ℓ T₀) ⟶
      ((DerivedCategory.singleFunctor (WeilModules k₀ ℓ T₀) 0).obj
        (tate k₀ ℓ T₀))⟦(2 : ℤ)⟧ :=
  mapSingleArrow (descent k₀ ℓ T₀) (2 : ℤ) c.class

end AlgebraicGeometry.ProEtale.NativeCartier

namespace AlgebraicGeometry.ProEtale.NativeCartier
open SpTowerClasses DiagonalCoefficients CategoryTheory.MonoidalCategory

/-- The prescribed pullback of the Qbar Tate line. Its underlying map is fixed
on every rational finite stage, and there by the integral root-limit map.
Source: cartesian coefficients and twists, integral/rational/Qbar paragraphs
(blueprint: def-pur-native-cartier-realization-data). -/
def IsTatePullback (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) f).obj
      (spQbarTwist Y ℓ) ≅ spQbarTwist X ℓ) : Prop :=
  ∃ ρ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).obj
        (spRationalTwist Y ℓ E).X ⟶ (spRationalTwist X ℓ E).X,
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)) ≫
        ρ E =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
        (spIntegralTwist Y ℓ E).X ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
        spIntegralComparison f ℓ E) ≫
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E)) ∧
    ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).map
          (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫
        (CondensedRing.upperStarForgetIso (Profinite.padicAlgClRingObj.{u} ℓ) f).hom.app
          (spQbarTwist Y ℓ) ≫ e.hom.hom =
      ρ E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  {X₀ Y₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))]
  [Y₀.Over (Spec (CommRingCat.of k₀))]
  (f : X₀ ⟶ Y₀) [f.IsOver (Spec (CommRingCat.of k₀))]

/-- The actual geometric-fibre map, retaining the over-base commutation proof.
Source: native framework (blueprint: def-pur-native-cartier-realization-data). -/
abbrev geometricMap :
    (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶
      (Y₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))

/-- The Frobenius exchange for inverse image, using only the geometric-fibre
commutative square and the canonical pullback compositor.
Source: native framework, inverse image
(blueprint: def-pur-native-cartier-realization-data). -/
def pullExchange :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) (geometricMap k₀ f) ⋙
      frobenius k₀ ℓ X₀ ≅
    frobenius k₀ ℓ Y₀ ⋙
      CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) (geometricMap k₀ f) :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj.{u} ℓ)
    (X₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
    (geometricMap k₀ f)).symm ≪≫
  CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj.{u} ℓ)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius f (comp_over f _)).symm ≪≫
  CondensedRing.upperStarComp (Profinite.padicAlgClRingObj.{u} ℓ) (geometricMap k₀ f)
    (Y₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom

/-- Native inverse image is defined on equivariant sheaves before localization.
Source: native framework (blueprint: def-pur-native-cartier-realization-data). -/
def pull : WeilModules k₀ ℓ Y₀ ⥤ WeilModules k₀ ℓ X₀ :=
  IsoAlgebra.mapOfNatIso (pullExchange k₀ ℓ f)

/-- Native inverse image is additive. Source: native framework
(blueprint: def-pur-native-cartier-realization-data). -/
instance pullAdditive : (pull k₀ ℓ f).Additive := IsoAlgebra.additive_mapOfNatIso _

/-- Native inverse image preserves kernels. Source: native framework
(blueprint: def-pur-native-cartier-realization-data). -/
instance pullLimits : PreservesFiniteLimits (pull k₀ ℓ f) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

/-- Native inverse image preserves cokernels. Source: native framework
(blueprint: def-pur-native-cartier-realization-data). -/
instance pullColimits : PreservesFiniteColimits (pull k₀ ℓ f) :=
  IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

/-- The prescribed ordinary pullback/descent comparison, before localization.
Source: trace proof (1), geometric base change
(blueprint: def-pur-native-cartier-realization-data). -/
def descentBaseChange :
    CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (Y₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj ⋙
      CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) (geometricMap k₀ f) ≅
    CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) f ⋙
      CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj.{u} ℓ) (geometricMap k₀ f)
    (Y₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).symm ≪≫
  CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj.{u} ℓ)
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberProj f (comp_over f _)) ≪≫
  CondensedRing.upperStarComp (Profinite.padicAlgClRingObj.{u} ℓ)
    (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj f

/-- Native pullback endpoints fixed by their actual underlying coefficient and
root maps. Faithfulness of equivariant forgetting makes these normalizations
unambiguous. Recording the endpoints directly avoids expanding the full native
functor compositor when a consumer only needs the two lines.
Source: trace proof (1), coefficient and Tate pullback
(blueprint: def-pur-native-cartier-realization-data). -/
structure PullbackEndpoints where
  coefficient : (pull k₀ ℓ f).obj (unit k₀ ℓ Y₀) ≅ unit k₀ ℓ X₀
  coefficient_normalization :
    HEq ((IsoAlgebra.forget (frobenius k₀ ℓ X₀)).map coefficient.hom)
      ((descentBaseChange k₀ ℓ f).hom.app
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y₀)) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
          (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).map
          (CondensedRing.upperStarObjRegularIso
            (Profinite.padicAlgClRingObj.{u} ℓ) f).hom)
  ordinaryTate : (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ) f).obj
    (spQbarTwist Y₀ ℓ) ≅ spQbarTwist X₀ ℓ
  roots : IsTatePullback ℓ f ordinaryTate
  line : (pull k₀ ℓ f).obj (tate k₀ ℓ Y₀) ≅ tate k₀ ℓ X₀
  line_normalization :
    HEq ((IsoAlgebra.forget (frobenius k₀ ℓ X₀)).map line.hom)
      ((descentBaseChange k₀ ℓ f).hom.app (spQbarTwist Y₀ ℓ) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
          (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).map ordinaryTate.hom)

end AlgebraicGeometry.ProEtale.NativeCartier

namespace AlgebraicGeometry.ProEtale.NativeCartier
open SpTowerClasses DiagonalCoefficients

/-- A scheme in the range of the native Cartier assertion. This is only an
indexing structure: all four properties are the literal scheme properties.
Source: trace proof (1) (blueprint: def-pur-native-cartier-realization-data). -/
structure Base (k₀ : Type u) [Field k₀] where
  scheme : Scheme.{u}
  [overBase : scheme.Over (Spec (CommRingCat.of k₀))]
  [qc : QuasiCompact (scheme ↘ Spec (CommRingCat.of k₀))]
  [qs : QuasiSeparated (scheme ↘ Spec (CommRingCat.of k₀))]
  [lft : LocallyOfFiniteType (scheme ↘ Spec (CommRingCat.of k₀))]

attribute [instance] Base.overBase Base.qc Base.qs Base.lft

set_option maxHeartbeats 800000 in
-- The derived endpoint presentations contain the large standard localization structures.
/-- The native Cartier construction as one family, including the geometric-fibre
ordinary normalization and all permitted pullback squares. The native arrow is
`nativeClass` of `route`, so is produced by exact descent on complexes, rather
than by choosing a lift of an invariant ordinary derived arrow. All comparison
maps are constrained by their actual root and base-change components.
Source: trace proof (1), Cartier and base-change paragraphs
(blueprint: def-pur-native-cartier-realization-data). -/
structure Construction (k₀ : Type u) [Field k₀] [Finite k₀]
    (ℓ : ℕ) [Fact ℓ.Prime] where
  route : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData) (hJ : J.IsInvertible),
    OrdinaryRoute ℓ X.scheme (divisorPic J hJ)
  geometricInvertible : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData)
    (_hJ : J.IsInvertible),
    (J.comap (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).IsInvertible
  geometricRoute : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData) (hJ : J.IsInvertible),
    OrdinaryRoute ℓ (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (divisorPic (J.comap (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
        (geometricInvertible X J hJ))
  forget : ∀ (X : Base k₀) (J : X.scheme.IdealSheafData) (hJ : J.IsInvertible),
    ∃ e : (CondensedRing.upperStar (Profinite.padicAlgClRingObj.{u} ℓ)
        (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).obj
        (spQbarTwist X.scheme ℓ) ≅
      spQbarTwist (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiber ℓ,
    IsTatePullback ℓ (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj e ∧
    HEq (mapSingleArrow (IsoAlgebra.forget (frobenius k₀ ℓ X.scheme)) (2 : ℤ)
        (nativeClass k₀ ℓ X.scheme (route X J hJ)))
      ((DerivedCategory.singleFunctor _ 0).map
          (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj.{u} ℓ)
            (X.scheme ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).hom ≫
        (geometricRoute X J hJ).class ≫
        ((DerivedCategory.singleFunctor _ 0).map e.inv)⟦(2 : ℤ)⟧')
  natural : ∀ (X Y : Base k₀) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (CommRingCat.of k₀))]
      (J : Y.scheme.IdealSheafData) (hJ : J.IsInvertible)
      (hJ' : (J.comap f).IsInvertible),
    ∃ e : PullbackEndpoints k₀ ℓ f,
    HEq (mapSingleArrow (pull k₀ ℓ f) (2 : ℤ)
        (nativeClass k₀ ℓ Y.scheme (route Y J hJ)))
      ((DerivedCategory.singleFunctor _ 0).map e.coefficient.hom ≫
        nativeClass k₀ ℓ X.scheme (route X (J.comap f) hJ') ≫
        ((DerivedCategory.singleFunctor _ 0).map e.line.inv)⟦(2 : ℤ)⟧')

end AlgebraicGeometry.ProEtale.NativeCartier
