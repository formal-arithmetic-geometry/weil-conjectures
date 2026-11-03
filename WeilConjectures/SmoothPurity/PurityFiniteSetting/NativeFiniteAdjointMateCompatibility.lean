/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorFactors
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.Compactification.BaseChange
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison

/-! # Native finite reduction of the canonical exceptional mates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.proof.md, Step 2
(blueprint: lem-pur-finite-adjoint-mate-compatibility).

Tensor and composition are stated on the original intrinsic pro-etale objects.
Base change and arbitrary transposes use the canonical etale-origin coordinates
of def-pur-co-smoothness. Every bounded constructible finite-Tor pro-etale object
has an etale origin. The fully faithful comparison carries the displayed mates,
including their units and counits, to the constructible pro-etale mates. These
coordinate statements therefore quantify over exactly the original domain.

The arbitrary-morphism clause uses the finite etale adjunction directly. In
particular, it imposes no smoothness on that morphism and imports no legacy
FiniteExceptionalData construction to define its coefficient mate.

## Main statements

* `native_finite_adjoint_mate_tensor`: reduction of the tensor mate.
* `native_finite_adjoint_mate_composition`: reduction of exceptional composition.
* `native_finite_adjoint_mate_baseChange`: reduction of every extraordinary square.
* `native_finite_adjoint_mate_transpose`: reduction of every adjoint transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem transpose_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (adjA : F ⊣ G) (adjB : F' ⊣ G') {S : C ⥤ C'} {T : D ⥤ D'}
    (α : TwoSquare S F F' T) (M : C) (L : D) (a : F.obj M ⟶ L) :
    S.map (adjA.unit.app M ≫ G.map a) ≫ (mateEquiv adjA adjB α).app L =
      adjB.unit.app (S.obj M) ≫ G'.map (α.app M ≫ T.map a) := by
  have hn := (mateEquiv adjA adjB α).naturality a
  change S.map (G.map a) ≫ (mateEquiv adjA adjB α).app L =
    (mateEquiv adjA adjB α).app (F.obj M) ≫ G'.map (T.map a) at hn
  calc
    _ = S.map (adjA.unit.app M) ≫
        ((mateEquiv adjA adjB α).app (F.obj M) ≫ G'.map (T.map a)) := by
      rw [Functor.map_comp, Category.assoc, hn]
    _ = (S.map (adjA.unit.app M) ≫
        (mateEquiv adjA adjB α).app (F.obj M)) ≫ G'.map (T.map a) :=
      (Category.assoc _ _ _).symm
    _ = (adjB.unit.app (S.obj M) ≫ G'.map (α.app M)) ≫
        G'.map (T.map a) := by
      rw [unit_mateEquiv]
      rfl
    _ = _ := by rw [Category.assoc, ← Functor.map_comp]

variable (P : PurityFiniteSetting.{u}) (m : ℕ+) (hmn : (m : ℕ) ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

variable [Xsep : IsSeparated (X ↘ Spec (.of P.field.k))]
variable [Ysep : IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [fbase : f.IsOver (Spec (.of P.field.k))]

include Xsep Ysep fbase

/-- Reduction identifies the extraordinary comparison for every Cartesian square.
At K=A_Y, the canonical scalar-unit identification gives exactly the coefficient
object comparison of def-pur-co-smoothness.
Source: current blueprint reduction proof Step 2, arbitrary base-change mates
(blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: thm-cbc-finite-level-proetale makes compact-support exchange invertible.
The pullback compatibility of lem-fix-compact-support-coefficient-change gives
the coefficient cube for that exchange, hence for its inverse. Paste with the
counit-normalized exceptional coefficient squares. Taking mates gives the two
sides below, with the scalar/pullback isomorphisms in the displayed directions.
Injectivity of the mate correspondence proves equality. Specializing to the
coefficient unit and its ordinary pullback-unit comparison gives the final claim.
No condition on v beyond being a morphism in the standing setting is used. -/
theorem native_finite_adjoint_mate_baseChange {X' Y' : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    (u' : X' ⟶ X) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    [u'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [v.IsOver (Spec (.of P.field.k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (sq : IsPullback u' f' f v) (K : Etale.DerivedCategoryModule P.Coefficient Y)
    (hK : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Y K) :
    P.nativeFiniteAdjointMateBaseChangeClause m hmn f u' f' v sq K := by
  have _ := Xsep
  have _ := Ysep
  have _ := fbase
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of P.field.k))
  have := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  have := isNoetherian_of_locallyOfFiniteType (X' ↘ Spec (.of P.field.k))
  have := isNoetherian_of_locallyOfFiniteType (Y' ↘ Spec (.of P.field.k))
  have := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have := hasCompactification_of_finiteType_over_field P.field.k X' Y' f'
  have : HasInvertibleExponent P.Coefficient Y :=
    P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  let B := (P.finiteReductionSetting m m.property).Coefficient
  obtain ⟨a₀, b₀, ht⟩ := hK.2
  have hG :=
    Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    P.Coefficient f d a₀ b₀
    ⟨⟨hK.1, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht⟩, ht⟩
  have hM := hG.1.1.1.1
  have hSM := Etale.ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X _
    ⟨_, _, hG.2⟩
  let := Etale.isIso_rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  let := Etale.isIso_rightDerivedLowerShriekBaseChangeMap B sq
  let eA := asIso (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq)
  let eB := asIso (Etale.rightDerivedLowerShriekBaseChangeMap B sq)
  let a := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f
  let b := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f'
  let ae := Etale.rightDerivedUpperShriekAdjunction B f
  let be := Etale.rightDerivedUpperShriekAdjunction B f'
  let αU := Etale.ExceptionalCoefficients.chosenCompactSupportIso φ f
  let αV := Etale.ExceptionalCoefficients.chosenCompactSupportIso φ f'
  have hfwd := Etale.ExceptionalCoefficients.compact_scalar_exchange_left φ sq
    ⟨_, hM⟩ ⟨⟨_, hSM⟩, rfl⟩
  rw [← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ f,
    ← Etale.ExceptionalCoefficients.chosenCompactSupportIso_hom φ f'] at hfwd
  have hcube : Adjunction.coefficientPullbackSquare eA.inv eB.inv αU αV
      (Etale.scalarPullbackIso φ u').inv (Etale.scalarPullbackIso φ v).inv
        ((Etale.rightDerivedUpperShriek P.Coefficient f).obj K) := by
    unfold Adjunction.coefficientPullbackSquare
    change (Etale.upperStar (ModuleCat.{u + 1} B) v).leftDerivedFunctor.map
        (αU.hom.app _) ≫ eB.hom.app _ ≫
          (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
            ((Etale.scalarPullbackIso φ u').hom.app _) =
      (Etale.scalarPullbackIso φ v).hom.app _ ≫
        (Etale.scalarExtension φ Y').map (eA.hom.app _) ≫ αV.hom.app _ at hfwd
    have hi := IsIso.inv_eq_inv.mpr hfwd
    have hh := congrArg (fun z ↦ αV.hom.app
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').leftDerivedFunctor.obj
        ((Etale.rightDerivedUpperShriek P.Coefficient f).obj K)) ≫
      z ≫ (Etale.upperStar (ModuleCat.{u + 1} B) v).leftDerivedFunctor.map
        (αU.hom.app ((Etale.rightDerivedUpperShriek
          P.Coefficient f).obj K))) hi
    simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
      Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id] using hh.symm
  have hh := Adjunction.coefficient_exchange_of_counit_at a b ae be eA.inv eB.inv K
    ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app K)
    ((Etale.rightDerivedUpperShriekBaseChangeMap B sq).app
      ((Etale.scalarExtension φ Y).obj K))
    (mateEquiv_counit a b eA.inv K)
    (mateEquiv_counit ae be eB.inv ((Etale.scalarExtension φ Y).obj K))
    αU αV (Etale.scalarPullbackIso φ u').inv (Etale.scalarPullbackIso φ v).inv
    (Etale.ExceptionalCoefficients.mateMap φ f K)
    (Etale.ExceptionalCoefficients.mateMap φ f'
      ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj K))
    (Etale.ExceptionalCoefficients.mateMap_counit φ f K)
    (Etale.ExceptionalCoefficients.mateMap_counit φ f' _) hcube
  exact hh.symm

/-- Reduction preserves adjoint transposes for every separated finite-type f.
Source: current blueprint reduction proof Step 2, unit compatibility
(blueprint: lem-pur-finite-adjoint-mate-compatibility).
Proof: write the transpose as eta_A followed by G_A(a). Naturality of the
exceptional coefficient mate moves Q(G_A(a)) across that mate. The unit equation
of lem-coef-finite-exceptional identifies Q(eta_A), followed by the exceptional
mate and G_B(q), with eta_B. Compose with G_B(q inverse) and G_B(Q(a));
functoriality and the inverse equations for q give the displayed result. This is
also the unit formula for the mate of q inverse. The etale/pro-etale comparison
preserves both adjunctions on these finite-Tor constructible objects. There is
no smoothness hypothesis on f. -/
theorem native_finite_adjoint_mate_transpose
    (M : Etale.DerivedCategoryModule P.Coefficient X)
    (hM : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient X M)
    (L : Etale.DerivedCategoryModule P.Coefficient Y)
    (hL : Etale.DerivedCategory.boundedConstructibleFiniteTor P.Coefficient Y L) :
    P.nativeFiniteAdjointMateTransposeClause m hmn f M L := by
  have _ := Xsep
  have _ := Ysep
  have _ := fbase
  have _ := hM
  have _ := hL
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  let φ := RingHom.ulift.{u + 1, u + 1} (P.finiteReductionRingHom m m.property hmn)
  let α := Etale.ExceptionalCoefficients.compactSupportIso φ
    (HasCompactification.compactification f)
  let adjA := Etale.rightDerivedUpperShriekAdjunction P.Coefficient f
  let adjB := Etale.rightDerivedUpperShriekAdjunction
    (P.finiteReductionSetting m m.property).Coefficient f
  change ∀ a : (Etale.rightDerivedLowerShriek
    (ModuleCat.{u + 1} P.Coefficient) f).obj M ⟶ L, _
  intro a
  rw [Etale.ExceptionalCoefficients.mateMap_eq φ f L,
    Etale.ExceptionalCoefficients.comparisonInverse_eq φ
      (HasCompactification.compactification f) M]
  exact transpose_mate adjA adjB (TwoSquare.mk _ _ _ _ α.inv) M L a

end WeilConjectures.PurityFiniteSetting
