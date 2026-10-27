/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.PerfectProjectionFormula
import all Sheaf.Paper.PerfectProjectionFormula
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Normalized quotient pullback composition

Source: Stacks Project, Tags 03D3, 03D8, 00WH and 0D6D; blueprint
lemma-weil-pbc-perfect-projection-formula, third proof paragraph
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).

We reuse the completed constant-quotient presentation and its uniquely
section-normalized module comparisons. The exponent represented by n is n+1.

## Main statements

* `ordinary_composition`: composition of the normalized module comparisons.
* `derived_composition`: the corresponding canonical derived composition.
* `transition_naturality` and `system_naturality`: both naturality assertions.
* `cartesian_square`: compatibility with the inverse ambient square comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PerfectProjection

namespace AlgebraicGeometry.Scheme.QuotientPullbackNormalization

private noncomputable local instance (priority := 20000) fixedAbelianSite
    (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} T

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The system map commutes with the adjacent quotient arrows after taking constants.
Source: Stacks 00WH and 099M
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: apply constantSheaf to the naturality square for φ at the adjacent arrow.
The two constant-sheaf quotient arrows are exactly the defining arrows of the
adicLisseRingSystem, so functoriality gives the displayed equality. -/
theorem systemSheafMap_naturality {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower)
    (T : Scheme.{u}) (n : ℕ) :
    (adicLisseRingSystem T d.ideal).map (homOfLE (Nat.le_succ n)).op ≫
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (φ.app (op n)) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (φ.app (op (n + 1))) ≫
        (adicLisseRingSystem T e.ideal).map (homOfLE (Nat.le_succ n)).op := by
  have hq (I : Ideal A) :
      reductionQuotientMap I (n + 1) n (Nat.le_succ n) =
        Ideal.Quotient.factorPowSucc I (n + 1) := by
    ext x
    rfl
  have hqe : reductionQuotientMap e.ideal (n + 1) n (Nat.le_succ n) =
      Ideal.Quotient.factorPowSucc e.ideal (n + 1) := by
    ext x
    rfl
  simpa only [adicLisseRingSystem, AdicCoefficientDatum.ringTower,
    Functor.ofOpSequence_map_homOfLE_succ, hq, hqe, ← Functor.map_comp] using
    congrArg ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map)
      (φ.naturality (homOfLE (Nat.le_succ n)).op)

/-- The completed map induced by a morphism of finite coefficient systems.
Source: Stacks 098T and 099M, inverse-limit functoriality
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
def systemRingMap {B : Type (u + 1)} [CommRing B] (e : AdicCoefficientDatum B)
    (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) : ring d T ⟶ ring e T :=
  limMap (NatTrans.ofOpSequence
    (fun n ↦ (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (φ.app (op n)))
    (systemSheafMap_naturality d e φ T))

/-- Exact scalar restriction with its module categories made explicit.
Source: Stacks 05RT
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
abbrev systemRestriction {B : Type (u + 1)} [CommRing B] (e : AdicCoefficientDatum B)
    (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) : modules e T ⥤ modules d T :=
  proEtaleRingRestrictScalars.{u} (systemRingMap d e φ T)

/-- Restriction preserves finite limits by the published exact restriction theorem.
Source: Stacks 05RT
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
instance systemRestriction_limits {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) :
    PreservesFiniteLimits (systemRestriction d e φ T) :=
  proEtaleRingRestrictScalars_preservesFiniteLimits (systemRingMap d e φ T)

/-- Restriction preserves finite colimits by the published exact restriction theorem.
Source: Stacks 05RT
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
instance systemRestriction_colimits {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) :
    PreservesFiniteColimits (systemRestriction d e φ T) :=
  proEtaleRingRestrictScalars_preservesFiniteColimits (systemRingMap d e φ T)

/-- The level map is uniquely determined by its sectionwise coefficient homomorphism.
Source: Stacks 00WH and 099M
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: take the underlying additive map of the constant-ring-sheaf map φ_n.
The projection equation for limMap gives scalar linearity for systemRingMap.
Its naturality gives a module-sheaf map. Faithfulness of forgetting the action
makes its specified section values determine the map uniquely. -/
theorem systemModuleMap_existsUnique {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower)
    (T : Scheme.{u}) (n : ℕ) :
    ∃! a : CompletedConstantReduction.residue T d.ideal n ⟶
        (systemRestriction d e φ T).obj
          (CompletedConstantReduction.residue T e.ideal n),
      ∀ (U : T.ProEtᵒᵖ)
        (x : (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U),
        a.val.app U x =
          ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
            (φ.app (op n))).hom.app U x := by
  let q := (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (φ.app (op n))
  have hp : systemRingMap d e φ T ≫ limit.π (adicLisseRingSystem T e.ideal) (op n) =
      limit.π (adicLisseRingSystem T d.ideal) (op n) ≫ q := by
    exact limMap_π _ _
  let ψ : (CompletedConstantReduction.residue T d.ideal n).val.presheaf ⟶
      ((systemRestriction d e φ T).obj
        (CompletedConstantReduction.residue T e.ideal n)).val.presheaf :=
    Functor.whiskerRight q.hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let qm : CompletedConstantReduction.residue T d.ideal n ⟶
      (systemRestriction d e φ T).obj
        (CompletedConstantReduction.residue T e.ideal n) :=
    ⟨PresheafOfModules.homMk ψ (by
      intro U r x
      change (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U at x
      change q.hom.app U
          ((show (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))).obj.obj U from
            (limit.π (adicLisseRingSystem T d.ideal) (op n)).hom.app U r) * x) =
        (show (adicLisseConstantRing T (B ⧸ e.ideal ^ (n + 1))).obj.obj U from
          (limit.π (adicLisseRingSystem T e.ideal) (op n)).hom.app U
            ((systemRingMap d e φ T).hom.app U r)) *
              (show (adicLisseConstantRing T (B ⧸ e.ideal ^ (n + 1))).obj.obj U from
                q.hom.app U x)
      rw [map_mul]
      congr 1
      exact congrArg (fun z ↦ z.hom.app U r) hp.symm)⟩
  refine ⟨qm, fun _ _ ↦ rfl, ?_⟩
  intro qm' hqm'
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact hqm' U x

/-- The specified linear map on quotients, with restriction along the completed map.
Source: Stacks 099M
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
def systemModuleMap {B : Type (u + 1)} [CommRing B] (e : AdicCoefficientDatum B)
    (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) (n : ℕ) :=
  (systemModuleMap_existsUnique d e φ T n).exists.choose

/-- Exact restriction on the standard published derived categories.
Source: Stacks 05RT and 0735
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
abbrev systemDerivedRestriction {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) :
    PerfectProjection.derived.{u} e T ⥤ PerfectProjection.derived.{u} d T :=
  reductionDerivedRestrict.{u} T (systemRingMap d e φ T)

/-- Degree zero in the same standard localization as the recorded quotient object.
Source: Stacks 0735
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
abbrev systemSingle (T : Scheme.{u}) :=
  @DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} (modules d T) inferInstance
    (SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      ((adicLisseForget T).obj (ring d T)))
    (proEtaleRingModules_hasDerivedCategory.{u} T (ring d T)) 0

/-- The canonical exact-restriction comparison on single complexes.
Source: Stacks 0735
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
abbrev systemRestrictionSingle {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) :=
  @Functor.mapDerivedCategorySingleFunctor.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (modules e T) inferInstance
    (SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      ((adicLisseForget T).obj (ring e T)))
    (proEtaleRingModules_hasDerivedCategory.{u} T (ring e T))
    (modules d T) inferInstance
    (SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1}
      ((adicLisseForget T).obj (ring d T)))
    (proEtaleRingModules_hasDerivedCategory.{u} T (ring d T))
    (systemRestriction d e φ T) inferInstance inferInstance inferInstance 0

/-- The same finite-system map on degree-zero derived objects.
Source: Stacks 0735, exact restriction of scalars
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization). -/
def systemDerivedMap {B : Type (u + 1)} [CommRing B] (e : AdicCoefficientDatum B)
    (φ : d.ringTower ⟶ e.ringTower) (T : Scheme.{u}) (n : ℕ) :
    quotient d T n ⟶
      (systemDerivedRestriction d e φ T).obj
        (quotient e T n) :=
  (systemSingle d T).map
      (systemModuleMap d e φ T n) ≫
    (systemRestrictionSingle d e φ T).inv.app
      (CompletedConstantReduction.residue T e.ideal n)

/-- The completed coefficient square induced by a map of finite systems commutes.
Source: Stacks 098T and profinite inverse-image naturality
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: compose both sides with each quotient projection. The limit equations and
finite-level naturality identify them there. The projections jointly detect equality. -/
theorem systemRingMap_square {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (coefficients d f).hom ≫ systemRingMap d e φ X =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (systemRingMap d e φ Y) ≫
        (coefficients e f).hom := by
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, systemRingMap, limMap_π, NatTrans.ofOpSequence_app]
  change coefficientMap d f ≫
      limit.π (adicLisseRingSystem X d.ideal) n ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (φ.app n) = _
  rw [← Category.assoc, coefficientMap, limit.lift_π]
  change ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (limit.π (adicLisseRingSystem Y d.ideal) n) ≫
        (proEtaleConstantComparison f).app _) ≫ _ = _
  rw [Category.assoc, ← (proEtaleConstantComparison f).naturality]
  change _ = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map _ ≫
    coefficientMap e f ≫ _
  rw [← Category.assoc, coefficientMap, limit.lift_π]
  simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp, limMap_π,
    NatTrans.ofOpSequence_app]
  rfl

/-- Both normalizations are natural in arbitrary maps of the finite coefficient systems.
The scalar comparison is the canonical mate of identity on direct-image sections.
Source: Stacks 03D3, 00WH and 0D6D
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: after transposition the two ordinary maps send every constant p to φ_n(p).
The completed projection equation makes these maps linear after restriction.
Sheafification uniqueness and the adjunction give the first equality. Restriction
is exact and leaves underlying complexes unchanged. Localize that equality and
use the canonical single-complex comparison to obtain the second equality. -/
theorem system_naturality {B : Type (u + 1)} [CommRing B]
    (e : AdicCoefficientDatum B) (φ : d.ringTower ⟶ e.ringTower)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).map
        (systemModuleMap d e φ Y n) ≫
      (proEtaleRingRestrictionPullbackInv f (ring d Y) (ring e Y) (ring d X) (ring e X)
        (systemRingMap d e φ Y) (systemRingMap d e φ X) (coefficients d f)
        (coefficients e f) (systemRingMap_square d e φ f)).app
          (CompletedConstantReduction.residue Y e.ideal n) ≫
      (systemRestriction d e φ X).map
        (quotientPullback e f n).hom =
      (quotientPullback d f n).hom ≫ systemModuleMap d e φ X n ∧
    (pullback d f).map (systemDerivedMap d e φ Y n) ≫
      (proEtaleRingRestrictionDerivedPullback.{u} f (ring d Y) (ring e Y)
        (ring d X) (ring e X) (systemRingMap d e φ Y) (systemRingMap d e φ X)
        (coefficients d f) (coefficients e f) (systemRingMap_square d e φ f)).inv.app
          (quotient e Y n) ≫
      (systemDerivedRestriction d e φ X).map
        (quotientDerivedPullback e f n).hom =
      (quotientDerivedPullback d f n).hom ≫ systemDerivedMap d e φ X n := by
  let Ld := proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)
  let Le := proEtaleRingModulePullback f (ring e Y) (ring e X) (coefficients e f)
  let ad := proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)
  let ae := proEtaleRingModuleAdjunction f (ring e Y) (ring e X) (coefficients e f)
  let G := systemRestriction d e φ Y
  let H := systemRestriction d e φ X
  let b := proEtaleRingRestrictionPullbackInv f (ring d Y) (ring e Y)
    (ring d X) (ring e X) (systemRingMap d e φ Y) (systemRingMap d e φ X)
    (coefficients d f) (coefficients e f) (systemRingMap_square d e φ f)
  let c := proEtaleRingRestrictionDirectImage f (ring d Y) (ring e Y)
    (ring d X) (ring e X) (systemRingMap d e φ Y) (systemRingMap d e φ X)
    (coefficients d f) (coefficients e f) (systemRingMap_square d e φ f)
  have hb := restrictionPullback_mate f (ring d Y) (ring e Y)
    (ring d X) (ring e X) (systemRingMap d e φ Y) (systemRingMap d e φ X)
    (coefficients d f) (coefficients e f) (systemRingMap_square d e φ f)
  have hm : Ld.map (systemModuleMap d e φ Y n) ≫
      b.app (CompletedConstantReduction.residue Y e.ideal n) ≫
        H.map (quotientPullback e f n).hom =
      (quotientPullback d f n).hom ≫ systemModuleMap d e φ X n := by
    apply (ad.homEquiv _ _).injective
    rw [ad.homEquiv_naturality_left]
    rw [mate_adjunct ae ad (TwoSquare.mk _ _ _ _ b)]
    change systemModuleMap d e φ Y n ≫ G.map _ ≫
      (mateEquiv ae ad (TwoSquare.mk _ _ _ _ b)).natTrans.app _ = _
    change (mateEquiv ae ad (TwoSquare.mk _ _ _ _ b)).natTrans = c.hom at hb
    rw [hb]
    rw [ad.homEquiv_naturality_right]
    have hc := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
      f (ring d Y) (ring e Y) (ring d X) (ring e X)
      (systemRingMap d e φ Y) (systemRingMap d e φ X)
      (coefficients d f) (coefficients e f) (systemRingMap_square d e φ f))).1
    have hr := congrArg ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
      ((proEtaleConstantComparison f).naturality (φ.app (op n)))
    dsimp only [Functor.comp_map] at hr
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hr
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (c.hom.app (CompletedConstantReduction.residue X e.ideal n)).val.app U
      (((ae.homEquiv _ _ (quotientPullback e f n).hom).val.app U)
        ((systemModuleMap d e φ Y n).val.app U x)) =
      (systemModuleMap d e φ X n).val.app ((proEtaleBaseChange f).op.obj U)
        ((ad.homEquiv _ _ (quotientPullback d f n).hom).val.app U x)
    dsimp only [c, proEtaleRingRestrictionDirectImage]
    erw [hc]
    dsimp only [systemModuleMap, quotientPullback, ad, ae]
    rw [(systemModuleMap_existsUnique d e φ Y n).exists.choose_spec,
      (quotientPullback_existsUnique e f n).exists.choose_spec,
      (quotientPullback_existsUnique d f n).exists.choose_spec,
      (systemModuleMap_existsUnique d e φ X n).exists.choose_spec]
    exact congrArg (fun z ↦ z.hom.app U x) hr
  refine ⟨hm, ?_⟩
  have : IsIso b := proEtaleRingRestrictionPullbackInv_isIso f (ring d Y) (ring e Y)
    (ring d X) (ring e X) (systemRingMap d e φ Y) (systemRingMap d e φ X)
    (coefficients d f) (coefficients e f) (systemRingMap_square d e φ f)
  let be : G ⋙ Ld ≅ Le ⋙ H := asIso b
  let db : pullback e f ⋙ systemDerivedRestriction d e φ X ≅
      systemDerivedRestriction d e φ Y ⋙ pullback d f :=
    (Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2} Le H).symm ≪≫
    Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2} be.symm ≪≫
      Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2, u + 1, u + 1, u + 1,
      u + 2, u + 2, u + 2} G Ld
  let M := CompletedConstantReduction.residue Y e.ideal n
  have hnorm : db.inv.app ((systemSingle e Y).obj M) ≫
      H.mapDerivedCategory.map ((Le.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (H.mapDerivedCategorySingleFunctor 0).hom.app (Le.obj M) =
      Ld.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (Ld.mapDerivedCategorySingleFunctor 0).hom.app (G.obj M) ≫
          (systemSingle d X).map (b.app M) := by
    have hs := Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor be M
    have h1 := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor G Ld M
    have h2 := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor Le H M
    have hi := Functor.mapDerivedCategoryNatIso_symm be
    simp only [db, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
    rw [h2]
    have hi' : (Functor.mapDerivedCategoryNatIso be.symm).inv =
        (Functor.mapDerivedCategoryNatIso be).hom := by
      exact (congrArg Iso.inv
        (Iso.ext hi : Functor.mapDerivedCategoryNatIso be.symm =
          (Functor.mapDerivedCategoryNatIso be).symm))
    rw [hi', hs, ← h1]
    simp only [← Category.assoc]
    erw [Iso.inv_hom_id_app]
    simp only [Category.id_comp]
    rfl
  change Ld.mapDerivedCategory.map
      ((systemSingle d Y).map (systemModuleMap d e φ Y n) ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      db.inv.app ((systemSingle e Y).obj M) ≫
        H.mapDerivedCategory.map
          ((Le.mapDerivedCategorySingleFunctor 0).hom.app M ≫
            (systemSingle e X).map (quotientPullback e f n).hom) =
    ((Ld.mapDerivedCategorySingleFunctor 0).hom.app
        (CompletedConstantReduction.residue Y d.ideal n) ≫
      (systemSingle d X).map (quotientPullback d f n).hom) ≫
        (systemSingle d X).map (systemModuleMap d e φ X n) ≫
          (H.mapDerivedCategorySingleFunctor 0).inv.app
            (CompletedConstantReduction.residue X e.ideal n)
  apply (cancel_mono ((H.mapDerivedCategorySingleFunctor 0).hom.app
    (CompletedConstantReduction.residue X e.ideal n))).mp
  have hH := (H.mapDerivedCategorySingleFunctor 0).hom.naturality
    (quotientPullback e f n).hom
  have hL := (Ld.mapDerivedCategorySingleFunctor 0).hom.naturality
    (systemModuleMap d e φ Y n)
  dsimp only [Functor.comp_map] at hH hL
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  erw [hH]
  rw [reassoc_of% hnorm]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [Category.comp_id, Category.comp_id]
  erw [hL]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [hm]

/-- The ordinary comparison composes through the inverse left-adjoint conjugate of
sectionwise direct-image pasting. Source: Stacks 03D3, 03D8 and 00WH.
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: transpose the quotient comparisons in the actual module adjunctions.
Their adjuncts send constants to the same constants. On an iterated base change,
the direct-image compositor restricts along fibre-product pasting, and preserves
these constants. Precomposing with the constant-presheaf sheafification unit makes
both adjuncts equal; its universal property makes them equal on the whole sheaf.
The unit equation for the inverse conjugate of D identifies the transpose of the
right side with this composite adjunct. Injectivity of the adjunction gives the
formula. In tensor coordinates the conjugate sends m tensor r to (m tensor 1)
tensor r, fixing the ordinary comparison used in derived composition. -/
theorem ordinary_composition {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (D : proEtaleRingModuleDirectImage h (ring d W) (ring d Z) (coefficients d h) ⋙
      proEtaleRingModuleDirectImage k (ring d V) (ring d W) (coefficients d k) ≅
        proEtaleRingModuleDirectImage (h ≫ k) (ring d V) (ring d Z)
          (coefficients d (h ≫ k)))
    (hD : ∀ (N : modules d Z) (U : V.ProEt)
      (m : ((proEtaleRingModuleDirectImage h (ring d W) (ring d Z) (coefficients d h) ⋙
        proEtaleRingModuleDirectImage k (ring d V) (ring d W)
          (coefficients d k)).obj N).val.obj (op U)),
      (D.hom.app N).val.app (op U) m = N.val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m)
    (n : ℕ) :
    (Adjunction.leftAdjointCompIso
      (proEtaleRingModuleAdjunction k (ring d V) (ring d W) (coefficients d k))
      (proEtaleRingModuleAdjunction h (ring d W) (ring d Z) (coefficients d h))
      (proEtaleRingModuleAdjunction (h ≫ k) (ring d V) (ring d Z)
        (coefficients d (h ≫ k))) D).inv.app
          (CompletedConstantReduction.residue V d.ideal n) ≫
      (proEtaleRingModulePullback h (ring d W) (ring d Z) (coefficients d h)).map
        (quotientPullback d k n).hom ≫ (quotientPullback d h n).hom =
      (quotientPullback d (h ≫ k) n).hom := by
  exact PerfectProjection.quotientPullback_compositor d h k n D hD

/-- Completed coefficient transport and the canonical derived compositor give the
normalized degree-zero composition. Source: Stacks 0D6D, 06YS and 00WH.
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: projections of the completed coefficient maps give their composition equality.
The ordinary tensor comparison is the inverse conjugate in ordinary_composition,
since both satisfy its unit equation. Localize this comparison termwise. On every
flat-term K-flat resolution it is the specified canonical derived comparison by
its representative normalization; naturality along the resolving quasi-isomorphism
identifies them on every object. The exact-pullback/single-complex comparisons are
natural in module maps. Their composition equation changes the desired composite
into the single-complex image of ordinary_composition, proving the formula. -/
theorem derived_composition {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    ∃ hc : proEtaleRingCompositeCoefficients h k (ring d V) (ring d W) (ring d Z)
        (coefficients d k) (coefficients d h) = coefficients d (h ≫ k),
      ∀ n : ℕ,
        (eqToIso (congrArg (proEtaleRingDerivedPullback (h ≫ k) (ring d V) (ring d Z))
          hc.symm) ≪≫ proEtaleCanonicalDerivedPullbackComparison h k
            (ring d V) (ring d W) (ring d Z) (coefficients d k)
              (coefficients d h)).hom.app (quotient d V n) ≫
          (pullback d h).map (quotientDerivedPullback d k n).hom ≫
            (quotientDerivedPullback d h n).hom =
          (quotientDerivedPullback d (h ≫ k) n).hom := by
  refine ⟨PerfectProjection.coefficients_comp d h k, fun n ↦ ?_⟩
  exact PerfectProjection.quotientDerivedPullback_compositor d h k n

/-- Ordinary and derived comparisons commute with every quotient transition.
Source: Stacks 00WH and the projection identities in profinite inverse image
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: on constants both adjunct composites send p to its quotient image on the
base-changed object. Sheafification uniqueness gives equality of the linear maps.
Transpose using the module adjunction and then apply exact termwise localization
and naturality of its single-complex comparison. -/
theorem transition_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n m : ℕ) (hnm : n ≤ m) :
    (proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)).map
        (quotientModuleMap d Y n m hnm) ≫ (quotientPullback d f n).hom =
      (quotientPullback d f m).hom ≫ quotientModuleMap d X n m hnm ∧
    (pullback d f).map (quotientMap d Y n m hnm) ≫
        (quotientDerivedPullback d f n).hom =
      (quotientDerivedPullback d f m).hom ≫ quotientMap d X n m hnm := by
  let L := proEtaleRingModulePullback f (ring d Y) (ring d X) (coefficients d f)
  let adj := proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f)
  let adjR := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let c : adicLisseRingSystem Y d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
        adicLisseRingSystem X d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ (proEtaleConstantComparison f).app
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))))
      (fun n ↦ by
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))
  have hr := congrArg (adjR.homEquiv _ _) (c.naturality (homOfLE hnm).op)
  simp only [Functor.comp_map, adjR.homEquiv_naturality_left,
    adjR.homEquiv_naturality_right] at hr
  have hm : L.map (quotientModuleMap d Y n m hnm) ≫ (quotientPullback d f n).hom =
      (quotientPullback d f m).hom ≫ quotientModuleMap d X n m hnm := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (adj.homEquiv _ _ (quotientPullback d f n).hom).val.app U
        ((quotientModuleMap d Y n m hnm).val.app U x) =
      (quotientModuleMap d X n m hnm).val.app ((proEtaleBaseChange f).op.obj U)
        ((adj.homEquiv _ _ (quotientPullback d f m).hom).val.app U x)
    dsimp only [quotientModuleMap, quotientPullback, adj]
    rw [(quotientModuleMap_existsUnique d Y n m hnm).exists.choose_spec,
      (quotientPullback_existsUnique d f n).exists.choose_spec,
      (quotientPullback_existsUnique d f m).exists.choose_spec,
      (quotientModuleMap_existsUnique d X n m hnm).exists.choose_spec]
    exact congrArg (fun z ↦ z.hom.app U x) hr
  exact ⟨hm, quotientDerivedPullback_naturality d f n m hnm⟩

/-- The quotient square uses the inverse ambient pullback comparison, and needs
neither properness nor invertibility of the exchange mate. Source: blueprint
perfect-projection-formula, third proof paragraph, and Stacks 0D6D.
(blueprint: lem-weil-pbc-quotient-pullback-compositor-normalization).
Proof: the profinite comparison agrees around the square after every quotient
projection, hence on the completed ring. Apply derived_composition to both paths.
Transport the middle quotient comparison along the scheme-square equality and
this coefficient equality. Cancel the invertible compositor on the first path.
The remaining product of compositors is precisely the inverse ambient comparison.
No cancellation of an exchange map is involved. -/
theorem cartesian_square {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) (n : ℕ) :
    (pullback d g').map (quotientDerivedPullback d f n).hom ≫
        (quotientDerivedPullback d g' n).hom =
      (proEtaleAmbientRingedPullbackComparison sq
        (ring d X) (ring d Y) (ring d X') (ring d Y')
        (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
        (coefficients_square d f sq)).inv.app (quotient d Y n) ≫
      (pullback d f').map (quotientDerivedPullback d g n).hom ≫
        (quotientDerivedPullback d f' n).hom := by
  let theta := proEtaleAmbientRingedPullbackComparison sq
    (ring d X) (ring d Y) (ring d X') (ring d Y')
    (coefficients d f) (coefficients d g) (coefficients d g') (coefficients d f')
    (coefficients_square d f sq)
  symm
  let cR := eqToIso (congrArg
    (proEtaleRingDerivedPullback (g' ≫ f) (ring d Y) (ring d X'))
    (PerfectProjection.coefficients_comp d g' f).symm) ≪≫
      proEtaleCanonicalDerivedPullbackComparison g' f (ring d Y) (ring d X)
        (ring d X') (coefficients d f) (coefficients d g')
  let cL := eqToIso (congrArg
    (proEtaleRingDerivedPullback (f' ≫ g) (ring d Y) (ring d X'))
    (PerfectProjection.coefficients_comp d f' g).symm) ≪≫
      proEtaleCanonicalDerivedPullbackComparison f' g (ring d Y) (ring d Y')
        (ring d X') (coefficients d g) (coefficients d f')
  have hc : cR ≪≫ theta.symm = eqToIso (congrArg (pullback d) sq.w) ≪≫ cL := by
    apply Iso.ext
    apply NatTrans.ext
    funext P
    simp only [cR, cL, theta, proEtaleAmbientRingedPullbackComparison,
      Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_app_assoc, eqToIso.hom, eqToIso.inv,
      eqToHom_app, eqToHom_trans_assoc]
    rfl
  have ht : (eqToIso (congrArg (pullback d) sq.w)).hom.app (quotient d Y n) ≫
      (quotientDerivedPullback d (f' ≫ g) n).hom =
        (quotientDerivedPullback d (g' ≫ f) n).hom := by
    have transport (kR kL : X' ⟶ Y) (hw : kR = kL) :
        (eqToIso (congrArg (pullback d) hw)).hom.app (quotient d Y n) ≫
          (quotientDerivedPullback d kL n).hom =
            (quotientDerivedPullback d kR n).hom := by
      cases hw
      simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    exact transport _ _ sq.w
  apply (cancel_epi (cR.hom.app (quotient d Y n))).mp
  have he := congrArg (fun e ↦ e.hom.app (quotient d Y n)) hc
  change cR.hom.app (quotient d Y n) ≫ theta.inv.app (quotient d Y n) =
    (eqToIso (congrArg (pullback d) sq.w)).hom.app (quotient d Y n) ≫
      cL.hom.app (quotient d Y n) at he
  simp only [← Category.assoc]
  rw [he]
  simp only [Category.assoc]
  rw [PerfectProjection.quotientDerivedPullback_compositor d f' g n, ht,
    PerfectProjection.quotientDerivedPullback_compositor d g' f n]

end AlgebraicGeometry.Scheme.QuotientPullbackNormalization
