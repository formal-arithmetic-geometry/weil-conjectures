/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureOrdinaryLine
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.IntegersModPow
public import WeilConjectures.TateTwist.Integral
import all WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRootPullStep

/-!
# The two descriptions of `ℚ̄_ℓ(1)`

Let `ℓ` be a prime invertible on a scheme `X`. The blueprint (`definition-tate-twists`) defines
`ℚ̄_{ℓ,X}(1) = colim_E E_X(1)`, where `E_X(1) = 𝒪_{E,X}(1)[1/ℓ]` and
`𝒪_{E,X}(1) = lim_n (𝒪_E/ℓ^{n+1})_X ⊗ μ_{ℓ^{n+1}}` (`AlgebraicGeometry.ProEtale.spQbarTwist`), and
asserts the equivalent description `ℚ̄_{ℓ,X}(1) = ℚ̄_{ℓ,X} ⊗_{ℤ_{ℓ,X}} ℤ_{ℓ,X}(1)` with
`ℤ_{ℓ,X}(1) = lim_n μ_{ℓ^n}` (`AlgebraicGeometry.ProEtale.tateTwistOne`). This file proves it
(`AlgebraicGeometry.ProEtale.nonempty_spQbarTwist_iso_tateTwistOne`).

## Strategy

* For the bottom subextension `E = ℚ_ℓ`, the inclusion `ℤ_{ℓ,X} ⟶ 𝒪_{ℚ_ℓ,X}` is an isomorphism, and
  the levels `ℤ_ℓ ⊗ μ_{ℓ^{n+1}}` of the Tate module are the levels
  `(𝒪_{ℚ_ℓ}/ℓ^{n+1}) ⊗ μ_{ℓ^{n+1}}` of `𝒪_{ℚ_ℓ,X}(1)`: the reduction is the cokernel of `ℓ^{n+1}`,
  tensoring is right exact, and `ℓ^{n+1}` kills `μ_{ℓ^{n+1}}`. These comparisons are compatible
  with the transition maps, so passing to the limit gives a canonical isomorphism
  `ℤ_ℓ(1) ≅ 𝒪_{ℚ_ℓ,X}(1)` (`AlgebraicGeometry.ProEtale.tateModuleIsoComapSpIntegralTwist`).
* Transitivity of extension of scalars along `ℤ_{ℓ,X} ≅ 𝒪_{ℚ_ℓ,X} ⟶ ℚ_{ℓ,X} ⟶ ℚ̄_{ℓ,X}` gives a
  canonical isomorphism `ℚ̄_ℓ ⊗_{ℤ_ℓ} ℤ_ℓ(1) ≅ ℚ̄_ℓ ⊗_{ℚ_ℓ} ℚ_{ℓ,X}(1)`
  (`AlgebraicGeometry.ProEtale.tateTwistOneIsoExtendScalarsSpRationalTwist`).
* Finally `ℚ̄_ℓ ⊗_{ℚ_ℓ} ℚ_{ℓ,X}(1) ≅ ℚ̄_{ℓ,X}(1)` by
  `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalClosure_ordinaryLine`, which is where
  the invertibility of `ℓ` is used.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite
open scoped CategoryTheory.Obj

namespace Profinite

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inclusion `ℤ̲_ℓ ⟶ 𝒪̲_{ℚ_ℓ}` into the condensed ring of integers of the bottom
subextension `ℚ_ℓ ⊆ ℚ̄_ℓ` is an isomorphism. -/
instance isIso_padicIntRingObjToPadicIntegers_bot :
    IsIso (padicIntRingObjToPadicIntegers.{u} ℓ
      (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))) := by
  obtain ⟨-, eInt, -, heInt, -, -, -, -, -, zIso, -, -, hz, -, -⟩ :=
    base_coefficient_condensed_identification.{u} ℓ
  have h : padicIntRingObjToPadicIntegers.{u} ℓ (⊥ : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) =
      zIso.hom.hom := by
    ext S a
    refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
    exact ((hz S.unop a.down s).trans (RingHom.congr_fun heInt (a.down s))).symm
  rw [h]
  exact (Mon.forget _).map_isIso zIso.hom

/-- The reduction `𝒪̲_E ⟶ (𝒪_E ⧸ ℓ^{n+1})̲` is the cokernel of the multiplication by `ℓ^{n+1}`. -/
noncomputable def isColimitSpEllPointReduction (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (f := ((ℓ : ℤ) ^ (n + 1) • 𝟙 (padicIntegersRingObj.{u} ℓ E.1)))
      (AlgebraicGeometry.ProEtale.spEllPointReduction.{u} ℓ E n)
      (zsmul_id_comp_padicIntegersRingObjToIntegersModPow ℓ E.1 (n + 1))) :=
  (shortExact_padicIntegersRingObjToIntegersModPow ℓ E.1 (n + 1)).gIsCokernel

end Profinite

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inverse image `p_X^*` from the point is additive, being a left adjoint. -/
private lemma additive_upperStarFromPoint' : (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)

/-- If `ℓ^{n+1}` kills an abelian sheaf `M`, then tensoring the reduction
`𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓ^{n+1})_X` with `M` is an isomorphism: the reduction is the cokernel of
`ℓ^{n+1}`, tensoring with `M` is right exact, and `ℓ^{n+1} ⊗ M = 0`. -/
lemma isIso_spEllReduction_whiskerRight (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)
    (M : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (hM : ((ℓ : ℤ) ^ (n + 1)) • 𝟙 M = 0) :
    IsIso (spEllReduction X ℓ E n ▷ M) := by
  have := additive_upperStarFromPoint' X
  let G := upperStarFromPoint X ⋙ tensorRight M
  have hc := (CokernelCofork.ofπ _ _).mapIsColimit
    (Profinite.isColimitSpEllPointReduction ℓ E n) G
  refine CokernelCofork.IsColimit.isIso_π _ hc ?_
  let A := (upperStarFromPoint X).obj (Profinite.padicIntegersRingObj.{u} ℓ E.1)
  have h₁ : (((ℓ : ℤ) ^ (n + 1)) • 𝟙 A) ▷ M = ((ℓ : ℤ) ^ (n + 1)) • (𝟙 A ▷ M) :=
    (tensorRight M).map_zsmul (f := 𝟙 A) (r := (ℓ : ℤ) ^ (n + 1))
  have h₂ : A ◁ (((ℓ : ℤ) ^ (n + 1)) • 𝟙 M) = ((ℓ : ℤ) ^ (n + 1)) • (A ◁ 𝟙 M) :=
    (tensorLeft A).map_zsmul (f := 𝟙 M) (r := (ℓ : ℤ) ^ (n + 1))
  have h₃ : G.map (((ℓ : ℤ) ^ (n + 1)) • 𝟙 (Profinite.padicIntegersRingObj.{u} ℓ E.1)) =
      (upperStarFromPoint X).map (((ℓ : ℤ) ^ (n + 1)) • 𝟙 _) ▷ M := rfl
  rw [h₃, Functor.map_zsmul, CategoryTheory.Functor.map_id, h₁, id_whiskerRight,
    ← MonoidalCategory.whiskerLeft_id, ← h₂, hM, MonoidalPreadditive.whiskerLeft_zero]

/-- `N` kills the sheaf `μ_N` of `N`-th roots of unity. -/
lemma natCast_zsmul_id_proEtaleRootsOfUnitySheaf (N : ℕ) :
    (N : ℤ) • 𝟙 (Scheme.proEtaleRootsOfUnitySheaf X N) = 0 := by
  ext U x
  have h : ((N : ℤ) • 𝟙 (Scheme.proEtaleRootsOfUnitySheaf X N)).hom.app U = (N : ℤ) • 𝟙 _ :=
    ((sheafToPresheaf _ Ab.{u + 1} ⋙ (evaluation _ _).obj U).map_zsmul (f := 𝟙 _)
      (r := (N : ℤ))).trans (by simp)
  rw [h]
  simpa using Scheme.proEtaleRootsOfUnity_nsmul X N U x

/-- The normalized comparison `μ_N ≅ μ_N` between the two presentations of the roots of unity
intertwines the power map `μ_{mN} ⟶ μ_N` with the Kummer transition. -/
lemma rootComparison_transition_of_eq (N m M : ℕ) (h : M = m * N) (hN : 0 < N) (hM : 0 < M)
    (hd : N ∣ M) :
    eqToHom (congrArg (rootsOfUnitySheaf X) h) ≫ rootsOfUnitySheafPow X N m ≫
        (PurityTransport.rootComparison X N).hom =
      (PurityTransport.rootComparison X M).hom ≫
        Scheme.proEtaleRootsOfUnityTransition X N M hN hM hd := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  exact PurityTransport.rootComparison_transition X N m hN (Nat.pos_of_mul_pos_right hM)

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C] {R D : C} [MonObj R] [MonObj D]

/-- The morphism `q ⊗ v : R ⊗ U ⟶ D ⊗ V` from the free `R`-module on `U` to the restriction of
scalars of the free `D`-module on `V` along a morphism of monoid objects `q : R ⟶ D`. -/
def freeTensorHom (q : R ⟶ D) [IsMonHom q] {U V : C} (v : U ⟶ V) :
    (freeFunctor R).obj U ⟶ (comap q).obj ((free D).obj V) :=
  homMk (q ⊗ₘ v) (by
    change ((α_ R R U).inv ≫ μ ▷ U) ≫ (q ⊗ₘ v) =
      R ◁ (q ⊗ₘ v) ≫ q ▷ (D ⊗ V) ≫ (α_ D D V).inv ≫ μ ▷ V
    have e₁ : μ ▷ U ≫ (q ⊗ₘ v) = ((q ⊗ₘ q) ⊗ₘ v) ≫ μ ▷ V := by
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        IsMonHom.mul_hom, Category.id_comp, Category.comp_id]
    rw [Category.assoc, e₁, ← Category.assoc (R ◁ (q ⊗ₘ v)), ← tensorHom_def',
      associator_inv_naturality_assoc])

/-- The underlying morphism of `freeTensorHom q v` is `q ⊗ v`. -/
@[simp]
lemma freeTensorHom_hom (q : R ⟶ D) [IsMonHom q] {U V : C} (v : U ⟶ V) :
    (freeTensorHom q v).hom = q ⊗ₘ v := rfl

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

set_option hygiene false in
/-- The bottom finite subextension `ℚ_ℓ ⊆ ℚ̄_ℓ`. -/
local notation "𝔼" => (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField ℓ)

set_option hygiene false in
/-- The isomorphism `ℤ_{ℓ,X} ⟶ 𝒪_{ℚ_ℓ,X}`. -/
local notation "φ" => coefficientMap (Profinite.padicIntRingObjToPadicIntegers ℓ (𝔼).1) X

/-- The comparison `ℤ_ℓ ⊗ μ_{ℓ^{n+1}} ⟶ (𝒪_{ℚ_ℓ}/ℓ^{n+1}) ⊗ μ_{ℓ^{n+1}}` between the `(n+1)`-st
level of the Tate module and the `n`-th level of the integral twist `𝒪_{ℚ_ℓ,X}(1)`. -/
noncomputable def tateModuleLevelSuccHom (n : ℕ) :
    tateModuleLevel X ℓ (n + 1) ⟶ (Mod.comap φ).obj (spIntegralTwistLevel X ℓ 𝔼 n) :=
  Mod.freeTensorHom (φ ≫ spEllReduction X ℓ 𝔼 n)
      (PurityTransport.rootComparison X (ℓ ^ (n + 1))).hom ≫
    (Mod.comapComp φ (spEllReduction X ℓ 𝔼 n)).hom.app _

/-- The underlying morphism of the level comparison is `(ℤ_ℓ ⟶ 𝒪_{ℚ_ℓ}/ℓ^{n+1}) ⊗ (μ ≅ μ)`. -/
lemma tateModuleLevelSuccHom_hom (n : ℕ) :
    (tateModuleLevelSuccHom X ℓ n).hom = (φ ≫ spEllReduction X ℓ 𝔼 n) ⊗ₘ
      (PurityTransport.rootComparison X (ℓ ^ (n + 1))).hom := by
  simp [tateModuleLevelSuccHom, Mod.comapComp]

/-- The level comparison is an isomorphism, since `ℓ^{n+1}` kills `μ_{ℓ^{n+1}}`. -/
instance (n : ℕ) : IsIso (tateModuleLevelSuccHom X ℓ n) := by
  rw [← isIso_iff_of_reflects_iso _ (Mod.forget _)]
  have hM : ((ℓ : ℤ) ^ (n + 1)) • 𝟙 (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))) = 0 := by
    simpa using natCast_zsmul_id_proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))
  have := isIso_spEllReduction_whiskerRight X ℓ 𝔼 n _ hM
  have e : (tateModuleLevelSuccHom X ℓ n).hom = (φ ⊗ₘ
      (PurityTransport.rootComparison X (ℓ ^ (n + 1))).hom) ≫ spEllReduction X ℓ 𝔼 n ▷ _ := by
    rw [tateModuleLevelSuccHom_hom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  rw [Mod.forget_map, e]
  infer_instance

/-- The successive reductions `𝒪_E ⟶ 𝒪_E/ℓ^{n+2} ⟶ 𝒪_E/ℓ^{n+1}` compose to the reduction. -/
lemma spEllReduction_comp_transition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllReduction X ℓ E (n + 1) ≫ coefficientMap (spEllPointTransition ℓ E n) X =
      spEllReduction X ℓ E n := by
  rw [← coefficientMap_comp]
  apply congrArg (fun f ↦ coefficientMap.{u} f X)
  unfold spEllPointReduction spEllPointTransition
  rw [← Functor.map_comp]
  rfl

/-- The level comparisons commute with the transition maps of both towers. -/
lemma tateModuleLevelSuccHom_naturality (n : ℕ) :
    tateModuleTransition X ℓ (n + 1) ≫ tateModuleLevelSuccHom X ℓ n =
      tateModuleLevelSuccHom X ℓ (n + 1) ≫
        (Mod.comap φ).map (spIntegralLevelTransition X ℓ 𝔼 n) := by
  have ht : (spIntegralLevelTransition X ℓ 𝔼 n).hom =
      coefficientMap.{u} (spEllPointTransition ℓ 𝔼 n) X ⊗ₘ
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) :=
    (spIntegralLevelTransition_existsUnique X ℓ 𝔼 n).exists.choose_spec
  have hc := rootComparison_transition_of_eq X (ℓ ^ (n + 1)) ℓ (ℓ ^ (n + 2)) (pow_succ' ℓ _)
    (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
    (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
  apply Mod.hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', tateModuleLevelSuccHom_hom, tateModuleLevelSuccHom_hom,
    Mod.comap_map_hom, ht, tateModuleTransition, Mod.freeFunctor_map_hom, ← id_tensorHom,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.assoc,
    Category.assoc, spEllReduction_comp_transition, hc]

/-- The shift `n ↦ n + 1` of `ℕᵒᵖ`. -/
def succOpFunctor : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show Monotone (fun n : ℕ ↦ n + 1) from fun _ _ h ↦ Nat.add_le_add_right h 1).functor.op

/-- The shift `n ↦ n + 1` is initial in `ℕᵒᵖ`. -/
instance : succOpFunctor.Initial :=
  Functor.initial_of_exists_of_isCofiltered succOpFunctor
    (fun n ↦ ⟨n, ⟨(homOfLE (Nat.le_succ n.unop)).op⟩⟩)
    (fun {_ c} _ _ ↦ ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)

/-- The comparison of the shifted Tate module tower `n ↦ ℤ_ℓ ⊗ μ_{ℓ^{n+1}}` with the tower of
`𝒪_{ℚ_ℓ,X}(1)`, restricted to `ℤ_{ℓ,X}`. -/
noncomputable def tateModuleSystemShiftHom :
    succOpFunctor ⋙ tateModuleSystem X ℓ ⟶ spIntegralTwistSystem X ℓ 𝔼 ⋙ Mod.comap φ :=
  NatTrans.ofOpSequence (fun n ↦ tateModuleLevelSuccHom X ℓ n) (fun n ↦ by
    have h : succOpFunctor.map (homOfLE (Nat.le_add_right n 1)).op =
        (homOfLE (Nat.le_add_right (n + 1) 1)).op := Subsingleton.elim _ _
    simp only [Functor.comp_map, h, tateModuleSystem, spIntegralTwistSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact tateModuleLevelSuccHom_naturality X ℓ n)

/-- The comparison of towers is an isomorphism, levelwise. -/
instance : IsIso (tateModuleSystemShiftHom X ℓ) := by
  have (n : ℕᵒᵖ) : IsIso ((tateModuleSystemShiftHom X ℓ).app n) := by
    rw [tateModuleSystemShiftHom, NatTrans.ofOpSequence_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The Tate module `ℤ_ℓ(1) = lim_n μ_{ℓ^n}` is the restriction of scalars of the integral twist
`𝒪_{ℚ_ℓ,X}(1) = lim_n (𝒪_{ℚ_ℓ}/ℓ^{n+1})_X(1)` along the isomorphism `ℤ_{ℓ,X} ≅ 𝒪_{ℚ_ℓ,X}`. -/
noncomputable def tateModuleIsoComapSpIntegralTwist :
    tateModule X ℓ ≅ (Mod.comap φ).obj (spIntegralTwist X ℓ 𝔼) :=
  have : PreservesLimitsOfSize.{0, 0} (Mod.comap φ) :=
    (Mod.extendRestrictAdjunction φ).rightAdjoint_preservesLimits
  (Functor.Initial.limitIso succOpFunctor (tateModuleSystem X ℓ)).symm ≪≫
    HasLimit.isoOfNatIso (asIso (tateModuleSystemShiftHom X ℓ)) ≪≫
    (preservesLimitIso (Mod.comap φ) (spIntegralTwistSystem X ℓ 𝔼)).symm

/-- The inclusions `𝒪̲_E ⟶ E̲ ⟶ ℚ̲̄_ℓ` compose to the inclusion `𝒪̲_E ⟶ ℚ̲̄_ℓ`. -/
lemma padicIntegersRingObjToContinuousMapRingObj_comp_padicSubfieldRingObjToPadicAlgCl
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E ≫
        Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E =
      Profinite.padicIntegersRingObjToPadicAlgCl ℓ E.1 := by
  rw [padicIntegersRingObjToContinuousMapRingObj, Profinite.padicSubfieldRingObjToPadicAlgCl,
    Profinite.padicIntegersRingObjToPadicAlgCl, ← Functor.map_comp]
  congr 1

/-- The canonical isomorphism `ℚ̄_{ℓ,X} ⊗_{ℤ_{ℓ,X}} ℤ_{ℓ,X}(1) ≅ ℚ̄_{ℓ,X} ⊗_{ℚ_{ℓ,X}} ℚ_{ℓ,X}(1)`,
where `ℚ_{ℓ,X}(1) = 𝒪_{ℚ_ℓ,X}(1)[1/ℓ]` is the rational twist for the bottom field `E = ℚ_ℓ`:
transitivity of extension of scalars along `ℤ_{ℓ,X} ≅ 𝒪_{ℚ_ℓ,X} ⟶ ℚ_{ℓ,X} ⟶ ℚ̄_{ℓ,X}` and the
identification `ℤ_ℓ(1) ≅ 𝒪_{ℚ_ℓ,X}(1)`. -/
noncomputable def tateTwistOneIsoExtendScalarsSpRationalTwist :
    tateTwistOne X ℓ ≅ (Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ 𝔼) X)).obj
        (spRationalTwist X ℓ 𝔼) :=
  (extendScalarsIntegralTateTwistOneIso X ℓ (𝔼).1).symm ≪≫
    ((Mod.extendScalarsCompIsoOfEq (CondensedRing.coefficientMap_comp_eq _ _ _
      (padicIntegersRingObjToContinuousMapRingObj_comp_padicSubfieldRingObjToPadicAlgCl ℓ 𝔼)
        X)).app _).symm ≪≫
    (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ 𝔼) X)).mapIso
      ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ 𝔼)).mapIso
        ((Mod.extendScalars φ).mapIso (tateModuleIsoComapSpIntegralTwist X ℓ) ≪≫
          (Mod.extendScalarsIsoComapInv φ).app _ ≪≫
          ((Mod.comapEquivalenceOfIsIso φ).unitIso.app _).symm))

/-- **Scalar description of the algebraic Tate twist.** If `ℓ` is invertible on `X`, the
twist `ℚ̄_{ℓ,X}(1) = colim_E E_X(1)`, `E_X(1) = (lim_n (𝒪_E/ℓ^n)_X(1))[1/ℓ]`, is isomorphic to
`ℚ̄_{ℓ,X} ⊗_{ℤ_{ℓ,X}} ℤ_{ℓ,X}(1)` with `ℤ_{ℓ,X}(1) = lim_n μ_{ℓ^n,X}`.
(blueprint: `definition-tate-twists--9`) -/
theorem nonempty_spQbarTwist_iso_tateTwistOne (hX : IsUnit (ℓ : Γ(X, ⊤))) :
    Nonempty (spQbarTwist X ℓ ≅ tateTwistOne X ℓ) := by
  obtain ⟨q, -⟩ := DiagonalCoefficients.diagonalClosure_ordinaryLine ℓ 𝔼 X hX
  exact ⟨q.symm ≪≫ (tateTwistOneIsoExtendScalarsSpRationalTwist X ℓ).symm⟩

end AlgebraicGeometry.ProEtale
