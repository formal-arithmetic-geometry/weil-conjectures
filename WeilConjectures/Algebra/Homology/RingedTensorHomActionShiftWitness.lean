/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorHomActionDefinitions
public import WeilConjectures.Algebra.Homology.RingedKFlatNativeModelIdentification
import WeilConjectures.CategoryTheory.DerivedCategory.NativeDerivedClosedTensorShifts

/-! # A step in the exactness of the ringed tensor-Hom action -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a b c v u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite WeilConjectures
open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

local instance moduleMonoidal : MonoidalCategory (RingedTensorModules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesMonoidal R
local instance moduleSymmetric : SymmetricCategory (RingedTensorModules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesSymmetric R
local instance modulePreadditive : MonoidalPreadditive (RingedTensorModules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesPreadditive R
local instance moduleClosed : MonoidalClosed (RingedTensorModules.{c, v, u} J R) :=
  (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
local instance moduleGrothendieck :
    IsGrothendieckAbelian.{max c v u, max (max c u) v,
      max (max (c + 1) (u + 1)) (v + 1)} (RingedTensorModules.{c, v, u} J R) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
    J R).1
local instance moduleFlat : Abelian.HasFunctorialFlatResolution
    (RingedTensorModules.{c, v, u} J R) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi R

/-- The fixed-factor comparison obtained from the native tensor comparison.
Source: Stacks 06YU (blueprint: lem-sf-tensor-hom-action-shift-normalization). -/
noncomputable def ringedTensorHomActionFixedLeftIso
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (e : @MonoidalCategory.tensor
      (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _
      (RingedDerivedNative.monoidal.{c, v, u, w} J R) ≅
        S.tensor)
    (V : DerivedCategory (RingedTensorModules.{c, v, u} J R)) :
    @MonoidalCategory.tensorLeft
      (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _
      (RingedDerivedNative.monoidal.{c, v, u, w} J R) V ≅ tensorHomActionSource S V :=
  NatIso.ofComponents (fun A ↦ e.app (V, A)) (by
    intro A B f
    simpa [tensorHomActionSource, MonoidalCategory.tensorLeft] using
      e.hom.naturality (Prod.mkHom (𝟙 V) f))

/-- The signed native total-tensor shifts, with no choice of signs or resolutions.
Source: More on Algebra, Tag 0FNH
(blueprint: lem-sf-tensor-hom-action-shift-normalization). -/
@[instance_reducible]
noncomputable def ringedTensorHomActionNativeShift :
    (@MonoidalCategory.curriedTensor
      (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _
      (RingedDerivedNative.monoidal.{c, v, u, w} J R)).CommShift₂Int :=
  DerivedCategory.commShift₂CurriedTensor (RingedTensorModules.{c, v, u} J R)

/-- Transport the signed native shifts through the actual comparison `e`.
Source: Stacks 06YU (blueprint: lem-sf-tensor-hom-action-shift-normalization). -/
@[instance_reducible]
noncomputable def ringedTensorHomActionTransportedFamily
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (e : @MonoidalCategory.tensor
      (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _
      (RingedDerivedNative.monoidal.{c, v, u, w} J R) ≅
        S.tensor) :
    ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ :=
  fun V ↦
    letI : MonoidalCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R)) :=
      RingedDerivedNative.monoidal.{c, v, u, w} J R
    letI : (@MonoidalCategory.curriedTensor
      (DerivedCategory (RingedTensorModules.{c, v, u} J R)) _
      (RingedDerivedNative.monoidal.{c, v, u, w} J R)).CommShift₂Int :=
      ringedTensorHomActionNativeShift J R
    Functor.CommShift.ofIso (ringedTensorHomActionFixedLeftIso J R S e V) ℤ

/-- A normalized native comparison exists for the recorded tensor models.

Proof: the native K-flat model identification gives a normalized localization
transformation `ε`, and for it a native comparison `e` that is normalized.
Source: Stacks 06YU and 0FPT
(blueprint: lem-sf-tensor-hom-action-shift-family). -/
theorem ringed_tensor_hom_action_shift_family
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) :
    ∃ e : RingedKFlatModel.nativeTensor.{c, v, u, w} J R ≅ S.tensor,
      RingedKFlatModel.Normalized.{c, v, u, w} J R S T e := by
  obtain ⟨-, ⟨ε, hε, -⟩, h⟩ :=
    RingedKFlatModel.ringed_kFlat_native_model_identification.{c, v, u, w} J R S T
      (Classical.arbitrary _) β hc
  obtain ⟨e, he, -⟩ := h ε hε
  exact ⟨e, he⟩

/-- The representative normalization for the explicitly transported family.
It is the signed total-tensor shift equation after transport through a normalized
native comparison; it is not asserted for an arbitrary `CommShift` family.

Proof: by uniqueness in the native K-flat model identification, `e` is the comparison
there, so `RingedDerivedNative.tensorIso P Q ≫ e = hc.tensorIso P Q` for K-flat `P,Q`.
By definition the transported shift at `A` is `e⁻¹` at `(V, A⟦n⟧)`, then the native
shift of `V ⊗ᴸ -`, then `e⟦n⟧` at `(V, A)`. Naturality of `e` in both variables moves
`eV` and the localization shift of `Q` past `e⁻¹`; naturality of the native shift in
`V` moves `eV` to the end. What remains is the equation on `Q.obj P` with `P` K-flat
(then `Q⟦n⟧` is K-flat too, by `mapBifunctorShift₂Iso`): the native shift of
`Q.obj P ⊗ᴸ -` at `Q.obj Q` is, through the localization tensorator, the image of
`mapBifunctorShift₂Iso P Q` (third conjunct of
`DerivedCategory.nativeDerivedClosedTensorShifts`, with both tensorators inverted).
Source: Stacks 06YU and More on Algebra, Tag 0FNH
(blueprint: lem-sf-tensor-hom-action-shift-normalization). -/
theorem ringed_tensor_hom_action_shift_normalization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (e : RingedKFlatModel.nativeTensor.{c, v, u, w} J R ≅ S.tensor)
    (he : RingedKFlatModel.Normalized.{c, v, u, w} J R S T e) :
    tensorHomActionShiftNormalization J R S T β hc
      (ringedTensorHomActionTransportedFamily J R S e) := by
  let : MonoidalCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R)) :=
    RingedDerivedNative.monoidal.{c, v, u, w} J R
  let : (MonoidalCategory.curriedTensor
      (DerivedCategory (RingedTensorModules.{c, v, u} J R))).CommShift₂Int :=
    ringedTensorHomActionNativeShift.{c, v, u, w} J R
  obtain ⟨-, ⟨ε, hε, -⟩, h⟩ :=
    RingedKFlatModel.ringed_kFlat_native_model_identification.{c, v, u, w} J R S T
      (Classical.arbitrary _) β hc
  -- Uniqueness extends the given comparison's normalization to every K-flat pair.
  obtain ⟨e₀, -, hu, -, -, hm, -⟩ := h ε hε
  have heq := hu e he
  subst e₀
  have hmodel (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
      (hc.tensorIso P Q (Or.inl hP)).hom =
        (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    (hm P Q hP hQ).symm
  change ∀ (V : DerivedCategory (RingedTensorModules.{c, v, u} J R))
    (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ), _
  intro V P Q hP hQ eV n
  -- A signed total-tensor shift identifies the acyclic tests for Q and Q[n].
  have hQn : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) (Q⟦n⟧) := by
    intro E hE
    have ht := hQ E hE
    have hs : (CochainComplex.mapBifunctor E Q
        (MonoidalCategory.curriedTensor (RingedTensorModules.{c, v, u} J R))⟦n⟧).Acyclic := by
      rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
      rw [← HomotopyCategory.shift_quotient_obj]
      exact (HomotopyCategory.subcategoryAcyclic _).le_shift n _ ht
    intro i
    exact (hs i).of_iso (CochainComplex.mapBifunctorShift₂Iso E Q
      (MonoidalCategory.curriedTensor (RingedTensorModules.{c, v, u} J R)) n).symm
  -- Invert the native tensorators in the signed localization square.
  have hnative := (DerivedCategory.nativeDerivedClosedTensorShifts
    (RingedTensorModules.{c, v, u} J R)).2.2.1 P Q n
  have hn : (RingedDerivedNative.tensorIso.{c, v, u, w} J R P (Q⟦n⟧) (Or.inl hP)).hom ≫
      (MonoidalCategory.tensor _).map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦n⟧)))
        (Y := (DerivedCategory.Q.obj P, (DerivedCategory.Q.obj Q)⟦n⟧))
        (𝟙 _, (DerivedCategory.Q.commShiftIso n).hom.app Q) ≫
      ((MonoidalCategory.tensorLeft (DerivedCategory.Q.obj P)).commShiftIso n).hom.app
        (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map
          (CochainComplex.mapBifunctorShift₂Iso P Q (MonoidalCategory.curriedTensor _) n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) ≫
        (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)).hom⟦n⟧' := by
    have := RingedDerivedNative.isIso_mu.{c, v, u, w} J R P Q (Or.inl hP)
    have := RingedDerivedNative.isIso_mu.{c, v, u, w} J R P (Q⟦n⟧) (Or.inl hP)
    apply (cancel_epi (Functor.LaxMonoidal.μ DerivedCategory.Q P (Q⟦n⟧))).1
    simp only [RingedDerivedNative.tensorIso, Iso.symm_hom, asIso_inv,
      IsIso.hom_inv_id_assoc]
    erw [reassoc_of% hnative]
    simp only [← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id, Category.comp_id]
    simp only [MonoidalCategory.tensor_map, MonoidalCategory.id_tensorHom,
      Functor.uncurry_obj_map, MonoidalCategory.curriedTensor_obj_map,
      MonoidalCategory.curriedTensor_map_app, MonoidalCategory.id_whiskerRight]
    erw [Category.id_comp]
  dsimp only
  rw [hmodel P (Q⟦n⟧) hP hQn]
  have hmodels := hmodel P Q hP hQ
  have hproof : (hc.tensorIso P Q (Or.inr hQ)).hom =
      (hc.tensorIso P Q (Or.inl hP)).hom := rfl
  rw [hproof, hmodels]
  -- Move the representative identification through the native and transported shifts.
  let N := MonoidalCategory.tensor (DerivedCategory (RingedTensorModules.{c, v, u} J R))
  let F := MonoidalCategory.curriedTensor
    (DerivedCategory (RingedTensorModules.{c, v, u} J R))
  let d := ringedTensorHomActionFixedLeftIso.{c, v, u, w} J R S e V
  let : (tensorHomActionSource S V).CommShift ℤ :=
    ringedTensorHomActionTransportedFamily.{c, v, u, w} J R S e V
  have hd : NatTrans.CommShift d.hom ℤ := Functor.CommShift.ofIso_compatibility d ℤ
  have hds := NatTrans.shift_app_comm d.hom n (DerivedCategory.Q.obj Q)
  have hmove : NatTrans.CommShift (F.map eV.hom) ℤ :=
    Functor.CommShift₂.commShift_map (G := F) (h := .int) eV.hom
  have hms := NatTrans.shift_app_comm (F.map eV.hom) n (DerivedCategory.Q.obj Q)
  have hv : N.map
      (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦n⟧)))
      (Y := (V, (DerivedCategory.Q.obj Q)⟦n⟧))
      (eV.hom, (DerivedCategory.Q.commShiftIso n).hom.app Q) ≫
        ((F.obj V).commShiftIso n).hom.app (DerivedCategory.Q.obj Q) =
      N.map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦n⟧)))
        (Y := (DerivedCategory.Q.obj P, (DerivedCategory.Q.obj Q)⟦n⟧))
        (𝟙 _, (DerivedCategory.Q.commShiftIso n).hom.app Q) ≫
        ((F.obj (DerivedCategory.Q.obj P)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj Q) ≫
        (N.map (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
          (Y := (V, DerivedCategory.Q.obj Q)) (eV.hom, 𝟙 _))⟦n⟧' := by
    simp only [N, MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id]
    change _ ≫ _ = _ ≫ _ ≫ ((F.map eV.hom).app (DerivedCategory.Q.obj Q))⟦n⟧'
    rw [hms]
    change _ ≫ _ = (𝟙 _ ⊗ₘ (DerivedCategory.Q.commShiftIso n).hom.app Q) ≫
      (eV.hom ▷ (DerivedCategory.Q.obj Q)⟦n⟧) ≫ _
    rw [← Category.assoc, MonoidalCategory.id_tensorHom]
    erw [← MonoidalCategory.tensorHom_def' eV.hom
      ((DerivedCategory.Q.commShiftIso n).hom.app Q)]
  simp only [Category.assoc]
  rw [← e.hom.naturality_assoc]
  change (RingedDerivedNative.tensorIso.{c, v, u, w} J R P (Q⟦n⟧) (Or.inl hP)).hom ≫
      N.map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦n⟧)))
        (Y := (V, (DerivedCategory.Q.obj Q)⟦n⟧))
        (eV.hom, (DerivedCategory.Q.commShiftIso n).hom.app Q) ≫
        d.hom.app ((DerivedCategory.Q.obj Q)⟦n⟧) ≫
        ((tensorHomActionSource S V).commShiftIso n).hom.app (DerivedCategory.Q.obj Q) = _
  rw [← hds, reassoc_of% hv]
  erw [reassoc_of% hn]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← e.hom.naturality]
  rfl

/-- The normalized coefficient shifts exist for the recorded closed tensor structure.

Proof: choose the normalized native comparison from the K-flat model
identification (`ringed_tensor_hom_action_shift_family`).  Its signed total-tensor
`CommShift₂Int` is the canonical derived shift, and
`ringedTensorHomActionTransportedFamily` transports its fixed-left component through
the comparison.  On K-flat representatives the normalization
calculation is the signed total-tensor square, with the comparison equation supplied
by `RingedKFlatModel.Normalized`; naturality and cancellation extend it to every
fixed object and every representative identification.
Source: Stacks 06YU and More on Algebra, Tag 0FNH
(blueprint: lem-sf-tensor-hom-action-normalized-shifts).
-/
theorem ringed_tensor_hom_action_shift_witness
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β) :
    ∃ s : ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ,
      tensorHomActionShiftNormalization J R S T β hc s := by
  obtain ⟨e, he⟩ := ringed_tensor_hom_action_shift_family J R S T β hc
  exact ⟨ringedTensorHomActionTransportedFamily J R S e,
    ringed_tensor_hom_action_shift_normalization J R S T β hc e he⟩

end CategoryTheory
