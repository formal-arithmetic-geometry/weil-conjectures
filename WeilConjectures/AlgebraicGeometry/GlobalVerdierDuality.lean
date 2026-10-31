/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VerdierExchange
public import WeilConjectures.AlgebraicGeometry.CommonStageCompactWeilCohomology
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.GlobalVerdierDualityData
import WeilConjectures.AlgebraicGeometry.GlobalIdentityNormalization
import WeilConjectures.CategoryTheory.ProjectionInternalHom
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Global Verdier duality by the five adjunction bijections -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated.Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.GlobalVerdierDuality
open ConstructibleExceptionalCoefficients VerdierExchange

variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)
private theorem transpose_left (P Q : D) {T T' : D} (f : T ⟶ T')
    (g : S.tensor.obj (T', P) ⟶ Q) :
    S.transpose T P Q (S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ g) =
      f ≫ S.transpose T' P Q g := by
  let := S.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor, Functor.flip,
    Prod.sectR, MonoidalCategory.tensor, Functor.comp_obj] using
    (S.adjunction P).homEquiv_naturality_left f g
private theorem transpose_symm_left (P Q : D) {T T' : D} (f : T ⟶ T')
    (g : T' ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm (f ≫ g) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose T' P Q).symm g := by
  let := S.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor, Functor.flip,
    Prod.sectR, MonoidalCategory.tensor, Functor.comp_obj] using
    (S.adjunction P).homEquiv_naturality_left_symm f g
private theorem transpose_symm_id (P Q : D) :
    (S.transpose (H.obj (op P, Q)) P Q).symm (𝟙 _) = S.evaluation P Q :=
  (S.adjunction P).homEquiv_symm_id Q
private def unitAdjunction :
    @MonoidalCategory.tensorRight D _ S.monoidal S.monoidal.tensorUnit ⊣ 𝟭 D := by
  letI := S.monoidal
  exact Adjunction.id.ofNatIsoLeft (MonoidalCategory.rightUnitorNatIso D).symm
private def closedUnitIso (O : D) : H.obj (op S.monoidal.tensorUnit, O) ≅ O :=
  ((S.adjunction S.monoidal.tensorUnit).rightAdjointUniq (unitAdjunction S)).app O
private theorem closedUnitIso_hom (O : D) :
    (closedUnitIso S O).hom =
      (S.monoidal.rightUnitor _).inv ≫ S.evaluation S.monoidal.tensorUnit O := by
  let := S.monoidal
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (S.adjunction S.monoidal.tensorUnit) (unitAdjunction S) O
  change ((unitAdjunction S).homEquiv _ _).symm (closedUnitIso S O).hom = _ at h
  rw [unitAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply] at h
  simp only [Adjunction.homEquiv_counit, Adjunction.id, Functor.id_map,
    NatTrans.id_app, Iso.symm_inv,
    MonoidalCategory.rightUnitorNatIso_hom_app] at h
  dsimp only [Functor.comp_obj, Functor.id_obj] at h
  simp only [Category.comp_id] at h
  change (S.monoidal.rightUnitor _).hom ≫ (closedUnitIso S O).hom =
    S.evaluation S.monoidal.tensorUnit O at h
  rw [← h, Iso.inv_hom_id_assoc]
private theorem closedUnitIso_inv (O : D) :
    (closedUnitIso S O).inv = S.transpose O S.monoidal.tensorUnit O
      (S.monoidal.rightUnitor O).hom := by
  let := S.monoidal
  apply (S.adjunction S.monoidal.tensorUnit).homEquiv O O |>.symm.injective
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (unitAdjunction S) (S.adjunction S.monoidal.tensorUnit) O
  rw [← Adjunction.rightAdjointUniq_inv_app] at h
  change ((S.adjunction S.monoidal.tensorUnit).homEquiv O O).symm
    (closedUnitIso S O).inv = _ at h
  change _ = ((S.adjunction S.monoidal.tensorUnit).homEquiv O O).symm
    (((S.adjunction S.monoidal.tensorUnit).homEquiv O O) _)
  rw [Equiv.symm_apply_apply]
  simpa [unitAdjunction] using h

section Stage
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S : Scheme.{u}} {s : Stage.{u} l}
  {F : Operation.{u, u} l Ω X S s} {unit : C.{u, u} l Ω S s}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem epsilon_isIso (d : Data l Ω F unit)
    (hd : d.dualizing = Iso.refl (F.G.obj unit))
    (hn : ∀ (M : C.{u, u} l Ω X s) {K L : C.{u, u} l Ω S s} (k : K ⟶ L),
      F.F.map (d.closedX.tensor.map (Prod.mkHom (d.pull.map k) (𝟙 M))) ≫
          (d.projection L M).hom =
        (d.projection K M).hom ≫ d.closedY.tensor.map (Prod.mkHom k (𝟙 _)))
    (M : C.{u, u} l Ω X s) : IsIso (d.epsilon l Ω M) := by
  let E := fun K : C.{u, u} l Ω S s ↦
    (d.closedY.transpose K (F.F.obj M) unit).symm.trans
      ((Iso.homCongr (d.projection K M) (Iso.refl unit)).symm.trans
        ((F.adjunction.homEquiv _ unit).trans
          ((d.closedX.transpose _ M (F.G.obj unit)).trans (d.adjunction.homEquiv K _))))
  have hnE : ∀ {K L : C.{u, u} l Ω S s} (k : K ⟶ L)
      (g : L ⟶ d.homY.obj (op (F.F.obj M), unit)),
      E K (k ≫ g) = k ≫ E L g := by
    intro K L k g
    dsimp only [E, Equiv.trans_apply]
    simp only [Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
      Iso.refl_inv, Category.comp_id]
    rw [transpose_symm_left]
    rw [← Category.assoc, ← hn M k, Category.assoc]
    rw [Adjunction.homEquiv_naturality_left, transpose_left,
      Adjunction.homEquiv_naturality_left]
  let e := isoOfNaturalHomEquiv E hnE
  have he : e.hom = d.epsilon l Ω M := by
    change E _ (𝟙 _) = _
    dsimp only [E, Equiv.trans_apply]
    simp only [Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom,
      Iso.refl_inv, Category.comp_id,
      transpose_symm_id]
    simp only [StageData.epsilon, hd, Iso.refl_hom]
    change _ = (d.adjunction.homEquiv _ _)
      (d.closedX.transpose _ _ _ ((F.adjunction.homEquiv _ _)
        ((d.projection _ M).hom ≫ d.closedY.evaluation _ unit) ≫ 𝟙 _))
    rw [Category.comp_id]
  rw [← he]
  exact e.isIso_hom

end Stage

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Global Verdier duality in the full bounded constructible point category at all
four coefficient stages. Its natural isomorphism has the actual projection/evaluation
transpose as components. ScalarConclusion gives its finite reduction and scalar
extension squares, and StageConclusion gives the contravariant shift square.
For the coefficient unit, Conclusion.constant is the component of the very same
isomorphism followed by the tensor/Hom unit evaluation.

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-global-duality, order 2507
(blueprint: sk-thm-sf-global-duality).

Proof plan:
1. By thm-sf-ctf-stability, the coefficient unit, omega_X, D_X K, Ra_! K and
   Ra_* D_X K all belong to the finite-Tor constructible categories. This applies
   at finite, completed integral, rational and common coefficient stages.
2. Specialize sk-thm-sf-verdier-exchange to the structure morphism X to Spec k.
   Its exceptional adjunction is the unconditional constructible adjunction.
3. Normalize the exceptional adjoint of the point identity by its counit, giving
   omega_s = Lambda_s. Specialize StageData to the literal identity adjunction;
   its epsilon is the canonical coefficient-dual-to-Verdier-sections arrow.
4. By lem-sf-point-fibre-derived-tensor and lem-weil-point-fibre-equivalence,
   point internal-Hom evaluation is the tensor/Hom transpose of evaluated
   tensor evaluation. Testing against Lambda[-r] shows it is invertible.
5. The exchange squares and the point sections reduction and scalar-extension
   squares (lem-pod-point-sections-derived-reduction and
   lem-weil-point-sections-scalar-extension) give the coefficient squares.
   Signed Hom comparisons give the shift square, with the opposite shift.
6. At K = Lambda_X, Hom(Lambda_X, omega_X) is omega_X by the unitor and
   tensor/Hom triangles. Compose this evaluation with the same epsilon component.
-/
theorem global_verdier_duality (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [Smooth (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [GeometricallyConnected (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : X.IsPureDimension d)
    (_hX : GeometricAlternative D (Over.mk (X ↘ Spec (.of D.k)))) :
    Assertion l Ω D hl X := by
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  have hExchange := VerdierExchange.verdier_exchange l Ω D hl (X ↘ Spec (.of D.k))
  intro A c
  obtain ⟨N⟩ := identity_normalization l Ω D hl X hExchange A c
  have h : ∀ s M, IsIso ((N.stage s).epsilon l Ω M) := fun s M ↦
    epsilon_isIso l Ω (N.stage s) (N.dualizing s) (N.projection_naturality s) M
  let U := fun s ↦ closedUnitIso (N.stage s).closedX ((A.ring.operation c s).G.obj (N.unit s))
  let C : ∀ s, Conclusion l Ω (N.stage s) := fun s ↦ {
    exchange := (N.maps s).toConclusion l Ω (h s)
    dualizing := N.dualizing s
    unitIso := U s
    evaluation := closedUnitIso_hom _ _
    coevaluation := closedUnitIso_inv _ _
    constant := ((N.maps s).toConclusion l Ω (h s)).epsilon.app
      (op (N.stage s).closedX.monoidal.tensorUnit) ≪≫ (N.stage s).star.mapIso (U s)
    constant_hom := rfl }
  exact ⟨{
    unit := N.unit
    stage := N.stage
    conclusion := C
    ring := N.ring
    projection := N.projection
    ringShifts := fun s ↦ N.ringShifts s (h (s.stage l))
    unitX := N.unitX
    unitY := N.unitY
    unitX_normalized := N.unitX_normalized
    unitY_normalized := N.unitY_normalized
    ringScalar := N.ringScalar h
    rationalization := N.rationalization h
    rationalScalar := N.rationalScalar h
    common := N.common h }⟩

end WeilConjectures.GlobalVerdierDuality
