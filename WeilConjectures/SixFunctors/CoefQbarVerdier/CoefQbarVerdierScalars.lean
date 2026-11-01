/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor
public import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory

/-! # Scalar formulas for the common-stage dual

Source: thm-coef-qbar-verdier, coefficient-transport paragraph.
(blueprint: lem-coef-qbar-verdier-scalars-component)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w a b
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.StageSystem

private theorem scalar_conjugate {C : Type a} [Category.{b} C] [Preadditive C]
    {R : Type w} [Semiring R] [Linear R C] {A B C₀ D : C}
    (f : A ⟶ B) (g : B ⟶ C₀) (h : C₀ ⟶ D) (r : R) :
    f ≫ (r • g) ≫ h = r • (f ≫ g ≫ h) := by
  rw [Linear.smul_comp, Linear.comp_smul]

private theorem scalar_inclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {C : Padic.FiniteCoefficientFields l Ω → Type a}
    [∀ E, Category.{b} (C E)] [∀ E, Preadditive (C E)] [∀ E, Linear E.val (C E)]
    [IsDirectedOrder (Padic.FiniteCoefficientFields l Ω)]
    (S : StageSystem C) (hS : QbarScalarCompatible l Ω S)
    (E : Padic.FiniteCoefficientFields l Ω) {K L : C E} (f : K ⟶ L) (c : E.val) :
    qbarScalarHom l Ω S hS (c : Ω) ((S.ι E).map f) = (S.ι E).map (c • f) := by
  change qbarScalarHom l Ω S hS (c : Ω)
    (PairCategory.mkHom (X := ⟨E, K⟩) (Y := ⟨E, L⟩) E le_rfl le_rfl
      ((S.T le_rfl).map f)) = _
  rw [qbarScalarHom_mkHom l Ω S hS (c : Ω) E le_rfl le_rfl _ E le_rfl c.property]
  have ht := S.tr_map (hi := (le_rfl : E ≤ E)) (le_rfl : E ≤ E) f
  change S.tr (hi := (le_rfl : E ≤ E)) (hj := (le_rfl : E ≤ E))
    (le_rfl : E ≤ E) ((S.T (le_rfl : E ≤ E)).map f) = _ at ht
  rw [ht]
  exact congrArg
    (fun g ↦ PairCategory.mkHom (X := ⟨E, K⟩) (Y := ⟨E, L⟩) E le_rfl le_rfl g)
    (hS (E := E) (F := E) le_rfl c f).symm

private theorem contravariant_scalar
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {C : Padic.FiniteCoefficientFields l Ω → Type a}
    [∀ E, Category.{b} (C E)] [∀ E, Preadditive (C E)] [∀ E, Linear E.val (C E)]
    [IsDirectedOrder (Padic.FiniteCoefficientFields l Ω)]
    (S : StageSystem C) (F : S.opposite.Morphism S)
    (hF : ∀ E (K M : C E) (f : K ⟶ M) (c : E.val),
      (F.Φ E).map (c • f).op = c • (F.Φ E).map f.op)
    (hS : QbarScalarCompatible l Ω S)
    {K M : S.PairCategory} (f : K ⟶ M) (c : Ω) :
    (S.pairUnopFunctor ⋙ F.functor).map (qbarScalarHom l Ω S hS c f).op =
      qbarScalarHom l Ω S hS c ((S.pairUnopFunctor ⋙ F.functor).map f.op) := by
  induction f using PairCategory.hom_induction with
  | h L hK hM f =>
    let N := Padic.finiteCoefficientCompositum l Ω L (qbarScalarField l Ω c)
    let h : L ≤ N := ((Padic.finiteCoefficientFields_properties l Ω).1 _ _).1
    let hc : c ∈ N.val := ((Padic.finiteCoefficientFields_properties l Ω).1 _ _).2
      (qbarScalarField_mem l Ω c)
    change PairCategory.mkHom (X := F.functor.obj (S.opPair M))
      (Y := F.functor.obj (S.opPair K)) N (hM.trans h) (hK.trans h)
        (F.mapAt ((⟨c, hc⟩ : N.val) • S.tr h f).op) =
      PairCategory.mkHom (X := F.functor.obj (S.opPair M))
        (Y := F.functor.obj (S.opPair K)) N (hM.trans h) (hK.trans h)
          ((⟨c, hc⟩ : N.val) • S.tr h
            (F.mapAt (x := op M.obj) (y := op K.obj) (hi := hM) (hj := hK) f.op))
    apply congrArg (PairCategory.mkHom (X := F.functor.obj (S.opPair M))
      (Y := F.functor.obj (S.opPair K)) N (hM.trans h) (hK.trans h))
    erw [F.tr_mapAt]
    have ho : (S.tr h f).op = S.opposite.tr (hi := hM) (hj := hK)
        (x := op M.obj) (y := op K.obj) h f.op := by
      apply Quiver.Hom.unop_inj
      exact (S.opposite_transport (hi := hK) (hj := hM) h f).symm
    erw [← ho]
    dsimp only [Morphism.mapAt]
    erw [hF]
    exact scalar_conjugate _ _ _ (⟨c, hc⟩ : N.val)

end CategoryTheory.StageSystem

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion)

attribute [-instance] intrinsicQbarStageLocalizedLinear in
/-- Omega-linearity and the finite coefficient normalization of the descended dual.
Source: thm-coef-qbar-verdier, coefficient-transport paragraph.
(blueprint: lem-coef-qbar-verdier-scalars-component)

Proof: represent a scalar and a morphism at a common finite stage and apply finite
linearity, then use the intrinsic quotient scalar formula. The beta factors commute
with multiplication since composition is bilinear. For the coefficient normalization,
compute the quotient scalar action at the original field and use semilinearity of
its identity transition. The coefficient and Shrink equivalences identify its scalar
with the displayed element of Omega. These arguments include repeated fields, zero
arrows and the empty scheme. -/
theorem descended_scalar_formulas (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (f : K ⟶ M) (c : Ω),
      (descendedDual D l hl Ω X F hF).map (c • f).op =
        c • (descendedDual D l hl Ω X F hF).map f.op) ∧
    (∀ (E : Index l Ω)
        (K M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
        (f : K ⟶ M) (c : Coefficient.{u} l Ω E),
      (inclusion (Y := X) E).map
        ((sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c •
          (f : (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) ⟶ M)) =
        ((Shrink.algEquiv (Padic l) E.val c : E.val) : Ω) • (inclusion E).map f) := by
  constructor
  · intro K M f c
    rw [(intrinsicQbarLinear_existsUnique l Ω X).exists.choose_spec K M c f,
      (intrinsicQbarLinear_existsUnique l Ω X).exists.choose_spec _ _ c _]
    apply StageSystem.contravariant_scalar
    intro E A B g a
    rw [finiteMorphism_phi]
    exact (F.datum E).linear A B g ((Shrink.algEquiv (Padic l) E.val).symm a)
  · intro E K M f c
    let : Linear E.val (sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) :=
      intrinsicQbarStageLinear l Ω X E
    rw [(intrinsicQbarLinear_existsUnique l Ω X).exists.choose_spec _ _ _ _]
    have hs := StageSystem.scalar_inclusion l Ω
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
      (intrinsicQbarScalarCompatible l Ω X) E f (Shrink.algEquiv (Padic l) E.val c)
    have he : (sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c • f =
        (Shrink.algEquiv (Padic l) E.val c) • f := by
      change (sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c • f =
        (intrinsicQbarStageFieldEquiv l Ω E).symm (Shrink.algEquiv (Padic l) E.val c) • f
      congr 1
      simp [intrinsicQbarStageFieldEquiv]
    rw [he]
    exact hs.symm

end WeilConjectures.CoefQbarVerdier
