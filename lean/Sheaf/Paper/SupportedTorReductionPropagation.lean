/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.FiniteCtfTriangulated
import Sheaf.Paper.SfIntegralConstructibleTriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Supported Tor bounds and uniform integral reduction

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, Finite Tor amplitude (2') and Other stages
(blueprint: lem-sf-supported-tor-reduction-propagation).

The records package the specified operations, adjunction maps, and comparisons in the
hypotheses. They do not assume the exceptional Tor bound or construct new operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v c h a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The specified constructible operations and supported triangles, before imposing Tor bounds.
Source: localization proof, (2') (blueprint: lem-sf-supported-tor-reduction-propagation). -/
structure SupportedTorSetup (C Z U : Type c)
    [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] [∀ m : ℤ, (shiftFunctor A m).Additive] [Pretriangulated A]
    (V : C ⥤ A) where
  iPush : Z ⥤ C
  iPull : C ⥤ Z
  jPull : C ⥤ U
  jPush : U ⥤ C
  exceptional : C ⥤ Z
  closedAdjunction : iPull ⊣ iPush
  openAdjunction : jPull ⊣ jPush
  exceptionalAdjunction : iPush ⊣ exceptional
  closed_counit (Q : Z) : IsIso (closedAdjunction.counit.app Q)
  boundary : jPull ⋙ jPush ⋙ V ⟶ exceptional ⋙ iPush ⋙ V ⋙ shiftFunctor A (1 : ℤ)
  distinguished (K : C) :
    Triangle.mk (V.map (exceptionalAdjunction.counit.app K))
      (V.map (openAdjunction.unit.app K)) (boundary.app K) ∈ distTriang A

section Packages
variable {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ m : ℤ, (shiftFunctor A m).Additive] [Pretriangulated A]
  {V : C ⥤ A} (S : SupportedTorSetup C Z U V)

/-- The four assumed interval estimates, excluding the exceptional estimate to be proved.
Source: localization proof, (2') (blueprint: lem-sf-supported-tor-reduction-propagation). -/
def SupportedTorInputBounds (IX : C → ℤ → ℤ → Prop) (IZ : Z → ℤ → ℤ → Prop)
    (IU : U → ℤ → ℤ → Prop) (N : ℤ) : Prop :=
  (∀ (Q : Z) (r s : ℤ), IZ Q r s → IX (S.iPush.obj Q) r s) ∧
  (∀ (K : C) (r s : ℤ), IX K r s → IZ (S.iPull.obj K) r s) ∧
  (∀ (K : C) (r s : ℤ), IX K r s → IU (S.jPull.obj K) r s) ∧
  (∀ (G : U) (r s : ℤ), IU G r s → IX (S.jPush.obj G) r (s + N))

/-- Restriction to the full finite-Tor subcategories, with the same functors, all six
adjunction maps and the original connecting arrow. The zero composite and invertible
exceptional unit are conditional conclusions, not extra input assumptions.
Source: localization proof, Other stages
(blueprint: lem-sf-supported-tor-reduction-propagation). -/
def SupportedTorRestriction (PX : ObjectProperty C) (PZ : ObjectProperty Z)
    (PU : ObjectProperty U) : Prop :=
  ∃ R : SupportedTorSetup PX.FullSubcategory PZ.FullSubcategory PU.FullSubcategory
      (PX.ι ⋙ V),
    R.iPush ⋙ PX.ι = PZ.ι ⋙ S.iPush ∧
    R.iPull ⋙ PZ.ι = PX.ι ⋙ S.iPull ∧
    R.jPull ⋙ PU.ι = PX.ι ⋙ S.jPull ∧
    R.jPush ⋙ PX.ι = PU.ι ⋙ S.jPush ∧
    R.exceptional ⋙ PZ.ι = PX.ι ⋙ S.exceptional ∧
    (∀ Q : PZ.FullSubcategory,
      HEq (PZ.ι.map (R.exceptionalAdjunction.unit.app Q))
        (S.exceptionalAdjunction.unit.app Q.obj)) ∧
    (∀ K : PX.FullSubcategory,
      HEq (PX.ι.map (R.exceptionalAdjunction.counit.app K))
        (S.exceptionalAdjunction.counit.app K.obj)) ∧
    (∀ K : PX.FullSubcategory,
      HEq (PX.ι.map (R.closedAdjunction.unit.app K))
        (S.closedAdjunction.unit.app K.obj)) ∧
    (∀ Q : PZ.FullSubcategory,
      HEq (PZ.ι.map (R.closedAdjunction.counit.app Q))
        (S.closedAdjunction.counit.app Q.obj)) ∧
    (∀ K : PX.FullSubcategory,
      HEq (PX.ι.map (R.openAdjunction.unit.app K)) (S.openAdjunction.unit.app K.obj)) ∧
    (∀ G : PU.FullSubcategory,
      HEq (PU.ι.map (R.openAdjunction.counit.app G)) (S.openAdjunction.counit.app G.obj)) ∧
    (∀ K : PX.FullSubcategory, HEq (R.boundary.app K) (S.boundary.app K.obj)) ∧
    ((∀ G : U, IsZero (S.exceptional.obj (S.jPush.obj G))) →
      ∀ G : PU.FullSubcategory, IsZero (R.exceptional.obj (R.jPush.obj G))) ∧
    ((∀ Q : Z, IsIso (S.exceptionalAdjunction.unit.app Q)) →
      ∀ Q : PZ.FullSubcategory, IsIso (R.exceptionalAdjunction.unit.app Q))
end Packages

section Reductions
variable {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
  {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ m : ℤ, (shiftFunctor A m).Additive] [Pretriangulated A]
  {V : C ⥤ A} (S : SupportedTorSetup C Z U V)
  {C' Z' U' : Type c} [Category.{h} C'] [Category.{h} Z'] [Category.{h} U']
  {A' : Type a} [Category.{b} A'] [Preadditive A'] [HasZeroObject A']
  [HasShift A' ℤ] [∀ m : ℤ, (shiftFunctor A' m).Additive] [Pretriangulated A']
  {V' : C' ⥤ A'} (T : SupportedTorSetup C' Z' U' V')

/-- The supplied reduction identifications of all five operations. Each adjunction's
unit and counit are preserved using those same identifications.
Source: localization proof, Other stages
(blueprint: lem-sf-supported-tor-reduction-propagation). -/
structure SupportedTorReduction (FX : C ⥤ C') (FZ : Z ⥤ Z') (FU : U ⥤ U') where
  iPush : FZ ⋙ T.iPush ≅ S.iPush ⋙ FX
  iPull : FX ⋙ T.iPull ≅ S.iPull ⋙ FZ
  jPull : FX ⋙ T.jPull ≅ S.jPull ⋙ FU
  jPush : FU ⋙ T.jPush ≅ S.jPush ⋙ FX
  exceptional : FX ⋙ T.exceptional ≅ S.exceptional ⋙ FZ
  closed_unit (K : C) :
    T.closedAdjunction.unit.app (FX.obj K) ≫ T.iPush.map (iPull.hom.app K) ≫
      iPush.hom.app (S.iPull.obj K) = FX.map (S.closedAdjunction.unit.app K)
  closed_counit (Q : Z) :
    T.iPull.map (iPush.hom.app Q) ≫ iPull.hom.app (S.iPush.obj Q) ≫
      FZ.map (S.closedAdjunction.counit.app Q) = T.closedAdjunction.counit.app (FZ.obj Q)
  open_unit (K : C) :
    T.openAdjunction.unit.app (FX.obj K) ≫ T.jPush.map (jPull.hom.app K) ≫
      jPush.hom.app (S.jPull.obj K) = FX.map (S.openAdjunction.unit.app K)
  open_counit (G : U) :
    T.jPull.map (jPush.hom.app G) ≫ jPull.hom.app (S.jPush.obj G) ≫
      FU.map (S.openAdjunction.counit.app G) = T.openAdjunction.counit.app (FU.obj G)
  exceptional_unit (Q : Z) :
    T.exceptionalAdjunction.unit.app (FZ.obj Q) ≫ T.exceptional.map (iPush.hom.app Q) ≫
      exceptional.hom.app (S.iPush.obj Q) = FZ.map (S.exceptionalAdjunction.unit.app Q)
  exceptional_counit (K : C) :
    T.iPush.map (exceptional.hom.app K) ≫ iPush.hom.app (S.exceptional.obj K) ≫
      FX.map (S.exceptionalAdjunction.counit.app K) =
        T.exceptionalAdjunction.counit.app (FX.obj K)
end Reductions

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Notational specialization of the recorded finite constructible category, at exponent n+1.
Source: localization proof, (2') (blueprint: lem-sf-supported-tor-reduction-propagation). -/
abbrev SupportedTorFiniteCategory (n : ℕ) (Y : Scheme.{u}) :=
  (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y).FullSubcategory

/-- The specified finite constructible operations, retaining the ambient derived triangles.
Source: localization proof, (2') (blueprint: lem-sf-supported-tor-reduction-propagation). -/
abbrev SupportedTorFiniteSetup (n : ℕ) (X Z U : Scheme.{u}) :=
  SupportedTorSetup (SupportedTorFiniteCategory l E n X)
    (SupportedTorFiniteCategory l E n Z) (SupportedTorFiniteCategory l E n U)
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι

/-- The specified integral constructible operations on the actual completed coefficient sheaf.
Source: localization proof, Other stages
(blueprint: lem-sf-supported-tor-reduction-propagation). -/
abbrev SupportedTorIntegralSetup (X Z U : Scheme.{u}) :=
  SupportedTorSetup (sfIntegralConstructibleCategory l E X)
    (sfIntegralConstructibleCategory l E Z) (sfIntegralConstructibleCategory l E U)
    (sfIntegralConstructible l E X).ι

/-- The explicitly specified residue coefficient kappa = A_(n+1)/(varpi).
Source: localization proof, (2') (blueprint: lem-sf-supported-tor-reduction-propagation). -/
abbrev supportedTorResidue (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1) ⧸ Ideal.span
    ({Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionRing l E (n + 1)))

/-- Residue-tensor cohomological bounds, on every K-flat representative of the given object.
This uses the existing derived tensor along the actual quotient map A_(n+1) -> kappa.
Source: localization proof, (2') (blueprint: lem-sf-supported-tor-reduction-propagation). -/
def SupportedTorResidueBound (n : ℕ) (Y : Scheme.{u})
    (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
    (r s : ℤ) : Prop :=
  ∀ (L P : CochainComplex (proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))) ℤ),
    Nonempty (DerivedCategory.Q.obj L ≅ K) →
    ∀ (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat
        (R := proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))) P)
      (q : ℤ), q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (derivedTensorRing Y (Padic.coefficientExtensionRing l E (n + 1))
          (supportedTorResidue l E n) (Ideal.Quotient.mk _) L P f hf hP))
end Coefficients

private theorem tor_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory Y A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude Y A K a b) : HasProEtaleTorAmplitude Y A L a b := by
  refine ⟨h.1, ?_⟩
  rintro N P ⟨q⟩ f hf hP M i hi
  exact h.2 N P ⟨q ≪≫ e.symm⟩ f hf hP M i hi

private theorem tor_mono (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {K : proEtaleDerivedCategory Y A} {a b c d : ℤ}
    (h : HasProEtaleTorAmplitude Y A K a b) (hc : c ≤ a) (hd : b ≤ d) :
    HasProEtaleTorAmplitude Y A K c d := by
  refine ⟨hc.trans (h.1.trans hd), ?_⟩
  intro N P hN f hf hP M i hi
  apply h.2 N P hN f hf hP M i
  exact hi.elim (fun hi ↦ Or.inl (hi.trans_le hc)) (fun hi ↦ Or.inr (hd.trans_lt hi))

private theorem tor_residue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (Y : Scheme.{u})
    (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
    (a b : ℤ) (h : HasProEtaleTorAmplitude Y _ K a b) :
    SupportedTorResidueBound l E n Y K a b := by
  intro L P hL f hf hP q hq
  exact h.2 L P hL f hf hP _ q hq

private def restrict_adj {C D : Type c} [Category.{h} C] [Category.{h} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R) (hL : ∀ K, P K → Q (L.obj K)) (hR : ∀ K, Q K → P (R.obj K)) :
    Q.lift (P.ι ⋙ L) (fun K ↦ hL K.obj K.property) ⊣
      P.lift (Q.ι ⋙ R) (fun K ↦ hR K.obj K.property) where
  unit :=
    { app := fun K ↦ ObjectProperty.homMk (adj.unit.app K.obj)
      naturality := fun _ _ f ↦ ObjectProperty.hom_ext P (adj.unit.naturality f.hom) }
  counit :=
    { app := fun K ↦ ObjectProperty.homMk (adj.counit.app K.obj)
      naturality := fun _ _ f ↦ ObjectProperty.hom_ext Q (adj.counit.naturality f.hom) }
  left_triangle_components K := ObjectProperty.hom_ext Q (adj.left_triangle_components K.obj)
  right_triangle_components K := ObjectProperty.hom_ext P (adj.right_triangle_components K.obj)

private theorem restrict_zero {C : Type c} [Category.{h} C] (P : ObjectProperty C)
    (K : P.FullSubcategory) (hK : IsZero K.obj) : IsZero K := by
  constructor
  · intro L
    exact ⟨⟨⟨ObjectProperty.homMk (hK.to_ L.obj)⟩,
      fun f ↦ ObjectProperty.hom_ext P (hK.eq_of_src _ _)⟩⟩
  · intro L
    exact ⟨⟨⟨ObjectProperty.homMk (hK.from_ L.obj)⟩,
      fun f ↦ ObjectProperty.hom_ext P (hK.eq_of_tgt _ _)⟩⟩

private theorem restrict_setup
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] [∀ m : ℤ, (shiftFunctor A m).Additive] [Pretriangulated A]
    {V : C ⥤ A} (S : SupportedTorSetup C Z U V)
    (PX : ObjectProperty C) (PZ : ObjectProperty Z) (PU : ObjectProperty U)
    (hi : ∀ Q, PZ Q → PX (S.iPush.obj Q))
    (hp : ∀ K, PX K → PZ (S.iPull.obj K))
    (hj : ∀ K, PX K → PU (S.jPull.obj K))
    (hr : ∀ G, PU G → PX (S.jPush.obj G))
    (he : ∀ K, PX K → PZ (S.exceptional.obj K)) :
    SupportedTorRestriction S PX PZ PU := by
  let R : SupportedTorSetup PX.FullSubcategory PZ.FullSubcategory PU.FullSubcategory
      (PX.ι ⋙ V) :=
    { iPush := PX.lift (PZ.ι ⋙ S.iPush) (fun Q ↦ hi Q.obj Q.property)
      iPull := PZ.lift (PX.ι ⋙ S.iPull) (fun K ↦ hp K.obj K.property)
      jPull := PU.lift (PX.ι ⋙ S.jPull) (fun K ↦ hj K.obj K.property)
      jPush := PX.lift (PU.ι ⋙ S.jPush) (fun G ↦ hr G.obj G.property)
      exceptional := PZ.lift (PX.ι ⋙ S.exceptional) (fun K ↦ he K.obj K.property)
      closedAdjunction := restrict_adj PX PZ _ _ S.closedAdjunction hp hi
      openAdjunction := restrict_adj PX PU _ _ S.openAdjunction hj hr
      exceptionalAdjunction := restrict_adj PZ PX _ _ S.exceptionalAdjunction hi he
      closed_counit := fun Q ↦ by
        apply (ObjectProperty.isIso_hom_iff _).1
        exact S.closed_counit Q.obj
      boundary :=
        { app := fun K ↦ S.boundary.app K.obj
          naturality := fun _ _ f ↦ S.boundary.naturality f.hom }
      distinguished := fun K ↦ S.distinguished K.obj }
  refine ⟨R, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q; rfl
  · intro K; rfl
  · intro K; rfl
  · intro Q; rfl
  · intro K; rfl
  · intro G; rfl
  · intro K; rfl
  · intro hz G
    exact restrict_zero PZ _ (hz G.obj)
  · intro hu Q
    apply (ObjectProperty.isIso_hom_iff _).1
    exact hu Q.obj

private theorem finite_exceptional
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (X Z U : Scheme.{u}) (S : SupportedTorFiniteSetup l E n X Z U)
    (N : ℕ) (h : SupportedTorInputBounds S
      (fun K ↦ HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (N : ℤ))
    (K : SupportedTorFiniteCategory l E n X) (a b : ℤ)
    (hK : HasProEtaleTorAmplitude X _ K.obj a b) :
    HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1))
        (S.exceptional.obj K).obj a (b + N + 1) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        (S.iPush.obj (S.exceptional.obj K)).obj a (b + N + 1) := by
  have hC := h.2.2.2 _ a b (h.2.2.1 _ a b hK)
  have hshift := (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).2.2.1
    _ a (b + N) (-1) hC
  let T := Triangle.mk
    ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι.map
      (S.exceptionalAdjunction.counit.app K))
    ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι.map
      (S.openAdjunction.unit.app K)) (S.boundary.app K)
  have hF := (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).2.2.2
    T.invRotate a (b + N + 1) (inv_rot_of_distTriang T (S.distinguished K))
    (tor_mono X _ hshift (by omega) (by omega))
    (tor_mono X _ hK le_rfl (by omega))
  have hc := S.closed_counit (S.exceptional.obj K)
  have he := tor_iso Z _
    ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι.mapIso
      (asIso (S.closedAdjunction.counit.app (S.exceptional.obj K))))
    (h.2.1 _ _ _ hF)
  exact ⟨he, hF⟩

private theorem integral_ctf
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (finiteTorConstructibleIntegral l E Y) ∧
      ObjectProperty.IsTriangulated (finiteTorConstructibleIntegral l E Y) := by
  let : Zero (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    HasZeroObject.zero' _
  let P := sfIntegralConstructible l E Y
  let Q : ObjectProperty (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj K) a b
  have : P.IsClosedUnderIsomorphisms := sfIntegralConstructible_isClosedUnderIsomorphisms _ _ _
  have : P.IsTriangulated := sfIntegralConstructible_isTriangulated _ _ _
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    rintro K L e ⟨a, b, hab, hK⟩
    exact ⟨a, b, hab, fun n ↦ tor_iso Y _
      ((scalarReductionDerivedExtension.{u, u} l E Y n).mapIso e) (hK n)⟩⟩
  have : Q.ContainsZero := ⟨0, isZero_zero _, 0, 0, le_rfl, by
    intro n
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let F := scalarReductionDerivedExtension.{u, u} l E Y n
    obtain ⟨hshift, htri⟩ :=
      (scalarReductionDerivedExistence.{u, u} l E Y n).choose_spec.choose_spec.2.1
    let : F.CommShift ℤ := hshift
    have : F.IsTriangulated := htri
    have hz := F.map_isZero (isZero_zero _)
    let Z := F.obj 0
    let S : ObjectProperty (proEtaleDerivedCategory Y A) :=
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y A K
    obtain ⟨hSi, hSt, hs, _⟩ := finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Y
    have : S.IsClosedUnderIsomorphisms := hSi
    have : S.IsTriangulated := hSt
    obtain ⟨a, b, h⟩ := (S.prop_of_isZero hz).2
    refine ⟨le_rfl, ?_⟩
    intro L R hL f hf hR M i _hi
    have ht := hs Z a b (b - i + 1) h
    have hzshift := (shiftFunctor _ (b - i + 1)).map_isZero hz
    have ht' := tor_iso Y A (hzshift.iso hz) ht
    exact ht'.2 L R hL f hf hR M i (Or.inr (by omega))⟩
  have : Q.IsStableUnderShift ℤ := ⟨fun m ↦ ⟨by
    rintro K ⟨a, b, hab, hK⟩
    refine ⟨a - m, b - m, by omega, ?_⟩
    intro n
    let F := scalarReductionDerivedExtension.{u, u} l E Y n
    obtain ⟨hshift, htri⟩ :=
      (scalarReductionDerivedExistence.{u, u} l E Y n).choose_spec.choose_spec.2.1
    let : F.CommShift ℤ := hshift
    have : F.IsTriangulated := htri
    have ht := (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Y).2.2.1
      (F.obj K) a b m (hK n)
    exact tor_iso Y _ ((F.commShiftIso m).app K).symm ht⟩⟩
  have : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro T hT h₁ h₃
    obtain ⟨a, b, hab, h₁⟩ := h₁
    obtain ⟨c, d, hcd, h₃⟩ := h₃
    refine ⟨min a c, max b d, (min_le_left _ _).trans (hab.trans (le_max_left _ _)), ?_⟩
    intro n
    let F := scalarReductionDerivedExtension.{u, u} l E Y n
    obtain ⟨hshift, htri⟩ :=
      (scalarReductionDerivedExistence.{u, u} l E Y n).choose_spec.choose_spec.2.1
    let : F.CommShift ℤ := hshift
    have : F.IsTriangulated := htri
    exact (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Y).2.2.2
      (F.mapTriangle.obj T) _ _ (F.map_distinguished T hT)
      (tor_mono Y _ (h₁ n) (min_le_left _ _) (le_max_left _ _))
      (tor_mono Y _ (h₃ n) (min_le_right _ _) (le_max_right _ _)))
  have : Q.IsTriangulated := {}
  exact ⟨inferInstanceAs (P ⊓ Q).IsClosedUnderIsomorphisms,
    inferInstanceAs (P ⊓ Q).IsTriangulated⟩

/-- Quantitative supported Tor bounds and restriction of the given triangles and adjunctions.
The input functors act on the actual constructible categories; the operation identifications
use the recorded finite and completed operations. The reduction squares preserve both maps
of every adjunction. Level n means exponent n+1 throughout, including n=0.

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, (2') and Other stages
(blueprint: lem-sf-supported-tor-reduction-propagation).

Proof:
1. Fix a finite level. Set F = i_* J K and C = Rj_* j^* K. The assumed open bounds
put C in [a,b+N]. The shift formula of lem-weil-finite-ctf-triangulated puts C[-1]
in [a+1,b+N+1]. Inversely rotate the given supported triangle to C[-1] -> F -> K.
2. Enlarge both outside intervals to [a,b+N+1], since N is nonnegative. The
common-interval triangle clause of lem-weil-finite-ctf-triangulated gives F this
interval. This tests every module sheaf, without assuming the residue is flat or perfect.
3. Apply the interval-preserving i^* and its invertible closed counit to identify i^*F
with J K. Specialize the all-module Tor test to the actual quotient kappa to get both
residue-tensor cohomological bounds, on every K-flat representative.
4. For each integral operation use its given reduction comparison. The finite estimates
apply at every n with the same N, yielding the stated uniform reduction intervals.
Constructibility of the outputs is already included in their specified codomains.
5. Finite ctf is triangulated by lem-weil-finite-ctf-triangulated. Integrally start from
lem-weil-integral-constructible-triangulated; the recorded scalar reduction has its
specified exact structure. Zero and isomorphisms preserve uniform Tor bounds; a shift
by m changes every interval to [a-m,b-m], and the finite triangulation theorem gives
the uniform interval hull for a distinguished triangle. Thus the integral
finite-Tor predicate is a replete triangulated subcategory as well.
6. The bounds put every supported vertex in these full subcategories. Lift the given
functors and all six adjunction maps by fullness; their identities and distinguished
triangles are unchanged. The same argument restricts a zero exceptional-open composite
and an invertible exceptional unit. At either field stage the ctf notation is the
constructible category itself by def-weil-finite-tor-amplitude, so restriction is identity.
-/
theorem supported_tor_reduction_propagation
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : k))
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ)
    (F : ∀ n : ℕ, SupportedTorFiniteSetup l E n X Z U)
    (I : SupportedTorIntegralSetup l E X Z U)
    (_finiteOperations : ∀ n : ℕ,
      Nonempty ((F n).iPush ⋙
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ⋙
          proEtaleConstantDerivedDirectImage i
          (Padic.coefficientExtensionRing l E (n + 1))) ∧
      Nonempty ((F n).iPull ⋙
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ≅
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
          finiteDerivedPullback l E n i) ∧
      Nonempty ((F n).jPull ⋙
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι ≅
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
          finiteDerivedPullback l E n j) ∧
      Nonempty ((F n).jPush ⋙
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
        (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι ⋙
          proEtaleConstantDerivedDirectImage j
          (Padic.coefficientExtensionRing l E (n + 1))))
    (_integralOperations :
      Nonempty ((I).iPush ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i) ∧
      Nonempty ((I).iPull ⋙ (sfIntegralConstructible l E Z).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E i) ∧
      Nonempty ((I).jPull ⋙ (sfIntegralConstructible l E U).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E j) ∧
      Nonempty ((I).jPush ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E U).ι ⋙ sfCompletedDerivedDirectImage l E j))
    (_reductions : ∀ n : ℕ, Nonempty (SupportedTorReduction I (F n)
      ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).lift
        ((sfIntegralConstructible l E X).ι ⋙ scalarReductionDerivedExtension.{u, u} l E X n)
        (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1))
      ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).lift
        ((sfIntegralConstructible l E Z).ι ⋙ scalarReductionDerivedExtension.{u, u} l E Z n)
        (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1))
      ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).lift
        ((sfIntegralConstructible l E U).ι ⋙ scalarReductionDerivedExtension.{u, u} l E U n)
        (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1))))
    (N : ℕ)
    (hfinite : ∀ n : ℕ, SupportedTorInputBounds (F n)
      (fun K ↦ HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (N : ℤ)) :
    (∀ (n : ℕ) (K : SupportedTorFiniteCategory l E n X) (a b : ℤ),
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K.obj a b →
        HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1))
          (((F n).exceptional.obj K).obj) a (b + N + 1) ∧
        SupportedTorResidueBound l E n X
          (((F n).iPush.obj ((F n).exceptional.obj K)).obj) a (b + N + 1) ∧
        SupportedTorResidueBound l E n Z (((F n).exceptional.obj K).obj) a (b + N + 1)) ∧
    SupportedTorInputBounds I
      (fun K a b ↦ a ≤ b ∧ ∀ n : ℕ,
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) a b)
      (fun K a b ↦ a ≤ b ∧ ∀ n : ℕ,
        HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E Z n).obj K.obj) a b)
      (fun K a b ↦ a ≤ b ∧ ∀ n : ℕ,
        HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E U n).obj K.obj) a b) (N : ℤ) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X) (a b : ℤ),
      (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) a b) →
      ∀ n : ℕ, HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E Z n).obj
          (I.exceptional.obj K).obj) a (b + N + 1)) ∧
    (∀ n : ℕ, SupportedTorRestriction (F n)
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K.obj)
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Z K.obj)
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) U K.obj)) ∧
    SupportedTorRestriction I
      (fun K ↦ finiteTorConstructibleIntegral l E X K.obj)
      (fun K ↦ finiteTorConstructibleIntegral l E Z K.obj)
      (fun K ↦ finiteTorConstructibleIntegral l E U K.obj) ∧
    (∀ n : ℕ,
      ObjectProperty.IsClosedUnderIsomorphisms
        (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X) ∧
      ObjectProperty.IsTriangulated
        (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X)) ∧
    (ObjectProperty.IsClosedUnderIsomorphisms (finiteTorConstructibleIntegral l E X) ∧
      ObjectProperty.IsTriangulated (finiteTorConstructibleIntegral l E X)) ∧
    (∀ n : ℕ,
      ObjectProperty.IsClosedUnderIsomorphisms
        (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Z) ∧
      ObjectProperty.IsTriangulated
        (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Z)) ∧
    (ObjectProperty.IsClosedUnderIsomorphisms (finiteTorConstructibleIntegral l E Z) ∧
      ObjectProperty.IsTriangulated (finiteTorConstructibleIntegral l E Z)) ∧
    (∀ n : ℕ,
      ObjectProperty.IsClosedUnderIsomorphisms
        (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) U) ∧
      ObjectProperty.IsTriangulated
        (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) U)) ∧
    (ObjectProperty.IsClosedUnderIsomorphisms (finiteTorConstructibleIntegral l E U) ∧
      ObjectProperty.IsTriangulated (finiteTorConstructibleIntegral l E U)) ∧
    (∀ Y : Scheme.{u},
      finiteTorFieldCoefficientCategory (sfRationalConstructibleCategory l E Y) =
        sfRationalConstructibleCategory l E Y) ∧
    (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
      (Y : Scheme.{u}), finiteTorFieldCoefficientCategory
          (generalAlgebraicallyClosedConstructibleCategory l Ω Y) =
        generalAlgebraicallyClosedConstructibleCategory l Ω Y) := by
  classical
  have hfin (n : ℕ) (K : SupportedTorFiniteCategory l E n X) (a b : ℤ)
      (hK : HasProEtaleTorAmplitude X _ K.obj a b) :=
    finite_exceptional l E n X Z U (F n) N (hfinite n) K a b hK
  let RX (n : ℕ) :=
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).lift
      ((sfIntegralConstructible l E X).ι ⋙ scalarReductionDerivedExtension.{u, u} l E X n)
      (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1)
  let RZ (n : ℕ) :=
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).lift
      ((sfIntegralConstructible l E Z).ι ⋙ scalarReductionDerivedExtension.{u, u} l E Z n)
      (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1)
  let RU (n : ℕ) :=
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).lift
      ((sfIntegralConstructible l E U).ι ⋙ scalarReductionDerivedExtension.{u, u} l E U n)
      (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1)
  let B (Y : Scheme.{u}) (K : sfIntegralConstructibleCategory l E Y) (a b : ℤ) :=
    a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj K.obj) a b
  have hb : SupportedTorInputBounds I (B X) (B Z) (B U) (N : ℤ) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro Q a b hQ
      refine ⟨hQ.1, fun n ↦ ?_⟩
      let d : SupportedTorReduction I (F n) (RX n) (RZ n) (RU n) :=
        Classical.choice (_reductions n)
      exact tor_iso X _
        ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι.mapIso
          (d.iPush.app Q)) ((hfinite n).1 ((RZ n).obj Q) a b (hQ.2 n))
    · intro K a b hK
      refine ⟨hK.1, fun n ↦ ?_⟩
      let d : SupportedTorReduction I (F n) (RX n) (RZ n) (RU n) :=
        Classical.choice (_reductions n)
      exact tor_iso Z _
        ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι.mapIso
          (d.iPull.app K)) ((hfinite n).2.1 ((RX n).obj K) a b (hK.2 n))
    · intro K a b hK
      refine ⟨hK.1, fun n ↦ ?_⟩
      let d : SupportedTorReduction I (F n) (RX n) (RZ n) (RU n) :=
        Classical.choice (_reductions n)
      exact tor_iso U _
        ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι.mapIso
          (d.jPull.app K)) ((hfinite n).2.2.1 ((RX n).obj K) a b (hK.2 n))
    · intro G a b hG
      refine ⟨by have := hG.1; omega, fun n ↦ ?_⟩
      let d : SupportedTorReduction I (F n) (RX n) (RZ n) (RU n) :=
        Classical.choice (_reductions n)
      exact tor_iso X _
        ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι.mapIso
          (d.jPush.app G)) ((hfinite n).2.2.2 ((RU n).obj G) a b (hG.2 n))
  have he (K : sfIntegralConstructibleCategory l E X) (a b : ℤ)
      (hK : ∀ n : ℕ, HasProEtaleTorAmplitude X _
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) a b) (n : ℕ) :
      HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E Z n).obj
          (I.exceptional.obj K).obj) a (b + N + 1) := by
    let d : SupportedTorReduction I (F n) (RX n) (RZ n) (RU n) :=
      Classical.choice (_reductions n)
    exact tor_iso Z _
      ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι.mapIso
        (d.exceptional.app K)) (hfin n ((RX n).obj K) a b (hK n)).1
  refine ⟨?_, hb, he, ?_, ?_, ?_, integral_ctf l E X, ?_, integral_ctf l E Z,
    ?_, integral_ctf l E U, fun _ ↦ rfl, fun _ _ _ _ _ ↦ rfl⟩
  · intro n K a b hK
    obtain ⟨hJ, hF⟩ := hfin n K a b hK
    exact ⟨hJ, tor_residue l E n X _ _ _ hF, tor_residue l E n Z _ _ _ hJ⟩
  · intro n
    apply restrict_setup (F n)
    · rintro Q ⟨_, a, b, hQ⟩
      exact ⟨((F n).iPush.obj Q).property, a, b, (hfinite n).1 Q a b hQ⟩
    · rintro K ⟨_, a, b, hK⟩
      exact ⟨((F n).iPull.obj K).property, a, b, (hfinite n).2.1 K a b hK⟩
    · rintro K ⟨_, a, b, hK⟩
      exact ⟨((F n).jPull.obj K).property, a, b, (hfinite n).2.2.1 K a b hK⟩
    · rintro G ⟨_, a, b, hG⟩
      exact ⟨((F n).jPush.obj G).property, a, b + N, (hfinite n).2.2.2 G a b hG⟩
    · rintro K ⟨_, a, b, hK⟩
      exact ⟨((F n).exceptional.obj K).property, a, b + N + 1, (hfin n K a b hK).1⟩
  · apply restrict_setup I
    · rintro Q ⟨_, a, b, hQ⟩
      exact ⟨(I.iPush.obj Q).property, a, b, hb.1 Q a b hQ⟩
    · rintro K ⟨_, a, b, hK⟩
      exact ⟨(I.iPull.obj K).property, a, b, hb.2.1 K a b hK⟩
    · rintro K ⟨_, a, b, hK⟩
      exact ⟨(I.jPull.obj K).property, a, b, hb.2.2.1 K a b hK⟩
    · rintro G ⟨_, a, b, hG⟩
      exact ⟨(I.jPush.obj G).property, a, b + N, hb.2.2.2 G a b hG⟩
    · rintro K ⟨_, a, b, hab, hK⟩
      exact ⟨(I.exceptional.obj K).property, a, b + N + 1,
        by omega, he K a b hK⟩
  · intro n
    exact ⟨(finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).1,
      (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).2.1⟩
  · intro n
    exact ⟨(finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Z).1,
      (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Z).2.1⟩
  · intro n
    exact ⟨(finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) U).1,
      (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) U).2.1⟩

end WeilConjectures
