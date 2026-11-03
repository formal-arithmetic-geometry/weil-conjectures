/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfAlgebraicallyClosedCoefficients.SfAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientStageNormalization
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.IntrinsicAssociatorShiftSquare
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficientsCondensed

/-! # Common-stage coefficients over arbitrary schemes

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1462;
main-20261015 sec-proetale-coefficients/sk-def-sf-operations, order 1821
(blueprint: def-weil-algebraically-closed-coefficients).

The datum-free intrinsic construction reuses the finite-field interface and its
legacy coefficient transports. Only preservation proofs mention p; choosing zero
there imposes no characteristic on Y. Tensor normalization identifies the resulting
transitions and comparisons with every finite-field specialization. Objects remain
literal pairs, with directed-colimit Hom groups and no Karoubi completion.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures
namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] ScalarLocalization.category

attribute [local irreducible] sfRationalConstructibleLocalization
  sfRationalTriangulationDatum sfRationalScalarExtension
  sfRationalScalarComp sfRationalScalarUnit sfIntegralScalarComp sfIntegralScalarUnit
  sfIntegralOrdinaryComparison

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

private abbrev PairCommon
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {S : StageSystem C} (A B : S.PairCategory) :=
  {L : I // A.stage ≤ L ∧ B.stage ≤ L}
private abbrev PairStageHom
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {S : StageSystem C} (A B : S.PairCategory) (L : PairCommon A B) :=
  (S.T L.property.1).obj A.obj ⟶ (S.T L.property.2).obj B.obj
private theorem generic_coordinates
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (ht : ∀ L M h f, t L M h f = S.tr h f)
    (dt : DirectedSystem (PairStageHom A B) (fun {L M} h ↦ t L M h)) :
    ∃! e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t,
      ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
        AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f := by
  classical
  let q : (A ⟶ B) ≃ _root_.DirectLimit ((PairStageHom A B))
      (fun L M h ↦ t L M h) :=
    { toFun := Quotient.lift
        (fun r : StageSystem.PairCategory.Rep A B ↦
          ⟦⟨⟨r.k, r.hX, r.hY⟩, r.u⟩⟧)
        (by
          rintro r s ⟨N, hr, hs, he⟩
          apply Quotient.sound
          refine ⟨⟨N, r.hX.trans hr, r.hY.trans hr⟩, hr, hs, ?_⟩
          simpa only [ht] using he)
      invFun := Quotient.lift
        (fun r : Σ L : (PairCommon A B), (PairStageHom A B) L ↦
          StageSystem.PairCategory.mkHom r.1.val r.1.property.1 r.1.property.2 r.2)
        (by
          rintro ⟨L, f⟩ ⟨M, g⟩ ⟨N, hL, hM, he⟩
          exact (StageSystem.PairCategory.mkHom_eq_mkHom_iff' f g).2
            ⟨N.val, hL, hM, by simpa only [ht] using he⟩)
      left_inv := by intro f; induction f using Quotient.inductionOn; rfl
      right_inv := by intro f; induction f using Quotient.inductionOn; rfl }
  have : DirectedSystem ((PairStageHom A B))
      (fun L M h ↦ (t L M h).toNatLinearMap) := by
    constructor
    · intro L f
      exact @DirectedSystem.map_self _ _ ((PairStageHom A B))
        (fun {L M} h ↦ t L M h) dt L f
    · intro N M L h k f
      exact @DirectedSystem.map_map _ _ ((PairStageHom A B))
        (fun {L M} h ↦ t L M h) dt N M L h k f
  let e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t := q.trans
    (Module.DirectLimit.linearEquiv ((PairStageHom A B))
      (fun L M h ↦ (t L M h).toNatLinearMap)).symm.toEquiv
  have he (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : (PairStageHom A B) ⟨L, hA, hB⟩) :
      e (StageSystem.PairCategory.mkHom L hA hB f) =
        AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f := by
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Equiv.ext
  intro f
  induction f using StageSystem.PairCategory.hom_induction with
  | h L hA hB f => exact (he' L hA hB f).trans (he L hA hB f).symm

private theorem coordinates_add
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t)
    (he : ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
      AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f)
    (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f g : PairStageHom A B ⟨L, hA, hB⟩) :
    letI := e.addCommGroup
    StageSystem.PairCategory.mkHom L hA hB f +
      StageSystem.PairCategory.mkHom L hA hB g =
        StageSystem.PairCategory.mkHom L hA hB (f + g) := by
  let := e.addCommGroup
  apply e.injective
  rw [show e (_ + _) = e _ + e _ from e.addEquiv.map_add _ _,
    he L hA hB f, he L hA hB g, he L hA hB (f + g)]
  exact (map_add (AddCommGroup.DirectLimit.of (PairStageHom A B) t
    ⟨L, hA, hB⟩) f g).symm

private theorem coordinates_zero
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) (A B : S.PairCategory)
    [∀ L : PairCommon A B, AddCommGroup (PairStageHom A B L)]
    [Nonempty (PairCommon A B)] [IsDirectedOrder (PairCommon A B)]
    [DecidableEq (PairCommon A B)]
    (t : ∀ L M : PairCommon A B, L ≤ M → PairStageHom A B L →+ PairStageHom A B M)
    (e : (A ⟶ B) ≃ AddCommGroup.DirectLimit (PairStageHom A B) t)
    (he : ∀ L hA hB f, e (StageSystem.PairCategory.mkHom L hA hB f) =
      AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩ f)
    (L : I) (hA : A.stage ≤ L) (hB : B.stage ≤ L) :
    letI := e.addCommGroup
    StageSystem.PairCategory.mkHom L hA hB
      (0 : PairStageHom A B ⟨L, hA, hB⟩) = 0 := by
  let := e.addCommGroup
  apply e.injective
  rw [he L hA hB (0 : PairStageHom A B ⟨L, hA, hB⟩),
    show e (0 : A ⟶ B) = 0 from e.addEquiv.map_zero]
  exact map_zero (AddCommGroup.DirectLimit.of (PairStageHom A B) t ⟨L, hA, hB⟩)

private theorem pair_composition_bilinear
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
    (S : StageSystem C) [∀ A B : S.PairCategory, AddCommGroup (A ⟶ B)]
    (hadd : ∀ {A B : S.PairCategory} {L : I} (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f g : A.toStage hA ⟶ B.toStage hB),
      StageSystem.PairCategory.mkHom L hA hB f +
        StageSystem.PairCategory.mkHom L hA hB g =
          StageSystem.PairCategory.mkHom L hA hB (f + g)) :
    (∀ (A B C : S.PairCategory) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : S.PairCategory) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  constructor
  · intro A B C f f' g
    obtain ⟨L, -, hA, hB, _, _, u, v, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage f f' A.stage
    obtain ⟨M, hLM, hB', hC, _, _, w, _, rfl, -⟩ :=
      StageSystem.PairCategory.exists_common_stage g g L
    rw [← StageSystem.PairCategory.mkHom_tr hLM u,
      ← StageSystem.PairCategory.mkHom_tr hLM v, hadd,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom, hadd, Preadditive.add_comp]
  · intro A B C f g g'
    obtain ⟨L, -, hB, hC, _, _, v, w, rfl, rfl⟩ :=
      StageSystem.PairCategory.exists_common_stage g g' B.stage
    obtain ⟨M, hLM, hA, hB', _, _, u, _, rfl, -⟩ :=
      StageSystem.PairCategory.exists_common_stage f f L
    rw [← StageSystem.PairCategory.mkHom_tr hLM v,
      ← StageSystem.PairCategory.mkHom_tr hLM w, hadd,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom,
      StageSystem.PairCategory.mkHom_comp_mkHom, hadd, Preadditive.comp_add]

private theorem stage_transport_additive
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    [∀ i, Preadditive (C i)] (S : StageSystem C)
    {i j n p : I} (hi : i ≤ n) (hj : j ≤ n) (h : n ≤ p)
    [(S.T h).Additive] (x : C i) (y : C j) :
    S.tr (hi := hi) (hj := hj) h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 ∧
      ∀ f g : (S.T hi).obj x ⟶ (S.T hj).obj y,
        S.tr h (f + g) = S.tr h f + S.tr h g := by
  constructor
  · simp only [StageSystem.tr, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
  · intro f g
    simp only [StageSystem.tr, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private theorem stage_transport_self
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    (S : StageSystem C) {i j n : I} (hi : i ≤ n) (hj : j ≤ n)
    [(S.T (le_refl n)).Faithful] (x : C i) (y : C j)
    (f : (S.T hi).obj x ⟶ (S.T hj).obj y) : S.tr (le_refl n) f = f := by
  apply (S.T (le_refl n)).map_injective
  apply (StageSystem.tr_injective (S := S) (le_refl n)).mp
  exact StageSystem.tr_tr (S := S) (le_refl n) (le_refl n) f

private theorem additive_equivalence
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] [HasBinaryProducts C] (e : C ≌ D) :
    e.functor.Additive := by
  let : e.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object
  exact Functor.additive_of_preserves_binary_products _

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

attribute [local irreducible] stageCategory transition scalarAssociator associator

/-- The upstream common-stage pair category, specialized to the specified rational stages.
Its objects are literal pairs, and no idempotents are adjoined.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Pair := (stageSystem l Ω Y).PairCategory

/-- Cache the existing upstream category on the named concrete pair type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pairCategory : Category (Pair l Ω Y) :=
  inferInstanceAs (Category (stageSystem l Ω Y).PairCategory)

variable {l Ω Y}

/-- The directed index of common finite coefficient overfields of two pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev Common (A B : Pair l Ω Y) :=
  {L : Index l Ω // A.stage ≤ L ∧ B.stage ≤ L}

/-- The compositum of the source and target fields supplies a common coefficient stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonNonempty (A B : Pair l Ω Y) : Nonempty (Common A B) :=
  ⟨⟨Padic.finiteCoefficientCompositum l Ω A.stage B.stage,
    (Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage⟩⟩

/-- Composita make the common-overfield poset directed while retaining both lower bounds.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDirected (A B : Pair l Ω Y) :
    IsDirectedOrder (Common A B) where
  directed L M :=
    ⟨⟨Padic.finiteCoefficientCompositum l Ω L.val M.val,
        L.property.1.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1,
        L.property.2.trans ((Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val).1⟩,
      (Padic.finiteCoefficientFields_properties l Ω).1 L.val M.val⟩

/-- Hom at one common coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def StageHom (A B : Pair l Ω Y) (L : Common A B) :=
  ((stageTransition l Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition l Ω Y B.stage L.val L.property.2).obj B.obj)

/-- Cache the abelian group of a stage Hom before forming the dependent colimit family.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance stageHomAddCommGroup (A B : Pair l Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  inferInstanceAs (AddCommGroup
    ((stageTransition l Ω Y A.stage L.val L.property.1).obj A.obj ⟶
      (stageTransition l Ω Y B.stage L.val L.property.2).obj B.obj))

/-- Extend the representative and conjugate by the specified associators.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transport (A B : Pair l Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  ((stageSystem l Ω Y).assoc L.property.1 h).inv.app A.obj ≫
    (stageTransition l Ω Y L.val M.val h).map f ≫
    ((stageSystem l Ω Y).assoc L.property.2 h).hom.app B.obj

/-- Transport is additive and preserves zero.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: scalar extension is additive. Left and right composition by each fixed
associator component are additive by preadditivity of the rational target stage. -/
theorem transport_additive
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) (L M :
        GeneralAlgebraicallyClosedCoefficients.Common A B) (h : L ≤ M) :
    GeneralAlgebraicallyClosedCoefficients.transport A B L M h 0 = 0 ∧
      ∀ f g, GeneralAlgebraicallyClosedCoefficients.transport A B L M h (f + g) =
        GeneralAlgebraicallyClosedCoefficients.transport A B L M h f +
            GeneralAlgebraicallyClosedCoefficients.transport A B L M h g := by
  exact stage_transport_additive (stageSystem l Ω Y)
    L.property.1 L.property.2 h A.obj B.obj

/-- The transition homomorphism of the directed Hom system.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def transportHom (A B : Pair l Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

/-- The actual representative transports form a directed system of abelian groups.
Source: blueprint order 1462, displayed Hom colimit
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: for a reflexive extension, the normalized tensor unit and the two unit coherence
laws identify the conjugated map with the original map. For two successive extensions,
expand transport and use the associator cocycle and naturality; the inner inverse
associators cancel. This gives identity and composition on each representative. -/
@[instance]
theorem transportSystem (A B : Pair l Ω Y) :
    DirectedSystem (StageHom A B) (fun {L M} h ↦ transportHom A B L M h) := by
  -- Faithfulness turns the cocycle's idempotent reflexive transport into the identity.
  constructor
  · intro L f
    have hf : (stageTransition l Ω Y L.val L.val le_rfl).Faithful := by
      unfold stageTransition
      rw [(stageSystem_existsUnique l Ω Y).exists.choose_spec.1 L.val L.val le_rfl]
      exact Functor.Faithful.of_iso (unitor l Ω Y L.val).symm
    exact stage_transport_self (stageSystem l Ω Y)
      L.property.1 L.property.2 A.obj B.obj f
  · intro N M L h k f
    exact StageSystem.tr_tr (S := stageSystem l Ω Y) h k f

/-- Decidable equality is used only to realize Mathlib's algebraic direct limit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance commonDecidableEq (A B : Pair l Ω Y) :
    DecidableEq (Common A B) := Classical.decEq _

/-- The actual abelian-group colimit, with no completion of its objects.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def ColimitHom (A B : Pair l Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

attribute [local irreducible] unitor

/-- The direct limit's abelian group structure, on the fixed Hom type.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance colimitHomGroup (A B : Pair l Ω Y) : AddCommGroup (ColimitHom A B) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)))

/-- The class of a map over a common finite coefficient field.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def colimitOf (A B : Pair l Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : ColimitHom A B :=
  AddCommGroup.DirectLimit.of (StageHom A B) (transportHom A B) ⟨L, hA, hB⟩ f

/-- The upstream quotient Hom has exactly the stated abelian-colimit coordinates.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: send each common-stage representative to its direct-limit class. The tensor
cocycle and unit law make transport a directed system; the quotient relation is exactly
equality after extension. The direct-limit representative criterion therefore makes
this map well-defined and bijective. Every Hom is represented, proving uniqueness. -/
theorem homCoordinates_existsUnique
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (A B : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :
    ∃! e : (A ⟶ B) ≃ GeneralAlgebraicallyClosedCoefficients.ColimitHom A B,
      ∀ (L : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
        (f : GeneralAlgebraicallyClosedCoefficients.StageHom A B ⟨L, hA, hB⟩),
        e (StageSystem.PairCategory.mkHom L hA hB f) =
          GeneralAlgebraicallyClosedCoefficients.colimitOf A
            B L hA hB f := by
  exact @generic_coordinates (Index l Ω) inferInstance inferInstance (Stage l Ω Y)
    (fun E ↦ stageCategory l Ω Y E)
    (stageSystem l Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (fun _ _ _ _ ↦ rfl) (transportSystem A B)

/-- The canonical Hom coordinates, fixed on every common-stage representative.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def homCoordinates (A B : Pair l Ω Y) :=
  (homCoordinates_existsUnique A B).exists.choose

/-- The abelian group transported from the specified directed colimit.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance homAddCommGroup (A B : Pair l Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

/-- The map represented at L, using the existing upstream quotient constructor.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev ofHom (A B : Pair l Ω Y) (L : Index l Ω)
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) : A ⟶ B :=
  StageSystem.PairCategory.mkHom L hA hB f

private theorem mkHom_add {A B : Pair l Ω Y} {L : Index l Ω}
    (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f g : A.toStage hA ⟶ B.toStage hB) :
    StageSystem.PairCategory.mkHom L hA hB f +
      StageSystem.PairCategory.mkHom L hA hB g =
        StageSystem.PairCategory.mkHom L hA hB (f + g) := by
  exact @coordinates_add (Index l Ω) inferInstance inferInstance (Stage l Ω Y)
    (fun E ↦ stageCategory l Ω Y E)
    (stageSystem l Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (homCoordinates A B)
    (homCoordinates_existsUnique A B).exists.choose_spec L hA hB f g

private theorem mkHom_zero {A B : Pair l Ω Y} {L : Index l Ω}
    (hA : A.stage ≤ L) (hB : B.stage ≤ L) :
    StageSystem.PairCategory.mkHom L hA hB (0 : A.toStage hA ⟶ B.toStage hB) = 0 := by
  exact @coordinates_zero (Index l Ω) inferInstance inferInstance (Stage l Ω Y)
    (fun E ↦ stageCategory l Ω Y E)
    (stageSystem l Ω Y) A B (stageHomAddCommGroup A B)
    inferInstance inferInstance (commonDecidableEq A B)
    (transportHom A B) (homCoordinates A B)
    (homCoordinates_existsUnique A B).exists.choose_spec L hA hB

/-- The fixed composition is additive in each variable.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: represent the three maps at a common compositum. Colimit structure maps are
additive and stage composition is bilinear, giving both asserted equations. -/
theorem composition_bilinear
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    :
    (∀ (A B C : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) (f f' : A ⟶ B) (g : B ⟶ C),
      (f + f') ≫ g = f ≫ g + f' ≫ g) ∧
    (∀ (A B C : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) (f : A ⟶ B) (g g' : B ⟶ C),
      f ≫ (g + g') = f ≫ g + f ≫ g') := by
  exact pair_composition_bilinear (stageSystem l Ω Y)
    (fun hA hB f g ↦ mkHom_add hA hB f g)

section
attribute [local irreducible] homAddCommGroup

/-- Preadditivity uses the actual colimit abelian groups.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance preadditive : Preadditive (Pair l Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

end

/-- The existing upstream inclusion of the actual rational finite stage.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev inclusion (E : Index l Ω) : Stage l Ω Y E ⥤ Pair l Ω Y :=
  (stageSystem l Ω Y).ι E

/-- The inclusion preserves the abelian-colimit addition.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: inclusion sends f to its normalized representative, and homCoordinates sends
that representative to its direct-limit class. Both normalization by fixed unit
components and the direct-limit structure maps are additive. -/
@[instance]
theorem inclusion_additive
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E : Padic.FiniteCoefficientFields l Ω) : (GeneralAlgebraicallyClosedCoefficients.inclusion E :
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤ _).Additive := by
  constructor
  intro X Z f g
  rw [StageSystem.ι_map_eq le_rfl, StageSystem.ι_map_eq le_rfl,
    StageSystem.ι_map_eq le_rfl, Functor.map_add]
  exact (mkHom_add (l := l) (Ω := Ω) (Y := Y)
    (A := ⟨E, X⟩) (B := ⟨E, Z⟩) le_rfl le_rfl _ _).symm

/-- Stagewise object shift, with the coefficient field unchanged.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftPair (n : ℤ) (A : Pair l Ω Y) : Pair l Ω Y :=
  ⟨A.stage, (shiftFunctor (Stage l Ω Y A.stage) n).obj A.obj⟩

/-- The shifted representative uses the prescribed scalar-extension shift comparison.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable def shiftRepresentative (n : ℤ) (A B : Pair l Ω Y)
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : StageHom A B ⟨L, hA, hB⟩) :
    StageHom (shiftPair n A) (shiftPair n B) ⟨L, hA, hB⟩ :=
  ((stageTransition l Ω Y A.stage L hA).commShiftIso n).hom.app A.obj ≫
    (shiftFunctor (Stage l Ω Y L) n).map f ≫
    ((stageTransition l Ω Y B.stage L hB).commShiftIso n).inv.app B.obj

/-- The induced shift is specified on every object, representative and stage inclusion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: shift each finite representative using shiftRepresentative. Exact scalar
extension and associator compatibility with shifts make this independent of stage.
The finite-stage shift units and addition isomorphisms descend componentwise; equality
and coherence may be checked after moving the finite diagrams to a common field.
The inclusion comparisons are identities on the displayed shifted pairs. Thus these
formulas determine the functors and their coherent comparisons on the generators.
Every object is literally in its own stage. The identity inclusion comparisons and
their coherence equations fix the zero and addition comparisons there, hence everywhere.
This proves uniqueness of the full shift structure, not just its object and arrow maps. -/
theorem shift_existsUnique :
    ∃! s : HasShift (Pair l Ω Y) ℤ,
      (fun [shiftInst : HasShift (Pair l Ω Y) ℤ] ↦
        (∀ n : ℤ, (shiftFunctor (Pair l Ω Y) n).Additive) ∧
        (∀ (n : ℤ) (A : Pair l Ω Y),
          (shiftFunctor (Pair l Ω Y) n).obj A = shiftPair n A) ∧
        (∀ (n : ℤ) (A B : Pair l Ω Y) (L : Index l Ω)
          (hA : A.stage ≤ L) (hB : B.stage ≤ L) (f : StageHom A B ⟨L, hA, hB⟩),
          HEq ((shiftFunctor (Pair l Ω Y) n).map (ofHom A B L hA hB f))
            (ofHom (shiftPair n A) (shiftPair n B) L hA hB
              (shiftRepresentative n A B L hA hB f))) ∧
        ∃ c : ∀ E : Index l Ω, (inclusion E : Stage l Ω Y E ⥤ _).CommShift ℤ,
          (fun [commInst : ∀ E : Index l Ω,
              (inclusion E : Stage l Ω Y E ⥤ _).CommShift ℤ] ↦
            ∀ (n : ℤ) (E : Index l Ω) (K : Stage l Ω Y E),
              HEq (((inclusion E : Stage l Ω Y E ⥤ _).commShiftIso n).hom.app K)
                (𝟙 ((inclusion E : Stage l Ω Y E ⥤ _).obj
                  ((shiftFunctor (Stage l Ω Y E) n).obj K)))) (commInst := c))
        (shiftInst := s) := by
  sorry

/-- The stagewise shift with the representative formula of shift_existsUnique.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance hasShift : HasShift (Pair l Ω Y) ℤ := shift_existsUnique.exists.choose

/-- Each induced integer shift is additive.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair l Ω Y) n).Additive := shift_existsUnique.exists.choose_spec.1 n

/-- The normalized exact-stage shift comparison, fixed to identity on shifted pairs.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage l Ω Y E ⥤ _).CommShift ℤ :=
  shift_existsUnique.exists.choose_spec.2.2.2.choose E

/-- A stage zero object remains zero after forming directed Hom colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: take the zero object at the bottom coefficient field. Every transition is exact
and therefore preserves zero. At every common field its Hom groups to and from any
object vanish. Their directed colimits vanish, giving the zero-object universal property. -/
theorem zero_exists : HasZeroObject (Pair l Ω Y) := by
  let E := Padic.finiteCoefficientBase l Ω
  let X : Pair l Ω Y := (inclusion E).obj (0 : Stage l Ω Y E)
  refine ⟨⟨X, ?_⟩⟩
  rw [IsZero.iff_id_eq_zero, StageSystem.PairCategory.id_eq_mkHom X le_rfl,
    ← mkHom_zero (A := X) (B := X) le_rfl le_rfl]
  have hz : IsZero (X.toStage le_rfl) :=
    Functor.map_isZero (stageTransition l Ω Y E E le_rfl) (isZero_zero _)
  exact congrArg (StageSystem.PairCategory.mkHom E le_rfl le_rfl) (hz.eq_of_src _ _)

attribute [instance] zero_exists

/-- The canonical coefficient-stage identifications commute with shifts.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients).
Proof: on finite representatives this is scalar-extension shift compatibility and
sfRationalScalar_coherence. The normalized inclusion comparisons are
identities on shifted pairs. The cocycle equation identifies both composites. -/
@[instance]
theorem transitionIso_commShift
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Y : AlgebraicGeometry.Scheme.{u}}
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    NatTrans.CommShift ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).transIso h).hom ℤ
        := by
  sorry

/-- The recorded common-stage distinguished-triangle criterion.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev Distinguished (T : Triangle (Pair l Ω Y)) : Prop :=
  (stageSystem l Ω Y).CommonStageDistinguished T

/-- The unique pretriangulation supplied by the common-stage Verdier theorem.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance pretriangulated : Pretriangulated (Pair l Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem l Ω Y)).exists.choose

/-- The Verdier axiom for the specified common-stage triangles.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance isTriangulated : IsTriangulated (Pair l Ω Y) :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem l Ω Y)).exists.choose_spec.2.1

/-- Each actual rational finite-stage inclusion is exact.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable instance inclusion_exact (E : Index l Ω) :
    (inclusion E : Stage l Ω Y E ⥤ _).IsTriangulated :=
  (StageSystem.commonStage_verdier_existsUnique (stageSystem l Ω Y)).exists.choose_spec.2.2 E

end GeneralAlgebraicallyClosedCoefficients

/-- The algebraically closed coefficient category is the pair category itself.
No Karoubi envelope occurs: its objects are finite-field pairs and its Hom groups are
canonically the displayed directed colimits.
Source: blueprint order 1462 (blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev generalAlgebraicallyClosedConstructibleCategory
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y

private theorem stage_equality_pairs
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [cC : ∀ i, Category.{v} (C i)]
    {S R : StageSystem C} (e : S = R) :
    (∀ (i : I) (x : C i),
      (Pi.eqToEquivalence (fun T : StageSystem C ↦ T.PairCategory) e).functor.obj
        ⟨i, x⟩ = ⟨i, x⟩) ∧
    (∀ (A B : S.PairCategory) (n : I) (hi : A.stage ≤ n) (hj : B.stage ≤ n)
      (f : (S.T hi).obj A.obj ⟶ (S.T hj).obj B.obj)
      (g : (R.T hi).obj A.obj ⟶ (R.T hj).obj B.obj),
      HEq f g → HEq
        ((Pi.eqToEquivalence (fun T : StageSystem C ↦ T.PairCategory) e).functor.map
          (StageSystem.PairCategory.mkHom n hi hj f))
        (StageSystem.PairCategory.mkHom (S := R)
          (X := ⟨A.stage, A.obj⟩) (Y := ⟨B.stage, B.obj⟩) n hi hj g)) := by
  subst R
  constructor
  · intro i x
    rfl
  · intro A B n hi hj f g hfg
    cases eq_of_heq hfg
    rfl

namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] homAddCommGroup
  SfAlgebraicallyClosedCoefficients.homAddCommGroup

attribute [local irreducible] ScalarLocalization.composition
  sfRationalScalarExtension sfRationalTriangulationDatum sfRationalConstructibleLocalization

private theorem normalized_comp_parameter_independent
    (l : ℕ) [Fact l.Prime]
    (E L M : Type u) [Field E] [Field L] [Field M]
    [Algebra (Padic l) E] [Algebra (Padic l) L] [Algebra (Padic l) M]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    [FiniteDimensional (Padic l) M]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] M) (k : E →ₐ[Padic l] M)
    (h : j.comp i = k) (Y : AlgebraicGeometry.Scheme.{u})
    (p q : ℕ) (hp : l ≠ p) (hq : l ≠ q) :
    HEq
      (sfRationalScalarComp l E L i Y p hp M j ≪≫
        eqToIso (congrArg (sfRationalScalarExtension l E Y p hp M) h))
      (sfRationalScalarComp l E L i Y q hq M j ≪≫
        eqToIso (congrArg (sfRationalScalarExtension l E Y q hq M) h)) := by
  unfold sfRationalScalarComp sfRationalScalarExtension sfIntegralScalarComp
  unfold sfConstructibleIntegralScalarExtension
  rfl

private theorem normalized_unit_parameter_independent
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] E) (h : i = AlgHom.id (Padic l) E)
    (Y : AlgebraicGeometry.Scheme.{u}) (p q : ℕ) (hp : l ≠ p) (hq : l ≠ q) :
    HEq
      (eqToIso (congrArg (sfRationalScalarExtension l E Y p hp E) h) ≪≫
        sfRationalScalarUnit l E Y p hp)
      (eqToIso (congrArg (sfRationalScalarExtension l E Y q hq E) h) ≪≫
        sfRationalScalarUnit l E Y q hq) := by
  unfold sfRationalScalarUnit sfRationalScalarExtension sfIntegralScalarUnit
  unfold sfConstructibleIntegralScalarExtension
  rfl

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The normalized associator and identity comparison specialize canonically.
Source: blueprint order 1821, canonical composition clause
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: the ordinary balanced tensor associator and multiplication unit contain
no p. The quotient-completion comparisons are the very same uniquely normalized
comparisons. Proof irrelevance identifies the integral restrictions. Their
exists-unique component specifications identify the integral comparisons and
then their rational images. Substitution through coefficientInclusion_laws
identifies the displayed stage associators and units, also for repeated fields. -/
theorem specialization_comparisons :
    (∀ (E L M : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) (k : L ≤ M),
      HEq (GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k)
        (SfAlgebraicallyClosedCoefficients.associator D l hl Ω Y E L M h k)) ∧
    (∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      HEq (unitor l Ω Y E) (SfAlgebraicallyClosedCoefficients.unitor D l hl Ω Y E)) := by
  constructor
  · intro E L M h k
    apply ((associator_existsUnique l Ω Y E L M h k).exists.choose_spec).trans
    unfold scalarAssociator SfAlgebraicallyClosedCoefficients.associator
    unfold SfAlgebraicallyClosedCoefficients.transition
    dsimp (config := { instances := true }) only
      [SfAlgebraicallyClosedCoefficients.stageCategory,
        SfAlgebraicallyClosedCoefficients.Stage, FiniteFieldDatum.sfRationalCategory]
    exact normalized_comp_parameter_independent l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)
      Y 0 D.p (Fact.out : l.Prime).ne_zero hl
  · intro E
    unfold unitor SfAlgebraicallyClosedCoefficients.unitor
    unfold transition SfAlgebraicallyClosedCoefficients.transition
    dsimp (config := { instances := true }) only
      [SfAlgebraicallyClosedCoefficients.stageCategory,
        SfAlgebraicallyClosedCoefficients.Stage, FiniteFieldDatum.sfRationalCategory]
    exact normalized_unit_parameter_independent l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E E le_rfl)
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)
      Y 0 D.p (Fact.out : l.Prime).ne_zero hl

/-- Equality of the complete normalized stage data, not merely its carriers.
Source: blueprint order 1821, finite-stage pair construction
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: both Stage families reduce to sfRationalConstructibleCategory on the
same small coefficient fields. specialization_transition and the associator
clause of specialization_comparisons identify every data field of StageSystem.
Its remaining cocycle field is a proof. Alternatively apply the uniqueness
clause of stageSystem_existsUnique to the old system. -/
theorem specialization_stageSystem :
    stageSystem l Ω Y = SfAlgebraicallyClosedCoefficients.stageSystem D l hl Ω Y := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      have hOld :=
        (SfAlgebraicallyClosedCoefficients.stageSystem_existsUnique D l hl Ω Y).exists.choose_spec
      apply (stageSystem_existsUnique l Ω Y).unique
      · exact (stageSystem_existsUnique l Ω Y).exists.choose_spec
      · constructor
        · intro E L h
          exact (hOld.1 E L h).trans (specialization_transition D l hl Ω Y E L h).symm
        · intro E L M h k
          exact (hOld.2 E L M h k).trans
            ((specialization_comparisons D l hl Ω Y).1 E L M h k).symm

/-- Specialization is the restriction of actual derived extension of scalars.
Source: latest blueprint `def-sfb-constructible-extend-to-qlbar.md`.
(blueprint: lem-pur-general-coefficient-specialization). -/
abbrev specialization (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  constructibleToPadicAlgCl Y ℓ E

/-- Specialization fixes the literal coefficient pair and every representative.
Source: blueprint order 1821, pair and Hom clauses
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: eliminate specialization_stageSystem. Pi.eqToEquivalence then reduces
to the identity equivalence. The object formula is reflexivity, and the map
formula is reflexivity after the assumed HEq identifies the finite maps. -/
theorem specialization_pairs :
    (∀ (E : AlgebraicallyClosedCoefficients.Index l Ω) (K : Stage l Ω Y E),
      (specialization D l hl Ω Y).functor.obj ⟨E, K⟩ = ⟨E, K⟩) ∧
    (∀ (A B : Pair l Ω Y) (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : StageHom A B ⟨L, hA, hB⟩)
      (g : SfAlgebraicallyClosedCoefficients.StageHom
        (⟨A.stage, A.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
        (⟨B.stage, B.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) ⟨L, hA, hB⟩),
      HEq f g → HEq ((specialization D l hl Ω Y).functor.map (ofHom A B L hA hB f))
        (SfAlgebraicallyClosedCoefficients.ofHom
          (⟨A.stage, A.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y)
          (⟨B.stage, B.obj⟩ : SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) L hA hB g)) := by
  exact stage_equality_pairs (C := Stage l Ω Y)
    (cC := fun E ↦ stageCategory l Ω Y E)
    (specialization_stageSystem D l hl Ω Y)

/-- Actual specialization is additive for the inherited ambient Hom laws.
Source: latest blueprint scalar-extension paragraph of `sk-thm-sfb-qlbar-two-colimit`.
(blueprint: lem-pur-general-coefficient-specialization).
Proof: the closure-additivity clause of the uniquely normalized scalar data applies
to the actual restricted scalar extension, with the ambient preadditive structures. -/
theorem specialization_additive (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (specialization ℓ Y E).Additive := by
  obtain ⟨d, hd, _⟩ := condensedCoefficientStageNormalization_existsUnique Y ℓ
  let : CondensedCoefficientStageData Y ℓ := d
  exact hd.1.closureAdditive E

/-- Specialization preserves and reflects the specified distinguished triangles.
Source: blueprint order 1821, common-stage triangles
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: each distinguished triangle is isomorphic to a distinguished finite-stage
image. specialization_pairs identifies the finite image arrows, and the
identity-normalized shift comparison identifies its connecting arrow. The same
argument with inverse equality transport gives reflection. The old and new
Verdier pretriangulations have precisely these common-stage distinguished sets. -/
theorem specialization_distinguished (T : Triangle (Pair l Ω Y)) :
    T ∈ distTriang (Pair l Ω Y) ↔
      (specialization D l hl Ω Y).functor.mapTriangle.obj T ∈
        distTriang (SfAlgebraicallyClosedCoefficients.Pair D l hl Ω Y) := by
  sorry

/-- Actual specialization is exact for the tensor-normalized coherent shifts.
Source: latest blueprint `sk-prop-qlbar-two-colimit.proof.md`, scalar-extension functor.
(blueprint: lem-pur-general-coefficient-specialization).
Proof: take the uniquely normalized scalar data. Its closure exactness states that
the ambient image of the specialized triangle is distinguished. By the definition
of the intrinsic triangulation this is exactly the required conclusion. -/
theorem specialization_exact (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI := specializationCommShift ℓ Y E
    (specialization ℓ Y E).IsTriangulated := by
  let d := (condensedCoefficientStageNormalization_existsUnique Y ℓ).exists.choose
  have hd : CondensedCoefficientStageNormalized Y ℓ d :=
    (condensedCoefficientStageNormalization_existsUnique Y ℓ).exists.choose_spec
  let := specializationCommShift ℓ Y E
  constructor
  intro T hT
  exact hd.2.2.2.closureExact inferInstance E T hT

/-- Every intrinsic algebraically closed coefficient object descends to a finite field.
Source: latest blueprint `sk-prop-qlbar-two-colimit.proof.md`, first sentence.
(blueprint: lem-pur-general-coefficient-specialization).
Proof: use object descent for the existing constructible scalar cocone and reverse
its supplied isomorphism, as in the intrinsic specialization theorem. -/
theorem representatives (N : PadicAlgClConstructible Y ℓ) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ) (K : PadicSubfieldConstructible Y ℓ E),
      Nonempty (N ≅ (specialization ℓ Y E).obj K) := by
  obtain ⟨E, K, ⟨e⟩⟩ := constructibleCocone_essSurjObj Y ℓ N
  exact ⟨E, K, ⟨e.symm⟩⟩

/-- The full inclusion is exact for its inherited ordinary derived shift.
Source: latest blueprint `det-def-sfb-bounded-constructible.md`, triangulated clause.
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: reuse the exactness constructor of the former interface: the forward direction
of the distinguishedness characterization is precisely preservation of triangles. -/
theorem inclusion_exact : (ambientInclusion ℓ Y).IsTriangulated := by
  constructor
  intro T hT
  exact (distinguished_iff ℓ Y T).mp hT

/-- Intrinsic distinguishedness is exactly ambient distinguishedness.
Source: latest blueprint `det-def-sfb-bounded-constructible.md`, triangulated clause.
(blueprint: def-weil-algebraically-closed-coefficients).
Proof: the full triangulated subcategory defines its distinguished set as the inverse
image of the ambient distinguished set under the inclusion on triangles. -/
theorem distinguished_iff (T : Triangle (PadicAlgClConstructible Y ℓ)) :
    T ∈ distTriang (PadicAlgClConstructible Y ℓ) ↔
      (ambientInclusion ℓ Y).mapTriangle.obj T ∈ distTriang _ := Iff.rfl

/-- The unique tensor-normalized scalar data fixes the coherent specialization shifts.
Source: latest blueprint scalar-extension paragraph of `sk-thm-sfb-qlbar-two-colimit`.
(blueprint: lem-general-algebraically-closed-coefficient-stages). -/
abbrev specializationCommShift (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (specialization ℓ Y E).CommShift ℤ :=
  (condensedCoefficientStageNormalization_existsUnique Y ℓ).exists.choose.closureShift E

/-- The full inclusion into the ordinary derived category of coefficient modules.
Source: latest blueprint `det-def-sfb-bounded-constructible.md`.
(blueprint: def-weil-algebraically-closed-coefficients). -/
abbrev ambientInclusion := (boundedConstructible (padicAlgClRingObj Y ℓ)).ι

attribute [local irreducible] specialization pairCategory
  SfAlgebraicallyClosedCoefficients.pairCategory preadditive
  SfAlgebraicallyClosedCoefficients.preadditive

end GeneralAlgebraicallyClosedCoefficients
end WeilConjectures
