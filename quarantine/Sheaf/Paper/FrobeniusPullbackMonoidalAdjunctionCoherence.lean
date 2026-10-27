/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.SemilinearFieldOperationLifts
public import Sheaf.Paper.FrobeniusSquareExchange
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.CompletedPullbackTensorComparison
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-! # Frobenius coherence of pullback, tensor, and the ordinary adjunction

Source: blueprint latest, prop-weil-operations.proof.md, sentence 1, through
lem-fix-weil-operations.proof.md, pullback/tensor and ordinary-adjunction paragraphs
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence).

The two coefficient specifications use the actual canonical integral-normalized
comparisons. The categorical clauses apply on the stipulated full closed domains:
the adjunction supplied there is the ordinary one, with its original maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v a b c d
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures.PodFrobeniusCoherence
/-- The comparison equation for the specified functors, in diagrammatic order.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def ComparisonEquation
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} {H J : C ⥤ B}
    (sH : H ⋙ Q ≅ P ⋙ H) (sJ : J ⋙ Q ≅ P ⋙ J) (e : H ≅ J) : Prop :=
  ∀ K : C, sH.hom.app K ≫ e.hom.app (P.obj K) =
    Q.map (e.hom.app K) ≫ sJ.hom.app K

/-- A specified equivariant comparison is an isomorphism of the standard lifts.
This also applies to products of input categories for multivariable operations.
Proof (node step 6): naturality of e with theta, followed by ComparisonEquation,
gives the structure equation. Multiplication by both inverses gives the inverse
structure equation. Naturality and both inverse identities hold on carriers;
faithfulness of the existing forgetful functor gives them for fixed pairs.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
theorem comparison_lifts
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} {H J : C ⥤ B}
    (sH : H ⋙ Q ≅ P ⋙ H) (sJ : J ⋙ Q ≅ P ⋙ J) (e : H ≅ J)
    (he : ComparisonEquation sH sJ e) :
    ∃ w : IsoAlgebra.mapOfNatIso sH ≅ IsoAlgebra.mapOfNatIso sJ,
      (∀ K : IsoAlgebra P, (w.hom.app K).hom.f = e.hom.app K.carrier) ∧
      ∀ K : IsoAlgebra P, (w.inv.app K).hom.f = e.inv.app K.carrier := by
  have hh : Functor.whiskerRight e.hom Q ≫ sJ.hom =
      sH.hom ≫ Functor.whiskerLeft P e.hom := by
    ext K
    exact (he K).symm
  let α := IsoAlgebra.mapOfNatIsoHom e.hom hh
  have hi : Functor.whiskerRight e.inv Q ≫ sH.hom =
      sJ.hom ≫ Functor.whiskerLeft P e.inv := by
    ext K
    change Q.map (e.inv.app K) ≫ sH.hom.app K =
      sJ.hom.app K ≫ e.inv.app (P.obj K)
    apply (cancel_mono (e.hom.app (P.obj K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [he K, ← Q.map_comp_assoc, Iso.inv_hom_id_app, Q.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  let β := IsoAlgebra.mapOfNatIsoHom e.inv hi
  let w : IsoAlgebra.mapOfNatIso sH ≅ IsoAlgebra.mapOfNatIso sJ :=
    { hom := α
      inv := β
      hom_inv_id := by
        apply NatTrans.ext
        funext K
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        exact e.hom_inv_id_app K.carrier
      inv_hom_id := by
        apply NatTrans.ext
        funext K
        apply ObjectProperty.hom_ext
        apply Algebra.Hom.ext
        exact e.inv_hom_id_app K.carrier }
  exact ⟨w, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The ordinary unit and counit, exchange normalization, and lifted triangles.
No exceptional operation is part of these data. The categories may themselves be
the prescribed full domains, so no extension of an operation domain is required.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def OrdinaryAdjunctionCoherent
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    (P : C ⥤ C) (Q : B ⥤ B) {L : C ⥤ B} {R : B ⥤ C}
    (adj : L ⊣ R) (s : L ⋙ Q ≅ P ⋙ L) : Prop :=
  ∃ t : R ⋙ P ≅ Q ⋙ R,
    t.hom = (mateEquiv adj adj s.inv).natTrans ∧
    (∀ M : B, t.hom.app M =
      adj.unit.app (P.obj (R.obj M)) ≫ R.map (s.inv.app (R.obj M)) ≫
        R.map (Q.map (adj.counit.app M))) ∧
    (∀ K : IsoAlgebra P,
      P.map (adj.unit.app K.carrier) ≫
          ((IsoAlgebra.mapOfNatIso t).obj ((IsoAlgebra.mapOfNatIso s).obj K)).str.hom =
        K.str.hom ≫ adj.unit.app K.carrier) ∧
    (∀ M : IsoAlgebra Q,
      ((IsoAlgebra.mapOfNatIso s).obj ((IsoAlgebra.mapOfNatIso t).obj M)).str.hom ≫
          adj.counit.app M.carrier =
        Q.map (adj.counit.app M.carrier) ≫ M.str.hom) ∧
    ∃ A : IsoAlgebra.mapOfNatIso s ⊣ IsoAlgebra.mapOfNatIso t,
      (∀ K : IsoAlgebra P, (A.unit.app K).hom.f = adj.unit.app K.carrier) ∧
      (∀ M : IsoAlgebra Q, (A.counit.app M).hom.f = adj.counit.app M.carrier) ∧
      (∀ K : IsoAlgebra P,
        (IsoAlgebra.mapOfNatIso s).map (A.unit.app K) ≫
          A.counit.app ((IsoAlgebra.mapOfNatIso s).obj K) = 𝟙 _) ∧
      ∀ M : IsoAlgebra Q,
        A.unit.app ((IsoAlgebra.mapOfNatIso t).obj M) ≫
          (IsoAlgebra.mapOfNatIso t).map (A.counit.app M) = 𝟙 _

/-- Ordinary adjunction coherence on any supplied closed operation domains.
Here P,Q are the Frobenius equivalences, s the specified pullback-square
comparison, and adj the original ordinary pullback/direct-image adjunction.
Proof (node steps 7--9): substitute s inverse in def-exchange-projection.
Its three factors are exactly mateEquiv, giving the stated normalization.
The mate is invertible along the Frobenius equivalences, as supplied by
lem-pod-semilinear-field-operation-lifts. Apply
lem-sf-fixed-pair-adjunction-lift to this mate: its unit and counit are the
original ordinary maps, and their structure conditions give the displayed two
equations. Both triangle composites forget to the ordinary triangles. Faithfulness
of the forgetful functor therefore proves the lifted triangles.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
theorem ordinary_adjunction_coherent
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    (P : C ⥤ C) (Q : B ⥤ B) [P.IsEquivalence] [Q.IsEquivalence]
    {L : C ⥤ B} {R : B ⥤ C} (adj : L ⊣ R) (s : L ⋙ Q ≅ P ⋙ L) :
    OrdinaryAdjunctionCoherent P Q adj s := by
  let t := IsoAlgebra.mateIso adj s
  have ht : (mateEquiv adj adj s.inv).natTrans = t.hom := rfl
  let A := IsoAlgebra.mapOfNatIsoAdjunction adj s t ht
  refine ⟨t, rfl, ?_, ?_, ?_, A, ?_, ?_, ?_, ?_⟩
  · intro M
    change (mateEquiv adj adj (TwoSquare.mk _ _ _ _ s.inv)).natTrans.app M = _
    simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.comp_obj,
      Functor.id_obj, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_map, Category.id_comp, Category.comp_id]
  · exact IsoAlgebra.map_unit_app_comp_str adj s t ht
  · intro M
    exact (IsoAlgebra.map_counit_app_comp_str adj s t ht M).symm
  · exact fun _ ↦ rfl
  · exact fun _ ↦ rfl
  · exact A.left_triangle_components
  · exact A.right_triangle_components

section Rational
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
variable {X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]

/-- The canonical rational Frobenius comparison for a model morphism.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def rationalSquare (f₀ : X₀ ⟶ Y₀)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  podRationalSquarePullbackComponent l E
    (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
    (FrobeniusExchange.fiberMap D f₀)
    (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
    (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1 K

/-- The canonical rational compositor, with the base-change functoriality transport.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def rationalComposition (f₀ : X₀ ⟶ Y₀) (h₀ : Y₀ ⟶ Z₀)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber Z₀).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI := fun z ↦ sfWeilPrimeInvertible D l hl Z₀ z
  eqToIso (congrArg
    (fun m : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Z₀).left ↦
      (rationalDerivedPullback l E m).obj K)
    (congrArg Over.Hom.left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map_comp f₀ h₀))) ≪≫
    pullbackTensorRationalComposition l E
    (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
    (Z := (D.geometricFiber X₀).left) (FrobeniusExchange.fiberMap D h₀)
      (FrobeniusExchange.fiberMap D f₀) K

/-- The specified rational composition and tensor comparisons commute with Frobenius.
The last clauses are exactly the multivariable associativity, signed symmetry,
and left/right unit equations of the canonical Frobenius tensor comparison.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def RationalCoherent (f₀ : X₀ ⟶ Y₀) (h₀ : Y₀ ⟶ Z₀) : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI := fun z ↦ sfWeilPrimeInvertible D l hl Z₀ z
  ∃ (sF : rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀) ⋙
        sfWeilFrobeniusPullback D l hl X₀ E ≅
      sfWeilFrobeniusPullback D l hl Y₀ E ⋙
        rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀))
    (sH : rationalDerivedPullback l E
          (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D h₀) ⋙
        sfWeilFrobeniusPullback D l hl Y₀ E ≅
      sfWeilFrobeniusPullback D l hl Z₀ E ⋙
        rationalDerivedPullback l E
          (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D h₀))
    (sHF : rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D (f₀ ≫ h₀)) ⋙
        sfWeilFrobeniusPullback D l hl X₀ E ≅
      sfWeilFrobeniusPullback D l hl Z₀ E ⋙
        rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D (f₀ ≫ h₀))),
    (∀ K, sF.app K = rationalSquare D l hl E f₀ K) ∧
    (∀ K, sH.app K = rationalSquare D l hl E h₀ K) ∧
    (∀ K, sHF.app K = rationalSquare D l hl E (f₀ ≫ h₀) K) ∧
    (∀ K, sHF.hom.app K ≫
        (rationalComposition D l hl E f₀ h₀
          ((sfWeilFrobeniusPullback D l hl Z₀ E).obj K)).hom =
      (sfWeilFrobeniusPullback D l hl X₀ E).map
          (rationalComposition D l hl E f₀ h₀ K).hom ≫
        sF.hom.app ((rationalDerivedPullback l E
          (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D h₀)).obj K) ≫
        (rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).map (sH.hom.app K)) ∧
    (∀ M N, sF.hom.app ((rationalDerivedTensor l E
          (D.geometricFiber Y₀).left).obj (M, N)) ≫
        (rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).map
          (canonicalRationalPullbackTensor l E
            (D.geometricFrobenius Y₀).hom M N).hom ≫
        (canonicalRationalPullbackTensor l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)
          ((sfWeilFrobeniusPullback D l hl Y₀ E).obj M)
          ((sfWeilFrobeniusPullback D l hl Y₀ E).obj N)).hom =
      (sfWeilFrobeniusPullback D l hl X₀ E).map
          (canonicalRationalPullbackTensor l E
            (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
            (FrobeniusExchange.fiberMap D f₀) M N).hom ≫
        (canonicalRationalPullbackTensor l E
          (D.geometricFrobenius X₀).hom
          ((rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).obj M)
          ((rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).obj N)).hom ≫
        (rationalDerivedTensor l E (D.geometricFiber X₀).left).map
          (Prod.mkHom (sF.hom.app M) (sF.hom.app N))) ∧
    (∀ (R : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left ⥤
          sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left)
      (adj : rationalDerivedPullback l E
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀) ⊣ R),
      OrdinaryAdjunctionCoherent
        (sfWeilFrobeniusPullback
          D l hl Y₀ E)
        (sfWeilFrobeniusPullback
          D l hl X₀ E) adj sF) ∧
    (canonicalRationalPullbackTensor_associative l E (D.geometricFrobenius X₀).hom ∧
      canonicalRationalPullbackTensor_braiding l E (D.geometricFrobenius X₀).hom ∧
      canonicalRationalPullbackTensor_unit l E (D.geometricFrobenius X₀).hom) ∧
    (canonicalRationalPullbackTensor_associative l E (D.geometricFrobenius Y₀).hom ∧
      canonicalRationalPullbackTensor_braiding l E (D.geometricFrobenius Y₀).hom ∧
      canonicalRationalPullbackTensor_unit l E (D.geometricFrobenius Y₀).hom) ∧
    (canonicalRationalPullbackTensor_associative l E (D.geometricFrobenius Z₀).hom ∧
      canonicalRationalPullbackTensor_braiding l E (D.geometricFrobenius Z₀).hom ∧
      canonicalRationalPullbackTensor_unit l E (D.geometricFrobenius Z₀).hom)

end Rational

section Common
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
variable {X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]

/-- The canonical common Frobenius comparison for a model morphism.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def commonSquare (f₀ : X₀ ⟶ Y₀)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  podCommonSquarePullbackComponent l Ω
    (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
    (FrobeniusExchange.fiberMap D f₀)
    (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
    (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1 K

/-- The canonical common compositor, with the base-change functoriality transport.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def commonComposition (f₀ : X₀ ⟶ Y₀) (h₀ : Y₀ ⟶ Z₀)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI := fun z ↦ sfWeilPrimeInvertible D l hl Z₀ z
  eqToIso (congrArg
    (fun m : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Z₀).left ↦
      (commonStageDerivedPullback l Ω m).obj K)
    (congrArg Over.Hom.left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map_comp f₀ h₀))) ≪≫
    pullbackTensorCommonComposition l Ω
    (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
    (Z := (D.geometricFiber X₀).left) (FrobeniusExchange.fiberMap D h₀)
      (FrobeniusExchange.fiberMap D f₀) K

/-- The specified common composition and tensor comparisons commute with Frobenius.
The last clauses are exactly the multivariable associativity, signed symmetry,
and left/right unit equations of the canonical Frobenius tensor comparison.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
def CommonCoherent (f₀ : X₀ ⟶ Y₀) (h₀ : Y₀ ⟶ Z₀) : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI := fun z ↦ sfWeilPrimeInvertible D l hl Z₀ z
  ∃ (sF : commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀) ⋙
        sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ⋙
        commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀))
    (sH : commonStageDerivedPullback l Ω
          (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D h₀) ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω ⋙
        commonStageDerivedPullback l Ω
          (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D h₀))
    (sHF : commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D (f₀ ≫ h₀)) ⋙
        sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω ⋙
        commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D (f₀ ≫ h₀))),
    (∀ K, sF.app K = commonSquare D l hl Ω f₀ K) ∧
    (∀ K, sH.app K = commonSquare D l hl Ω h₀ K) ∧
    (∀ K, sHF.app K = commonSquare D l hl Ω (f₀ ≫ h₀) K) ∧
    (∀ K, sHF.hom.app K ≫
        (commonComposition D l hl Ω f₀ h₀
          ((sfCommonStageWeilFrobeniusPullback D l hl Z₀ Ω).obj K)).hom =
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).map
          (commonComposition D l hl Ω f₀ h₀ K).hom ≫
        sF.hom.app ((commonStageDerivedPullback l Ω
          (X := (D.geometricFiber Y₀).left) (Y := (D.geometricFiber Z₀).left)
          (FrobeniusExchange.fiberMap D h₀)).obj K) ≫
        (commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).map (sH.hom.app K)) ∧
    (∀ M N, sF.hom.app ((commonStageDerivedTensor l Ω
          (D.geometricFiber Y₀).left).obj (M, N)) ≫
        (commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).map
          (canonicalCommonStagePullbackTensor l Ω
            (D.geometricFrobenius Y₀).hom M N).hom ≫
        (canonicalCommonStagePullbackTensor l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)
          ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj M)
          ((sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj N)).hom =
      (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).map
          (canonicalCommonStagePullbackTensor l Ω
            (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
            (FrobeniusExchange.fiberMap D f₀) M N).hom ≫
        (canonicalCommonStagePullbackTensor l Ω
          (D.geometricFrobenius X₀).hom
          ((commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).obj M)
          ((commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀)).obj N)).hom ≫
        (commonStageDerivedTensor l Ω (D.geometricFiber X₀).left).map
          (Prod.mkHom (sF.hom.app M) (sF.hom.app N))) ∧
    (∀ (R : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left ⥤
          generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (adj : commonStageDerivedPullback l Ω
          (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
          (FrobeniusExchange.fiberMap D f₀) ⊣ R),
      OrdinaryAdjunctionCoherent
        (sfCommonStageWeilFrobeniusPullback
          D l hl Y₀ Ω)
        (sfCommonStageWeilFrobeniusPullback
          D l hl X₀ Ω) adj sF) ∧
    (canonicalCommonStagePullbackTensor_associative l Ω (D.geometricFrobenius X₀).hom ∧
      canonicalCommonStagePullbackTensor_braiding l Ω (D.geometricFrobenius X₀).hom ∧
      canonicalCommonStagePullbackTensor_unit l Ω (D.geometricFrobenius X₀).hom) ∧
    (canonicalCommonStagePullbackTensor_associative l Ω (D.geometricFrobenius Y₀).hom ∧
      canonicalCommonStagePullbackTensor_braiding l Ω (D.geometricFrobenius Y₀).hom ∧
      canonicalCommonStagePullbackTensor_unit l Ω (D.geometricFrobenius Y₀).hom) ∧
    (canonicalCommonStagePullbackTensor_associative l Ω (D.geometricFrobenius Z₀).hom ∧
      canonicalCommonStagePullbackTensor_braiding l Ω (D.geometricFrobenius Z₀).hom ∧
      canonicalCommonStagePullbackTensor_unit l Ω (D.geometricFrobenius Z₀).hom)

end Common

/-- The two coefficient-stage assertions, using only the canonical comparisons.
Proof (node steps 1--6): obtain the normalized natural square comparisons from
lem-pod-semilinear-field-operation-lifts. The compositor is the rationalization
of lem-pod-integral-pullback-composition and its common-stage representative;
lem-pod-pullback-identities-scalar-extension identifies all scalar transports.
Apply pullback associativity to (g_X,f,h), (f,g_Y,h), (f,h,g_Z). Substitute the two
inverse-compositor formulas for s_F,s_H. Cancel the adjacent inverse factors;
the result is exactly the displayed composition equation. For tensor apply the
composition equation of lem-pur-derived-pullback-tensor-iso to (g_X,f) and
(f,g_Y), solve for their shared composite tensor comparison, and cancel.
The same lemma gives associativity, the signed derived braiding, and both units.
Naturality in each input and comparison_lifts then make all these maps, including
their inverses, morphisms of Weil pairs. All calculations use arbitrary rational
or common-stage arrows, with no invariant integral lattice required.
The remaining ordinary-adjunction clauses are ordinary_adjunction_coherent above,
applied to the original supplied adjunction and these normalized square maps.
Source: blueprint latest, lem-fix-weil-operations.proof.md
(blueprint: lem-pod-frobenius-pullback-monoidal-adjunction-coherence). -/
theorem frobeniusPullbackMonoidalAdjunctionCoherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ Y₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (f₀ : X₀ ⟶ Y₀) (h₀ : Y₀ ⟶ Z₀)
    [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    RationalCoherent D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f₀ h₀ ∧
      CommonCoherent D l hl Ω f₀ h₀ := by
  sorry

end WeilConjectures.PodFrobeniusCoherence
