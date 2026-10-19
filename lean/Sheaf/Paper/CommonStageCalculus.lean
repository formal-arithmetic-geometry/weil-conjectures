/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q07 and NS
-/
module

public import Sheaf.Paper.FiniteStagePairCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.IntrinsicCompletionCompleted
import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.BoundedConstructibleComplete
import Sheaf.Paper.PbcRationalCategory
import Sheaf.CategoryTheory.ScalarLocalization

import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Paper.PbcScalarExtension
/-! # The actual common-stage additive structure and shift

Source: blueprint `prop-weil-pbc-common-stage-calculus`.
(blueprint: prop-weil-pbc-common-stage-calculus)

These generic constructions apply to the canonical exact scalar-extension system.
They do not substitute an arbitrary system for the coefficient categories.
The sigma used in the representative formula is the adjunction mate of derived
scalar restriction's shift, restricted through the full integral inclusion and
then uniquely descended through rationalization. Thus it is fixed by the actual
tensor construction rather than supplied as an independent comparison.

## Main definitions and statements

* `pbcScalarCommShift`: the tensor-normalized finite-coefficient shift comparison.
* `pbcPairHasShift`: the coherent shift on the actual common-stage quotient.
* `CommonStageCalculusSpec`: the typed clause-by-clause common-stage assertion.
* `commonStageCalculus`: its specialization to the concrete PBC coefficient system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe c w u v
open CategoryTheory
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {E F G : Padic.FiniteCoefficientFields l Ω}
variable (T : Scheme.{u}) [IsNoetherian T]
  (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

/-- Signed reindexing preserves completion, bounded constructible reductions and
compatible etale origins. Source: blueprint orders 1308--1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: tensor with each finite quotient commutes with signed reindexing. Shift
all the bounded local models and all etale witnesses by the same integer; their
bounds translate by that integer and their quotient equations are unchanged.
The Koszul completion tower is shifted termwise, so its limit and unit shift too. -/
@[instance] theorem pbcIntegralStableShift (E : Padic.FiniteCoefficientFields l Ω) :
    ObjectProperty.IsStableUnderShift
      (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ℤ := by
  sorry

/-- The inherited shift remains linear for the actual constant-section action.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: scalar multiplication is degreewise multiplication on complexes. Signed
reindexing commutes with it. This passes to roofs in the ambient derived category
and restricts to the full integral subcategory. -/
@[instance] theorem pbcIntegralShiftLinear (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) :
    (shiftFunctor (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) n).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := by
  sorry

/-- The rational shift is fixed on tensor Homs, including its unit and addition
comparisons. Source: blueprint orders 1308--1309
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def PbcRationalShiftNormalized (E : Padic.FiniteCoefficientFields l Ω)
    (s : HasShift (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) ℤ) : Prop := by
  letI := s
  exact
    (∀ n : ℤ, shiftFunctor
        (PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)) n =
      ScalarLocalization.map (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
        (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E))
        (pbcStageUniformizer.{u} l Ω E)
        (shiftFunctor (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) n)) ∧
    (∀ K : PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E),
      HEq ((shiftFunctorZero
        (PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)) ℤ).hom.app
          K)
        ((pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)).map
          ((shiftFunctorZero
            (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ℤ).hom.app K.obj))) ∧
    (∀ (n m : ℤ)
        (K : PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)),
      HEq ((shiftFunctorAdd
        (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
          (pbcStageUniformizer.{u} l Ω E)) n m).hom.app
          K)
        ((pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)).map
          ((shiftFunctorAdd
            (PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) n m).hom.app K.obj)))

/-- Tensoring the integral shift and its comparisons gives the unique normalized
rational shift. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: extend each integral shift linearly on tensor Homs via ScalarLocalization.map.
Localize the integral zero and addition comparisons. Their coherence holds on
integral maps and extends to all tensors by bilinearity. The object and map
formulas and the component normalizations specify every part of HasShift uniquely. -/
theorem pbcRationalShift_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! s : HasShift (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) ℤ, PbcRationalShiftNormalized l Ω T E s := by
  sorry

/-- The rational shift has actual signed-reindexing data, uniquely normalized on
integral objects and tensor morphisms. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcRationalHasShift (E : Padic.FiniteCoefficientFields l Ω) :
    HasShift (PbcRationalCategory T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)) ℤ :=
  (pbcRationalShift_exists l Ω T E).exists.choose

/-- The tensor Hom shift is additive. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: its normalized Hom action is ScalarLocalization.map, whose mapHom is linear. -/
@[instance] theorem pbcRationalShiftAdditive (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ) :
    (shiftFunctor (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) n).Additive := by
  rw [((pbcRationalShift_exists l Ω T E).exists.choose_spec).1 n]
  infer_instance

/-- Localization commutes with shifts through the identity component comparison.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the normalized shift has the same objects and sends 1 tensor f to
1 tensor f[n]. Thus identity components are natural, and the normalized zero
and addition maps give the CommShift laws. The components imply uniqueness. -/
theorem pbcRationalizationShift_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! q : (pbcRationalization T (pbcStageDatum.{u} l Ω E)
        (pbcStageUniformizer.{u} l Ω E)).CommShift ℤ,
      (fun [qInst : (pbcRationalization T (pbcStageDatum.{u} l Ω E)
          (pbcStageUniformizer.{u} l Ω E)).CommShift ℤ] ↦
        ∀ (n : ℤ) (K : PbcBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)),
          HEq (((pbcRationalization T (pbcStageDatum.{u} l Ω E)
              (pbcStageUniformizer.{u} l Ω E)).commShiftIso n).hom.app K)
            (𝟙 ((pbcRationalization T (pbcStageDatum.{u} l Ω E)
              (pbcStageUniformizer.{u} l Ω E)).obj
                ((shiftFunctor (PbcBoundedConstructibleComplete T
                  (pbcStageDatum.{u} l Ω E)) n).obj K)))) (qInst := q) := by
  sorry

/-- The normalized identity comparison with rationalization.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcRationalizationCommShift (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcRationalization T (pbcStageDatum.{u} l Ω E) (pbcStageUniformizer.{u} l Ω E)).CommShift ℤ :=
  (pbcRationalizationShift_exists l Ω T E).exists.choose

/-- Derived scalar restriction has its canonical exact-functor shift comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcScalarRestrictCommShift (h : E ≤ F) :
    (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)).CommShift ℤ :=
  inferInstanceAs (((pbcRestrict (pbcCompletedScalarMap l Ω T h)).mapDerivedCategory).CommShift ℤ)

/-- The ambient tensor shift comparison is the mate of the canonical shift of
scalar restriction. Source: blueprint order 1307
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcAmbientScalarCommShift (h : E ≤ F) :
    (pbcAmbientScalarExtension l Ω T h).CommShift ℤ :=
  (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Ω T h)).leftAdjointCommShift ℤ

/-- The integral tensor comparison is inherited through its fully faithful inclusion.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcIntegralScalarCommShift (h : E ≤ F) :
    (pbcIntegralScalarExtension l Ω T hdim hl h).CommShift ℤ :=
  Functor.CommShift.ofComp
    (F := pbcIntegralScalarExtension l Ω T hdim hl h)
    (G := ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω F)))
    (Iso.refl (ObjectProperty.ι
      (PbcIsBoundedConstructibleComplete T (pbcStageDatum.{u} l Ω E)) ⋙
        pbcAmbientScalarExtension l Ω T h)) ℤ

/-- The rational tensor shift comparison is fixed by the actual integral comparison.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: localize the ambient tensor shift component on each integral object and
conjugate by the normalized integral/rational square. Naturality extends from
integral morphisms to their fractions. The integral zero and addition laws
localize, and every rational object is integral, proving uniqueness. -/
theorem pbcScalarShift_exists (h : E ≤ F) :
    ∃! q : (pbcScalarExtension l Ω T hdim hl h).CommShift ℤ,
      (fun [qInst : (pbcScalarExtension l Ω T hdim hl h).CommShift ℤ] ↦
        NatTrans.CommShift (pbcScalarIntegralComparison l Ω T hdim hl h).hom ℤ)
          (qInst := q) := by
  sorry

/-- The specified sigma comparison for finite coefficient extension.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcScalarCommShift (h : E ≤ F) :
    (pbcScalarExtension l Ω T hdim hl h).CommShift ℤ :=
  (pbcScalarShift_exists l Ω T hdim hl h).exists.choose

/-- Tensor balancing commutes with the normalized sigma comparisons.
Source: blueprint order 1307 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the ambient associator is the mate of identity-on-sections restriction
composition, which commutes with signed reindexing. Restrict and rationalize
that equation; the normalizations of both comparisons preserve it. -/
@[instance] theorem pbcScalarAssociatorCommShift (h : E ≤ F) (k : F ≤ G) :
    NatTrans.CommShift (pbcScalarAssociator l Ω T hdim hl h k).hom ℤ := by
  sorry

/-- The actual raw rational stages have finite biproducts and a zero object.
Source: blueprint orders 1308--1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the zero complex and finite sums satisfy all three defining integral
conditions: their reductions, local finite models and etale witnesses are the
corresponding sums. Finite sums commute with the Koszul limit. Their inclusion
and projection maps obey the biproduct equations in the full subcategory.
Tensor these maps with one; the same five equations hold in the raw localization. -/
@[instance] theorem pbcStageFiniteBiproducts (E : Padic.FiniteCoefficientFields l Ω) :
    Limits.HasFiniteBiproducts (PbcRationalCategory T (pbcStageDatum.{u} l Ω E)
      (pbcStageUniformizer.{u} l Ω E)) := by
  sorry

end AlgebraicGeometry.Scheme

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)



section Shift
variable [stageShift : ∀ i, HasShift (C i) ℤ]
    [transitionShift : ∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [associatorShift : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]
include associatorShift

/-- Compatibility of the shift comparisons with associators.
Source: blueprint scalar-extension shifts and common-stage shift
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: expand the composite functor's shift comparison in the CommShift equation
for the associator. Its component equation is exactly the displayed compatibility. -/
theorem pbcStageShift_coherence (n : ℤ) {i j k : I}
    (h : i ≤ j) (h' : j ≤ k) (X : C i) :
    (S.T h').map (((S.T h).commShiftIso n).hom.app X) ≫
      ((S.T h').commShiftIso n).hom.app ((S.T h).obj X) ≫
        (shiftFunctor (C k) n).map ((S.assoc h h').hom.app X) =
    (S.assoc h h').hom.app ((shiftFunctor (C i) n).obj X) ≫
      ((S.T (h.trans h')).commShiftIso n).hom.app X := by
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] using
    NatTrans.shift_app_comm (S.assoc h h').hom n X

/-- Shifting each finite stage gives a morphism of the actual stage system.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcStageShift (n : ℤ) : S.Morphism S where
  Φ i := shiftFunctor (C i) n
  β h := (S.T h).commShiftIso n
  coh h h' X := pbcStageShift_coherence S n h h' X

/-- The induced shift sends (E,K) literally to (E,K[n]) and acts on representatives
by the prescribed shift-comparison conjugation.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShift (n : ℤ) : S.PairCategory ⥤ S.PairCategory :=
  (pbcStageShift S n).functor

/-- Naturality of the stagewise zero-shift comparison on common-stage classes.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: represent f at one stage. The CommShift zero axiom identifies its conjugated
shift with f, using naturality of the finite-stage zero comparison. Applying the
common-stage quotient yields the displayed equation. -/
theorem pbcPairShiftZero_naturality {X Y : S.PairCategory} (f : X ⟶ Y) :
    (pbcPairShift S 0).map f ≫
      (S.ι Y.stage).map ((shiftFunctorZero (C Y.stage) ℤ).hom.app Y.obj) =
    (S.ι X.stage).map ((shiftFunctorZero (C X.stage) ℤ).hom.app X.obj) ≫ f := by
  induction f using PairCategory.hom_induction with
  | h k hX hY u =>
    change (pbcStageShift S 0).functor.map (PairCategory.mkHom k hX hY u) ≫ _ = _
    rw [Morphism.functor_map_mkHom, ι_map_eq hY, ι_map_eq hX]
    rw [PairCategory.mkHom_comp_mkHom, PairCategory.mkHom_comp_mkHom]
    congr 1
    dsimp only [Morphism.functor, pbcStageShift]
    simp [Morphism.mapAt, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero, Category.assoc, ← Functor.map_comp]

/-- The zero comparison is the actual image of the finite-stage zero comparison.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShiftZero : pbcPairShift S 0 ≅ 𝟭 S.PairCategory :=
  NatIso.ofComponents
    (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorZero (C X.stage) ℤ).app X.obj))
    (fun f ↦ pbcPairShiftZero_naturality S f)

/-- Naturality of the stagewise addition comparison on morphism classes.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: use one representative of f. The CommShift addition axiom rewrites both
composites into the same shifted representative. Finite-stage naturality of
shiftFunctorAdd proves equality before passing to the common-stage quotient. -/
theorem pbcPairShiftAdd_naturality (n m : ℤ) {X Y : S.PairCategory} (f : X ⟶ Y) :
    (pbcPairShift S (n + m)).map f ≫
      (S.ι Y.stage).map ((shiftFunctorAdd (C Y.stage) n m).hom.app Y.obj) =
    (S.ι X.stage).map ((shiftFunctorAdd (C X.stage) n m).hom.app X.obj) ≫
      (pbcPairShift S n ⋙ pbcPairShift S m).map f := by
  induction f using PairCategory.hom_induction with
  | h k hX hY u =>
    change (pbcStageShift S (n + m)).functor.map (PairCategory.mkHom k hX hY u) ≫ _ =
      _ ≫ (pbcStageShift S m).functor.map
        ((pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY u))
    rw [Morphism.functor_map_mkHom, Morphism.functor_map_mkHom,
      Morphism.functor_map_mkHom, ι_map_eq hY, ι_map_eq hX]
    rw [PairCategory.mkHom_comp_mkHom, PairCategory.mkHom_comp_mkHom]
    congr 1
    dsimp only [Morphism.functor, pbcStageShift]
    simp [Morphism.mapAt, Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_inv_app,
      Category.assoc, ← Functor.map_comp]
    simp only [Functor.map_comp, Category.assoc]

/-- The addition comparison is the actual image of the finite-stage comparison.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShiftAdd (n m : ℤ) :
    pbcPairShift S (n + m) ≅ pbcPairShift S n ⋙ pbcPairShift S m :=
  NatIso.ofComponents
    (fun X ↦ (S.ι X.stage).mapIso ((shiftFunctorAdd (C X.stage) n m).app X.obj))
    (fun f ↦ pbcPairShiftAdd_naturality S n m f)

/-- Coherence of the actual descended shift comparisons.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: each comparison component is the stage inclusion applied to the corresponding
finite-stage shift comparison. The shift of an included map is its included finite-stage
shift. Thus the three equations are the associativity and two unit equations of the
finite-stage HasShift structure, preserved by the inclusion functor. -/
theorem pbcPairShift_laws :
    (∀ (a b c : ℤ) (X : S.PairCategory),
      (pbcPairShiftAdd S (a + b) c).hom.app X ≫
        (pbcPairShift S c).map ((pbcPairShiftAdd S a b).hom.app X) =
      eqToHom (by rw [add_assoc]) ≫ (pbcPairShiftAdd S a (b + c)).hom.app X ≫
        (pbcPairShiftAdd S b c).hom.app ((pbcPairShift S a).obj X)) ∧
    (∀ (n : ℤ) (X : S.PairCategory),
      (pbcPairShiftAdd S 0 n).hom.app X =
        eqToHom (by dsimp; rw [zero_add]) ≫
          (pbcPairShift S n).map ((pbcPairShiftZero S).inv.app X)) ∧
    (∀ (n : ℤ) (X : S.PairCategory),
      (pbcPairShiftAdd S n 0).hom.app X =
        eqToHom (by dsimp; rw [add_zero]) ≫
          (pbcPairShiftZero S).inv.app ((pbcPairShift S n).obj X)) := by
  constructor
  · intro a b c X
    have h := congrArg (fun f ↦ (S.ι X.stage).map f)
      (shiftFunctorAdd_assoc_hom_app a b c X.obj)
    simpa [pbcPairShiftAdd, pbcPairShift, pbcPairShiftZero,
      Morphism.functor_map_ι, pbcStageShift, shiftFunctorAdd',
      Functor.map_comp, eqToHom_map,
      Morphism.functor_obj] using h
  constructor
  · intro n X
    have h := congrArg (fun f ↦ (S.ι X.stage).map f)
      (shiftFunctorAdd_zero_add_hom_app n X.obj)
    simpa [pbcPairShiftAdd, pbcPairShift, pbcPairShiftZero,
      Morphism.functor_map_ι, pbcStageShift, Functor.map_comp, eqToHom_map,
      Morphism.functor_obj] using h
  · intro n X
    have h := congrArg (fun f ↦ (S.ι X.stage).map f)
      (shiftFunctorAdd_add_zero_hom_app n X.obj)
    simpa [pbcPairShiftAdd, pbcPairShift, pbcPairShiftZero,
      pbcStageShift, Functor.map_comp, eqToHom_map,
      Morphism.functor_obj] using h

/-- The common-stage shift with the actual finite-stage unit and addition maps.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcPairShiftCore : ShiftMkCore S.PairCategory ℤ where
  F := pbcPairShift S
  zero := pbcPairShiftZero S
  add := pbcPairShiftAdd S
  assoc_hom_app := (pbcPairShift_laws S).1
  zero_add_hom_app := (pbcPairShift_laws S).2.1
  add_zero_hom_app := (pbcPairShift_laws S).2.2

/-- The canonical HasShift structure; its object action is (E,K) ↦ (E,K[n]).
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
@[instance_reducible] def pbcPairHasShift : HasShift S.PairCategory ℤ :=
  hasShiftMk S.PairCategory ℤ (pbcPairShiftCore S)

attribute [instance] pbcPairHasShift

/-- The canonical comparison for the finite-stage inclusion is the inverse of the
upstream stage-morphism comparison. Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
def pbcStageInclusionShiftIso (i : I) (n : ℤ) :
    shiftFunctor (C i) n ⋙ S.ι i ≅ S.ι i ⋙ shiftFunctor S.PairCategory n :=
  ((pbcStageShift S n).ιCompFunctorIso i).symm

/-- The inclusion comparisons retain the zero and addition normalization of the stages.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: the comparison components for an included object are identities in the pair
category. Its compatibility with the zero and addition comparisons follows because
those were defined as the actual images of the same finite-stage comparisons. -/
theorem pbcStageInclusionShift_laws (i : I) :
    pbcStageInclusionShiftIso S i 0 = Functor.CommShift.isoZero (S.ι i) ℤ ∧
    ∀ n m : ℤ, pbcStageInclusionShiftIso S i (n + m) =
      Functor.CommShift.isoAdd (pbcStageInclusionShiftIso S i n)
        (pbcStageInclusionShiftIso S i m) := by
  constructor
  · ext X
    simp only [Functor.CommShift.isoZero_hom_app]
    rw [show shiftFunctorZero S.PairCategory ℤ = pbcPairShiftZero S from rfl]
    simp [pbcStageInclusionShiftIso, Morphism.ιCompFunctorIso,
      pbcPairShiftZero, ι_obj, Morphism.functor_obj, pbcStageShift, ← Functor.map_comp]
  · intro n m
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app]
    rw [show shiftFunctorAdd S.PairCategory n m = pbcPairShiftAdd S n m from rfl]
    simp [pbcStageInclusionShiftIso, Morphism.ιCompFunctorIso,
      pbcPairShiftAdd, ι_obj, Morphism.functor_obj, pbcStageShift, ← Functor.map_comp]

/-- Finite-stage inclusions commute with the actual common-stage shift.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcStageInclusionCommShift (i : I) : (S.ι i).CommShift ℤ where
  commShiftIso := pbcStageInclusionShiftIso S i
  commShiftIso_zero := (pbcStageInclusionShift_laws S i).1
  commShiftIso_add := (pbcStageInclusionShift_laws S i).2

section AdditiveShift
variable [stagePreadditive : ∀ i, Preadditive (C i)]
    [transitionAdditive : ∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [stageShiftAdditive : ∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
include stagePreadditive transitionAdditive stageShiftAdditive

/-- The descended shift preserves the actual common-stage addition formula.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: represent two morphisms at a common stage. The stage shift is additive,
and pre- and post-composition by its comparison isomorphisms preserve sums.
The common-stage Hom quotient therefore identifies the shifted sum with the
sum of the shifted representatives. -/
theorem pbcPairShift_additive (n : ℤ) : (shiftFunctor S.PairCategory n).Additive := by
  have norm := (S.pairPreadditive_exists).exists.choose_spec
  constructor
  intro X Y f g
  obtain ⟨k, _, hX, hY, _, _, u, v, rfl, rfl⟩ :=
    PairCategory.exists_common_stage f g X.stage
  rw [← (norm X Y k hX hY u v).1]
  change (pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY (u + v)) =
    (pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY u) +
      (pbcStageShift S n).functor.map (PairCategory.mkHom k hX hY v)
  simp only [Morphism.functor_map_mkHom]
  dsimp only [Morphism.mapAt, pbcStageShift, Morphism.functor]
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  exact (norm ((pbcPairShift S n).obj X) ((pbcPairShift S n).obj Y)
    k hX hY _ _).1

attribute [instance] pbcPairShift_additive

variable [∀ i, Limits.HasZeroObject (C i)]

/-- An included finite-stage zero object is a genuine zero object of the pair category.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: move a morphism from or to this object to any common stage. Additivity
of transition functors sends a zero object to a zero object, so its arrow is
uniquely zero there. The common-stage quotient preserves this equality. -/
theorem pbcPairZero_isZero (i : I) :
    Limits.IsZero ((S.ι i).obj (0 : C i)) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  rw [← (S.ι i).map_id]
  change PairCategory.mkHom (X := ⟨i, (0 : C i)⟩)
    (Y := ⟨i, (0 : C i)⟩) i (le_refl i) (le_refl i)
      ((S.T (le_refl i)).map (𝟙 (0 : C i))) = 0
  have e : 𝟙 (0 : C i) = 0 := (Limits.isZero_zero (C i)).eq_zero_of_src _
  rw [e, Functor.map_zero]
  exact ((S.pairPreadditive_exists).exists.choose_spec _ _ i _ _ 0 0).2

/-- Existence of a zero object, witnessed by the image of any finite-stage zero.
Source: blueprint common-stage calculus
(blueprint: prop-weil-pbc-common-stage-calculus). -/
instance pbcPairHasZeroObject [Nonempty I] : Limits.HasZeroObject S.PairCategory :=
  (pbcPairZero_isZero S (Classical.choice (inferInstance : Nonempty I))).hasZeroObject

end AdditiveShift
end Shift

section FiniteDiagrams
variable [Nonempty I]

/-- Finite graphs of objects and arrows have simultaneous representatives.
Source: blueprint common-stage calculus (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: choose one representative for each of the finitely many arrows. Directedness
provides one upper bound for their stages and for the finitely many object stages.
Transport every representative to that upper bound. The associator cocycle identifies
its quotient class with the original arrow. The empty graph uses any base stage. -/
theorem pbcFiniteGraph_representation {A B : Type w} [Finite A] [Finite B]
    (X : A → S.PairCategory) (s t : B → A)
    (f : ∀ b : B, X (s b) ⟶ X (t b)) :
    ∃ (M : I) (h : ∀ a : A, (X a).stage ≤ M)
      (u : ∀ b : B, (X (s b)).toStage (h (s b)) ⟶
        (X (t b)).toStage (h (t b))),
      ∀ b : B, PairCategory.mkHom M (h (s b)) (h (t b)) (u b) = f b := by
  classical
  choose k hX hY hk using fun b ↦ PairCategory.exists_mkHom_eq (f b)
  obtain ⟨M, hM⟩ := Finite.exists_le (fun q : A ⊕ B ↦
    Sum.elim (fun a ↦ (X a).stage) k q)
  let h : ∀ a : A, (X a).stage ≤ M := fun a ↦ hM (Sum.inl a)
  have hu : ∀ b : B, ∃ u : (X (s b)).toStage (h (s b)) ⟶
      (X (t b)).toStage (h (t b)),
      PairCategory.mkHom M (h (s b)) (h (t b)) u = f b := by
    intro b
    obtain ⟨u, e⟩ := hk b M (hM (Sum.inr b))
    exact ⟨u, e.symm⟩
  choose u hu using hu
  exact ⟨M, h, u, hu⟩

variable [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, Limits.HasFiniteBiproducts (C i)]

/-- Finite direct sums descend without adjoining new objects.
Source: blueprint common-stage calculus (blueprint: prop-weil-pbc-common-stage-calculus).
Proof: transport the finitely many objects to one stage and take their biproduct
there. Include its injections and projections in the pair category. To test the
biproduct equations or its universal property, transport the finitely many arrows
to one further stage. Additive transitions preserve finite biproducts, so the
finite-stage equations give exactly the required pair-category equations. -/
@[instance] theorem pbcPairFiniteBiproducts : Limits.HasFiniteBiproducts S.PairCategory := by
  sorry
end FiniteDiagrams

end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
    [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, HasShift (C i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]

/-- All finitely many asserted equalities are detected simultaneously at one
further stage. Source: blueprint order 1309
(blueprint: prop-weil-pbc-common-stage-calculus).
Proof: choose the eventual-equality witness for each equation and take an upper
bound of their finitely many stages and the prescribed starting stage. The
transport cocycle preserves each equality. Conversely the common stage witnesses
each quotient equality. The empty family only requires an upper bound of m. -/
theorem pbcFiniteEqualities_detection {A : Type c} [Finite A]
    (X Y : A → S.PairCategory)
    (r s : ∀ a : A, PairCategory.Rep (X a) (Y a)) (m : I) :
    (∀ a : A, PairCategory.mkHom (r a).k (r a).hX (r a).hY (r a).u =
      PairCategory.mkHom (s a).k (s a).hX (s a).hY (s a).u) ↔
    ∃ (N : I) (_ : m ≤ N) (hr : ∀ a : A, (r a).k ≤ N)
      (hs : ∀ a : A, (s a).k ≤ N),
      ∀ a : A, S.tr (hr a) (r a).u = S.tr (hs a) (s a).u := by
  classical
  constructor
  · intro e
    have he : ∀ a : A, ∃ (p : I) (hr : (r a).k ≤ p) (hs : (s a).k ≤ p),
        S.tr hr (r a).u = S.tr hs (s a).u :=
      fun a ↦ (PairCategory.mkHom_eq_mkHom_iff' _ _).mp (e a)
    choose p hr hs he using he
    obtain ⟨N, hN⟩ := Finite.exists_le (fun a : Option A ↦ a.elim m p)
    refine ⟨N, hN none, fun a ↦ (hr a).trans (hN (some a)),
      fun a ↦ (hs a).trans (hN (some a)), ?_⟩
    intro a
    exact PairCategory.Rep.rel_of_eq (hr a) (hs a) (he a) (hN (some a))
  · rintro ⟨N, _, hr, hs, e⟩ a
    exact (PairCategory.mkHom_eq_mkHom_iff' _ _).mpr ⟨N, hr a, hs a, e a⟩

/-- A literal clause-by-clause specification of the common-stage calculus, using
actual typed representatives, quotient morphisms and sigma comparisons.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus). -/
structure CommonStageCalculusSpec : Prop where
  relation : ∀ X Y : S.PairCategory,
    _root_.Equivalence (PairCategory.Rep.Rel (X := X) (Y := Y))
  transport_add : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (h : r.k ≤ N) (v : X.toStage r.hX ⟶ Y.toStage r.hY),
    S.tr h (r.u + v) = S.tr h r.u + S.tr h v
  transport_cocycle : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N P : I} (h : r.k ≤ N) (k : N ≤ P),
    S.tr k (S.tr h r.u) = S.tr (h.trans k) r.u
  operations : S.PairPreadditiveNormalized (inferInstance : Preadditive S.PairCategory)
  negation : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y),
    -(PairCategory.mkHom r.k r.hX r.hY r.u) =
      PairCategory.mkHom r.k r.hX r.hY (-r.u)
  identity : ∀ X : S.PairCategory,
    𝟙 X = PairCategory.mkHom X.stage (le_refl _) (le_refl _) (𝟙 _)
  composition : ∀ {X Y Z : S.PairCategory}
    (r : PairCategory.Rep X Y) (s : PairCategory.Rep Y Z)
    (N : I) (hr : r.k ≤ N) (hs : s.k ≤ N),
    PairCategory.mkHom r.k r.hX r.hY r.u ≫ PairCategory.mkHom s.k s.hX s.hY s.u =
      PairCategory.mkHom N (r.hX.trans hr) (s.hY.trans hs) (S.tr hr r.u ≫ S.tr hs s.u)
  biproducts : Limits.HasFiniteBiproducts S.PairCategory
  finite_diagram : ∀ {A B : Type w} [Finite A] [Finite B]
    (X : A → S.PairCategory) (s t : B → A) (f : ∀ b : B, X (s b) ⟶ X (t b)),
    ∃ (M : I) (h : ∀ a : A, (X a).stage ≤ M)
      (u : ∀ b : B, (X (s b)).toStage (h (s b)) ⟶ (X (t b)).toStage (h (t b))),
      ∀ b : B, PairCategory.mkHom M (h (s b)) (h (t b)) (u b) = f b
  equalities : ∀ {A : Type w} [Finite A] (X Y : A → S.PairCategory)
    (r s : ∀ a : A, PairCategory.Rep (X a) (Y a)) (m : I),
    (∀ a : A, PairCategory.mkHom (r a).k (r a).hX (r a).hY (r a).u =
      PairCategory.mkHom (s a).k (s a).hX (s a).hY (s a).u) ↔
    ∃ (N : I) (_ : m ≤ N) (hr : ∀ a : A, (r a).k ≤ N)
      (hs : ∀ a : A, (s a).k ≤ N),
      ∀ a : A, S.tr (hr a) (r a).u = S.tr (hs a) (s a).u
  shift_objects : ∀ X : S.PairCategory,
    (shiftFunctor S.PairCategory (1 : ℤ)).obj X =
      ⟨X.stage, (shiftFunctor (C X.stage) (1 : ℤ)).obj X.obj⟩
  shift_maps : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y),
    (shiftFunctor S.PairCategory (1 : ℤ)).map
        (PairCategory.mkHom r.k r.hX r.hY r.u) =
      PairCategory.mkHom
        (X := (shiftFunctor S.PairCategory (1 : ℤ)).obj X)
        (Y := (shiftFunctor S.PairCategory (1 : ℤ)).obj Y) r.k r.hX r.hY
        (((S.T r.hX).commShiftIso (1 : ℤ)).hom.app X.obj ≫
          (shiftFunctor (C r.k) (1 : ℤ)).map r.u ≫
            ((S.T r.hY).commShiftIso (1 : ℤ)).inv.app Y.obj)
  shift_additive : (shiftFunctor S.PairCategory (1 : ℤ)).Additive
  inverse_additive : (shiftFunctor S.PairCategory (-1 : ℤ)).Additive
  inverse_left : Nonempty
    (shiftFunctor S.PairCategory (-1 : ℤ) ⋙ shiftFunctor S.PairCategory (1 : ℤ) ≅ 𝟭 _)
  inverse_right : Nonempty
    (shiftFunctor S.PairCategory (1 : ℤ) ⋙ shiftFunctor S.PairCategory (-1 : ℤ) ≅ 𝟭 _)
  inclusion_comparison : ∀ i : I, Nonempty ((S.ι i).CommShift ℤ)
  inclusion_normalization : ∀ (i : I) (n : ℤ),
    (S.ι i).commShiftIso n = pbcStageInclusionShiftIso S i n

private theorem commonStageCalculus_generic [∀ i, Limits.HasFiniteBiproducts (C i)]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] :
    CommonStageCalculusSpec S := by
  have norm := (S.pairPreadditive_exists).exists.choose_spec
  refine {
    relation := fun X Y ↦ PairCategory.Rep.rel_equivalence
    transport_add := ?_
    transport_cocycle := fun {X Y} r {N P} h k ↦ tr_tr h k r.u
    operations := norm
    negation := ?_
    identity := fun X ↦ PairCategory.id_eq_mkHom X (le_refl _)
    composition := fun {X Y Z} r s N hr hs ↦ PairCategory.mkHom_comp_mkHom' r.u s.u hr hs
    biproducts := inferInstance
    finite_diagram := pbcFiniteGraph_representation S
    equalities := pbcFiniteEqualities_detection S
    shift_objects := fun X ↦ rfl
    shift_maps := fun {X Y} r ↦ rfl
    shift_additive := inferInstance
    inverse_additive := inferInstance
    inverse_left := ⟨shiftFunctorCompIsoId S.PairCategory (-1 : ℤ) 1 (by decide)⟩
    inverse_right := ⟨shiftFunctorCompIsoId S.PairCategory (1 : ℤ) (-1) (by decide)⟩
    inclusion_comparison := fun i ↦ ⟨inferInstance⟩
    inclusion_normalization := fun i n ↦ rfl }
  · intro X Y r N h v
    simp only [tr, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  · intro X Y r
    apply neg_eq_of_add_eq_zero_left
    rw [← (norm X Y r.k r.hX r.hY (-r.u) r.u).1, neg_add_cancel]
    exact (norm X Y r.k r.hX r.hY 0 0).2

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

open CategoryTheory.StageSystem

/-- Common-stage additive and shift calculus for the concrete finite coefficient
system of the node, with no arbitrary stage-category parameter.
Source: blueprint order 1309 (blueprint: prop-weil-pbc-common-stage-calculus).
Proof plan: (1) Integral finite sums and signed shifts preserve K-flatness,
completion and the normalized reduction towers. (2) The full integral categories
and their tensor-Hom rationalizations inherit the finite-stage additive structures.
(3) Expand associator-conjugated transport; the pentagon and naturality cancel
adjacent inverse associators, proving its cocycle and additivity. (4) Reflexivity
and symmetry are immediate; transitivity uses a compositum of the two witnesses.
(5) Move all representatives to one stage; cancellation proves compatibility of
composition, and additivity proves independence of sums and negatives. (6) The
included finite-stage zero and binary biproducts satisfy their five equations.
(7) The identity representatives give the isomorphisms to scalar-extended objects.
(8) Bound the finitely many arrow stages and equality witnesses simultaneously;
the empty diagram uses the base field. (9) Naturality of sigma and its associator
compatibility show that sigma-conjugated shift commutes with transport. (10) The
negative comparison is obtained by shifting the positive comparison inversely;
the adjacent sigma factors cancel in both inverse composites. Stage units give
the specified inclusion comparison.

Detailed proof from the DAG, including its dependency citations:

Step 1. We first supply the finite-stage additive and shift laws used below. In the ambient
derived category [def-weil-abstract-derived-category], binary direct sums are biproducts, and the
shift is the reindexing complex with negated differential. Tensoring module sheaves distributes
over a binary sum: the inverse maps are $(x,y)\otimes z\mapsto(x\otimes z,y\otimes z)$ and
$(x\otimes z,y\otimes w)\mapsto(x,0)\otimes z+(0,y)\otimes w$, first on sections and then on
sheafifications [def-pur-sheaf-tensor-product]. The total-tensor formula
[def-pc-tensor-complex-sheaves] gives the corresponding chain isomorphisms and commutation with
shifts: the identification $P[1]\otimes Q\to(P\otimes Q)[1]$ is the identity on reindexed
summands; for $P\otimes Q[1]\to(P\otimes Q)[1]$ multiply the summand of first-factor degree $p$ by
$(-1)^p$. In the latter formula the first differential changes the multiplier from $(-1)^p$ to
$(-1)^{p+1}$, and the second differential already has the negated differential of $Q$, giving
precisely the negative total differential. Reversing these identifications gives the
negative-shift formulas. By the definition of K-flatness, zero, finite sums and shifts of K-flat
complexes remain K-flat: tensoring an acyclic complex gives respectively zero, a finite sum of
acyclic complexes, or a shift of one [def-pc-kflat-complex]. Thus K-flat resolutions
[lem-pc-kflat-resolution] compute reductions and the Koszul towers
[def-weil-pbc-intrinsic-completion] of sums and shifts by sums and shifts of those of their
inputs. The coefficient-datum reduction functor [def-weil-pbc-adic-coefficient-datum] supplies the
natural reduction normalizations; the foregoing chain isomorphisms commute with the transition
maps $1\otimes q$.

Step 2. For the finite-stage category laws used below, use the full stated hypothesis that
$T_{F/E}:\mathcal C_E(T)\to\mathcal C_F(T)$ is an exact functor [prop-weil-pbc-scalar-extension],
not merely flatness of $F/E$. By [def-weil-triangulated-category], an exact functor is an additive
functor between pre-triangulated categories, whose categories are additive and whose shifts are
additive automorphisms. Apply this assertion with $F=E$, where $T_{E/E}=1$. It supplies the
finite-stage zero object, binary biproducts, Hom abelian groups, bilinear composition and inverse
shifts that this proof needs. Thus we use the stage structures included in the existing exactness
package; we do not independently assert that inverse image of an infinite completed-module limit
commutes with that limit on a refined stratum. The shift is the signed reindexing of
[def-weil-abstract-derived-category] on the full integral subcategory
[def-weil-pbc-bounded-constructible-complete] and the same objects in
[def-weil-pbc-rational-category]. It is $\mathcal O_E$-linear by its chain formula. The Hom
localization [def-weil-linear-scalar-localization] acts by $f\otimes a\mapsto f[1]\otimes a$, so
identities, composition, addition and the inverse shift descend. The biproduct maps satisfy their
five equations after tensoring with $1$. These explain the concrete finite-stage structures used
in the common-stage calculations without proving, or assuming, any identification with Stacks'
constant-coefficient category.

Step 3. For transport write $A_X=a_{N,M,E,K}$, $A_Y=a_{N,M,F,L}$, $B_X=a_{P,N,E,K}$,
$B_Y=a_{P,N,F,L}$, $C_X=a_{P,M,E,K}$, $C_Y=a_{P,M,F,L}$. Put $H=T_{N/M}$, $G=T_{P/N}$,
$J=T_{P/M}$, and $b=a_{P,N,M}:GH\xrightarrow{\sim}J$. The pentagon in
[prop-weil-pbc-scalar-extension] gives $B_XG(A_X)=C_Xb_{T_{M/E}K}$ and the analogous equation for
$Y$. Naturality of $b$ gives $b_YGH(u)=J(u)b_X$. Substituting in the transport formula of
[def-weil-pbc-finite-stage-pair-category] yields $$
(u_N)_P=B_YG(A_Y)GH(u)G(A_X)^{-1}B_X^{-1}=C_YJ(u)C_X^{-1}=u_P. $$ The unit equations give $u_M=u$.
Exact functors are additive by [def-weil-triangulated-category], so each $T_{N/M}$ is additive.
Distributivity of composition with fixed associators now gives $(u+v)_N=u_N+v_N$, $0_N=0$, and
$(-u)_N=-u_N$.

Step 4. Reflexivity has witness $M$ since $u_M=u$, and symmetry follows by reversing the equality.
If $(M,u)\sim(N,v)$ at $P_1$ and $(N,v)\sim(Q,w)$ at $P_2$, the finite compositum $P=P_1P_2$
exists by the directed-field data in [def-weil-pbc-finite-stage-pair-category]. Transporting both
equalities and using step 3 gives $u_P=v_P=w_P$, which witnesses transitivity. No injectivity of
the transport maps is assumed.

Step 5. For two composable arrows at $M$, the transported composite satisfies $$
v_Nu_N=a_ZT(v)a_Y^{-1}a_YT(u)a_X^{-1}=a_ZT(vu)a_X^{-1}=(vu)_N, $$ and transport of an identity is
an identity. If inputs are replaced by equivalent representatives, take the compositum of their
equality witnesses and the two proposed operation fields; by step 3 the corresponding inputs
coincide there. The displayed identity and additivity then make the outputs of addition, negation
and composition coincide there. Thus the operations in [def-weil-pbc-finite-stage-pair-category]
are independent of the field and representatives. All abelian-group, associativity, identity and
bilinearity equations are verified by putting their finitely many representatives over one stage
and applying the finite-stage laws established in step 2.

Step 6. There is also a zero object and every binary biproduct, as required by
[def-weil-additive-category]. Take $Z=(\Ql,0)$. Scalar extension sends the zero identity to the
zero identity, so every transport of $0$ is a zero object; every representative to or from $Z$ is
therefore zero. For $X=(E,K)$ and $Y=(F,L)$ choose $M\supseteq E,F$ and take $B=(M,T_{M/E}K\oplus
T_{M/F}L)$. Represent the four inclusions and projections at $M$ by the finite-stage ones. The
equations $p_ii_j=\delta_{ij}$ and $i_1p_1+i_2p_2=1$ hold at $M$, hence on classes by step 5; the
identity of $X$ is represented there by the identity of $T_{M/E}K$, and likewise for $Y$. These
prove that $B$ is a biproduct. Together with the Hom abelian groups and bilinear composition of
step 5, this makes $\mathcal P_T$ additive.

Step 7. For $X=(E,K)$ and $N\supseteq E$ construct $\gamma_{N,X}:X\to(N,T_{N/E}K)$ by the
representative $(N,1_{T_{N/E}K})$; the same identity represents a map in the opposite direction.
By the unit equations their composites are the two identity classes, so these maps are inverse.
For $f=[M,u]:X\to Y$ and $N\supseteq M$, all three maps in $\gamma_{N,Y}f\gamma_{N,X}^{-1}$ are
represented at $N$; the outer maps are identities and the middle map is $u_N$. Thus this conjugate
is $j_N(u_N)$. This constructs the object identifications mentioned but not defined in the
blueprint proof.

Step 8. For a finite diagram take the compositum of the coefficient fields of its objects and the
representative fields of its arrows, and use step 7 to replace every object by its isomorphic
scalar extension at this field. By step 5 all specified composites are represented by the
corresponding composites there. An asserted equality of parallel composites holds in $\mathcal
P_T$ if and only if its two representatives become equal at a further field, by the equivalence
relation in [def-weil-pbc-finite-stage-pair-category]. Take the compositum of the witnesses for
the finitely many asserted equalities. Step 3 preserves each witness equality at this common
field, giving all equations simultaneously. The reverse implication uses that field as a witness
for each equality. An empty diagram may use $\Ql$. If just the list of equalities is empty, no
witness extension is required: keep the field already containing the diagram's object and arrow
fields. Representation of objects is through the displayed isomorphisms, not literal equality of
pairs.

Step 9. Write $s_X=\sigma_{M/E,K}$, $s_Y=\sigma_{M/F,L}$, $h_X=\sigma_{N/M,T_{M/E}K}$,
$h_Y=\sigma_{N/M,T_{M/F}L}$, and let $A_X=a_{N,M,E,K}$ and $A'_X=a_{N,M,E,K[1]}$, with analogous
notation for $Y$. Associator compatibility of the natural shift comparisons
[prop-weil-pbc-scalar-extension] is $$ \sigma_{N/E,K}A'_X=A_X[1]h_XT_{N/M}(s_X). $$ Naturality
gives $h_YT_{N/M}(u[1])=(T_{N/M}u)[1]h_X$. Insert both identities and the transport formula into
$S_N(u_N)$, where $S_M(u)=s_Y^{-1}u[1]s_X$; the adjacent inverse comparisons cancel, leaving $$
S_N(u_N)=A'_YT_{N/M}(S_M(u))(A'_X)^{-1}. $$ Consequently equivalent representatives give
equivalent shifted representatives. At a common stage, $S_M(v)S_M(u)=S_M(vu)$ by cancellation of
the middle $s_Ys_Y^{-1}$, $S_M(1)=1$, and $S_M(u+v)=S_M(u)+S_M(v)$ by the additive finite-stage
shift of step 2. Thus the formula in the statement defines a well-defined additive endofunctor.

Step 10. Compute with the signed chain-reindexing shifts, for which $K[-1][1]=K=K[1][-1]$ and the
inverse identities on chain maps are literal [def-weil-abstract-derived-category]; in a choice
with inverse identifications, insert the corresponding natural unit and counit in these equations.
Write $q_{M/E,K}=(\sigma_{M/E,K[-1]})[-1]:(T_{M/E}K)[-1]\to T_{M/E}(K[-1])$ and
$\tau_{M/E,K}=q_{M/E,K}^{-1}$. Define $R_M(u)=\tau_{M/F,L}^{-1}u[-1]\tau_{M/E,K}$. For $H=T_{N/M}$
put $A_X=a_{N,M,E,K}$ and $A_X^-=a_{N,M,E,K[-1]}$, with analogous notation for $Y$. Apply $[-1]$
to the positive comparison equation of step 9 at $K[-1]$ and use naturality of the $H$ comparison
at $\sigma_{M/E,K[-1]}$. It reads $$q_{N/E,K}A_X[-1]=A_X^-H(q_{M/E,K})q_{N/M,T_{M/E}K}.$$
Multiplying by inverse $q$ factors gives
$$\tau_{N/E,K}A_X^-=A_X[-1]\tau_{N/M,T_{M/E}K}H(\tau_{M/E,K}).$$ Naturality gives
$\tau_{N/M,T_{M/F}L}H(u[-1])=(Hu)[-1]\tau_{N/M,T_{M/E}K}$. Substitution cancels the two middle
$\tau$ factors and yields $$R_N(u_N)=A_Y^-H(R_M(u))(A_X^-)^{-1}.$$ This is the equality required
for representative independence. At one stage the equations are explicitly
$R_M(v)R_M(u)=\tau_Z^{-1}v[-1]\tau_Y\tau_Y^{-1}u[-1]\tau_X=R_M(vu)$, $R_M(1)=\tau_X^{-1}\tau_X=1$,
and $R_M(u+v)=\tau_Y^{-1}(u[-1]+v[-1])\tau_X=R_M(u)+R_M(v)$; step 5 passes them to classes. For
the inverse composites put $s_X=\sigma_{M/E,K}$ and $t_X=\sigma_{M/E,K[-1]}$, and use the
corresponding $Y$ notation. Since $\tau_{M/E,K[1]}=(s_X[-1])^{-1}$ and $\tau_{M/E,K}[1]=t_X^{-1}$,
the two calculations are $$R_M(S_M(u))=s_Y[-1](s_Y[-1])^{-1}u\,s_X[-1](s_X[-1])^{-1}=u,$$
$$S_M(R_M(u))=t_Y^{-1}t_Y\,u\,t_X^{-1}t_X=u.$$ Represent the finite-stage inverse-shift unit and
counit at $E$ for $(E,K)$. The displayed equations prove their naturality at the representative
stage $M$ of every arrow, and their two triangle composites at a common stage are the identity
chain-reindexing maps. This gives an inverse equivalence $[-1]$. Finally $j_E(K)=(E,K)$ and
$j_E(u)=[E,u]$ preserve identities, composition and sums by step 5. With normalized identity
associators, the shift compatibility equation at $E= M=N$ is $\sigma_{E/E,K}=\sigma_{E/E,K}^2$.
Invertibility therefore gives $\sigma_{E/E,K}=1$. The formula at $M=E$ yields
$j_E(u)[1]=[E,u[1]]$, and the objects agree as well, giving the specified inclusion-shift
comparison. -/
theorem commonStageCalculus (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    CommonStageCalculusSpec (pbcScalarSystem l Ω T hdim hl) := by
  exact commonStageCalculus_generic (pbcScalarSystem l Ω T hdim hl)

end AlgebraicGeometry.Scheme
