/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RelativeInvariantForgetting
public import Sheaf.CategoryTheory.RelativeBarData



/-! # RelativeTrivialCyclicMap

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-trivial-cyclic-map)

## Main definitions and statements

The primary declaration is `trivialCyclicMap`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {A' : CondensedBar.Ring.{u}}
variable {J}
variable {A G}

/-- The trivial coefficient module, restricted from H to the cyclic group with residual 1.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialInput (v : Z.{u} →ₜ* H) : Equivariant A (PUnit.{u + 1} × Z.{u}) :=
  (inflate (R := A.toMon) (productMap (G := PUnit.{u + 1}) v)).obj
    (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H))

/-- The relative two-column total of the restricted trivial regular module.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialTotal (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :=
  K.functor.obj (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj

private theorem trivialGenerator (v : Z.{u} →ₜ* H) (n : ℤ) :
    generatorEnd ((single A (PUnit.{u + 1} × Z) (trivialInput v)).obj.X n) = 𝟙 _ := by
  by_cases hn : n = 0
  · subst n
    symm
    apply (Classical.choose_spec (generatorEndExist _)).2
    intro S x
    rfl
  · exact ((retainResidual A PUnit.{u + 1} Z).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (trivialInput v) n hn)).eq_of_src _ _

private theorem trivialTotalIsZero (K : TotalModel A PUnit.{u + 1})
    (v : Z.{u} →ₜ* H) (n : ℤ) (hn : n ≠ 0) (hn' : n ≠ 1) :
    IsZero ((((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
      (.up ℤ)).obj (trivialTotal K v)).X n) := by
  apply (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map_isZero
  apply IsZero.of_iso _ (K.coordinates _ n)
  apply (biprod_isZero_iff _ _).2
  constructor
  · exact (retainResidual A PUnit.{u + 1} Z).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (trivialInput v) n hn)
  · exact (retainResidual A PUnit.{u + 1} Z).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (trivialInput v) (n - 1) (by omega))

private theorem trivialTotalDifferential (K : TotalModel A PUnit.{u + 1})
    (v : Z.{u} →ₜ* H) (n : ℤ) :
    (trivialTotal K v).d n (n + 1) = 0 := by
  let N := (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj
  have h := K.differential N n
  have hg : generatorEnd (N.X n) = 𝟙 _ := trivialGenerator v n
  have hd (i j : ℤ) : N.d i j = 0 := rfl
  simp only [hg, sub_self, hd, Functor.map_zero, comp_zero, zero_comp] at h
  replace h : (K.coordinates N n).inv ≫ (K.functor.obj N).d n (n + 1) ≫
      (K.coordinates N (n + 1)).hom = 0 := by
    rw [h]
    apply biprod.hom_ext <;> simp
  change (K.functor.obj N).d n (n + 1) = 0
  apply (cancel_epi (K.coordinates N n).inv).1
  apply (cancel_mono (K.coordinates N (n + 1)).hom).1
  simpa only [comp_zero, zero_comp, Category.assoc] using h

open scoped ZeroObject in
private theorem trivialCyclicExtendedIsZero (n : ℤ) (hn : n ≠ 0) (hn' : n ≠ 1) :
    IsZero ((extend (trivialCyclic A)).X n) := by
  by_cases h : 0 ≤ n
  · apply IsZero.of_iso _ ((trivialCyclic A).extendXIso
      ComplexShape.embeddingUpNat (Int.toNat_of_nonneg h))
    have hX : (trivialCyclic A).X n.toNat = (0 : Modules A) := if_neg (by omega)
    rw [hX]
    exact isZero_zero _
  · apply (trivialCyclic A).isZero_extend_X ComplexShape.embeddingUpNat
    intro i
    change (i : ℤ) ≠ n
    omega

private theorem trivialCyclicExtendedDifferential (n : ℤ) :
    (extend (trivialCyclic A)).d n (n + 1) = 0 := by
  by_cases h : n = 0
  · subst n
    change ((trivialCyclic A).extend ComplexShape.embeddingUpNat).d 0 1 = 0
    exact (HomologicalComplex.extend_d_eq (trivialCyclic A) ComplexShape.embeddingUpNat
      (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl).trans (by
        simp only [show (trivialCyclic A).d 0 1 = 0 from rfl, comp_zero, zero_comp])
  · by_cases h' : n = 1
    · subst n
      exact (trivialCyclicExtendedIsZero (A := A) 2 (by omega) (by omega)).eq_of_tgt _ _
    · exact (trivialCyclicExtendedIsZero (A := A) n h h').eq_of_src _ _

private def trivialTotalDegreeZero (K : TotalModel A PUnit.{u + 1})
    (v : Z.{u} →ₜ* H) :
    (((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
      (.up ℤ)).obj (trivialTotal K v)).X 0 ≅ (extend (trivialCyclic A)).X 0 :=
  (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapIso
    (K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 0 ≪≫
      (isoBiprodZero ((retainResidual A PUnit.{u + 1} Z).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (trivialInput v) (-1)
          (by omega)))).symm ≪≫
      (retainResidual A PUnit.{u + 1} Z).mapIso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v))) ≪≫
    ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).symm

private def trivialTotalDegreeOne (K : TotalModel A PUnit.{u + 1})
    (v : Z.{u} →ₜ* H) :
    (((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
      (.up ℤ)).obj (trivialTotal K v)).X 1 ≅ (extend (trivialCyclic A)).X 1 :=
  (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapIso
    (K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 1 ≪≫
      (isoZeroBiprod ((retainResidual A PUnit.{u + 1} Z).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (trivialInput v) 1
          (by omega)))).symm ≪≫
      (retainResidual A PUnit.{u + 1} Z).mapIso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v))) ≪≫
    ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat (i := 1) rfl).symm

/-- With trivial coefficients the total has its coordinate-normalized identification with
[R -> 0 R]. The equations in degrees zero and one determine the isomorphism, since all
other terms are zero by the total coordinates.
Source: paragraph (3), step 18
(blueprint: def-sfb-relative-trivial-cyclic-map).
Proof: the restricted generator acts as identity, so T-1 is zero. Use the first biproduct
coordinate in degree zero and the second in degree one; every other summand is zero. -/
theorem trivialTotalIsoExist (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :
    ∃! k : ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
        (.up ℤ)).obj (trivialTotal K v) ≅ extend (trivialCyclic A),
      (k.hom.f 0 ≫ ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
          (i := 0) (i' := 0) rfl).hom =
        (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
          ((K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 0).hom ≫
            biprod.fst ≫
            (retainResidual A PUnit.{u + 1} Z).map
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v)).hom)) ∧
      (k.hom.f 1 ≫ ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
          (i := 1) (i' := 1) rfl).hom =
        (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
          ((K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 1).hom ≫
            biprod.snd ≫
            (retainResidual A PUnit.{u + 1} Z).map
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v)).hom)) := by
  let T := ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
    (.up ℤ)).obj (trivialTotal K v)
  let E := extend (trivialCyclic A)
  let e (n : ℤ) : T.X n ≅ E.X n := by
    by_cases hn : n = 0
    · subst n
      exact trivialTotalDegreeZero K v
    · by_cases hn' : n = 1
      · subst n
        exact trivialTotalDegreeOne K v
      · exact (trivialTotalIsZero K v n hn hn').iso
          (trivialCyclicExtendedIsZero n hn hn')
  let k : T ≅ E := HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    change (e i).hom ≫ E.d i (i + 1) =
      (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
        ((trivialTotal K v).d i (i + 1)) ≫ (e (i + 1)).hom
    rw [trivialCyclicExtendedDifferential, trivialTotalDifferential]
    simp only [Functor.map_zero, comp_zero]
    exact (zero_comp : (0 : T.X i ⟶ T.X (i + 1)) ≫ (e (i + 1)).hom = 0).symm)
  have hk0 : k.hom.f 0 ≫ ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl).hom =
      (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
        ((K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 0).hom ≫
          biprod.fst ≫ (retainResidual A PUnit.{u + 1} Z).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v)).hom) := by
    change (trivialTotalDegreeZero K v).hom ≫ _ = _
    exact (((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl).eq_comp_inv).mp rfl
  have hk1 : k.hom.f 1 ≫ ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
      (i := 1) (i' := 1) rfl).hom =
      (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
        ((K.coordinates (single A (PUnit.{u + 1} × Z) (trivialInput v)).obj 1).hom ≫
          biprod.snd ≫ (retainResidual A PUnit.{u + 1} Z).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (trivialInput v)).hom) := by
    change (trivialTotalDegreeOne K v).hom ≫ _ = _
    exact (((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
      (i := 1) (i' := 1) rfl).eq_comp_inv).mp rfl
  refine ⟨k, ⟨hk0, hk1⟩, ?_⟩
  intro l hl
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    apply (cancel_mono ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl).hom).1
    exact hl.1.trans hk0.symm
  · by_cases hn' : n = 1
    · subst n
      apply (cancel_mono ((trivialCyclic A).extendXIso ComplexShape.embeddingUpNat
        (i := 1) (i' := 1) rfl).hom).1
      exact hl.2.trans hk1.symm
    · exact (trivialCyclicExtendedIsZero n hn hn').eq_of_tgt _ _

/-- The unique coordinate identification of the trivial cyclic total.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialTotalIso (K : TotalModel A PUnit.{u + 1}) (v : Z.{u} →ₜ* H) :
    ((CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex
      (.up ℤ)).obj (trivialTotal K v) ≅ extend (trivialCyclic A) :=
  Classical.choose (trivialTotalIsoExist K v)

/-- The trivial residual group disappears by the original identity on its regular module.
Source: paragraph (3), step 18
(blueprint: def-sfb-relative-trivial-cyclic-map).
Proof: restricting a trivial action is trivial. The underlying identity is equivariant,
natural and invertible; faithfulness fixes the displayed isomorphism uniquely. -/
theorem forgetTrivialExist :
    ∃! e : (forgetResidual A PUnit.{u + 1} H).obj
        (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H)) ≅
      CondensedDerivedRestriction.regularTrivial A H,
      e.hom.val = 𝟙 (Mod.regular A.X) := by
  refine ⟨Iso.refl _, rfl, ?_⟩
  intro e he
  apply Iso.ext
  exact Subtype.ext he

/-- The identity-normalized trivial-group comparison.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def forgetTrivial := Classical.choose (forgetTrivialExist (A := A) (H := H))

/-- The canonical identification of relative invariants of trivial coefficients with the
scalar derived invariants, with exact restriction and single-complex identifications.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialSourceIso :
    (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapDerivedCategory.obj
      ((derived A PUnit.{u + 1} H).obj ((DerivedCategory.singleFunctor _ 0).obj
        (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H)))) ≅
      (CondensedDerivedRestriction.derived A H).obj ((DerivedCategory.singleFunctor _ 0).obj
        (CondensedDerivedRestriction.regularTrivial A H)) :=
  (forgetDerived A PUnit.{u + 1} (J := H)).app _ ≪≫
    (CondensedDerivedRestriction.derived A H).mapIso
      (((forgetResidual A PUnit.{u + 1} H).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (forgetTrivial (A := A) (H := H)))

/-- The scalar map c obtained by forgetting the trivial residual action in the relative map.
Source: paragraph (3) (blueprint: def-sfb-relative-trivial-cyclic-map). -/
def trivialCyclicMap {K : TotalModel A PUnit.{u + 1}}
    (C : HasComparison A PUnit.{u + 1} K) (v : Z.{u} →ₜ* H) :
    (CondensedDerivedRestriction.derived A H).obj ((DerivedCategory.singleFunctor _ 0).obj
        (CondensedDerivedRestriction.regularTrivial A H)) ⟶
      DerivedCategory.Q.obj (extend (trivialCyclic A)) :=
  (trivialSourceIso (A := A) (H := H)).inv ≫
    (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapDerivedCategory.map
      (cyclicMap A PUnit.{u + 1} C v
        (CondensedDerivedRestriction.regularTrivial A (PUnit.{u + 1} × H))) ≫
    (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).mapDerivedCategoryFactors.hom.app
      (trivialTotal K v) ≫ DerivedCategory.Q.map (trivialTotalIso K v).hom


end CategoryTheory.RelativeCyclic
