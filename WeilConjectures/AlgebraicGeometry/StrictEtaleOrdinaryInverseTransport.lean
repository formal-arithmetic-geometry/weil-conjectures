/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientTransportInterfaces
import all WeilConjectures.AlgebraicGeometry.CoefficientSystemUnboundedComparison

/-! # Ordinary inverse-image transport of strict coefficient systems

Source: Zheng, Construction 4.1 and Construction 5.15; Stacks Tag 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf
  SheafOfModules.coefficientQuotientSheaf SheafOfModules.coefficientQuotientMap
  SheafOfModules.siteCoefficientTensor SheafOfModules.siteCoefficientTensorAdj
  AlgebraicGeometry.StrictEtaleCoefficientChange.sheaf
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived


private theorem systemHom_ext {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O]
    {ell : O} {M N : strictEtaleCoefficientSystem T O ell} (f g : M ⟶ N)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

private def systemIso {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O]
    {ell : O} {M N : strictEtaleCoefficientSystem T O ell}
    (e : ∀ n, M.level n ≅ N.level n)
    (h : ∀ n, (e (n + 1)).hom ≫ N.transition n = M.transition n ≫
      (coefficientRestriction (J := T.smallEtaleTopology) O ell (Nat.le_succ n)).map
        (e n).hom) : M ≅ N := by
  let hom : M ⟶ N :=
    { app := fun n ↦ (e n).hom
      comm := h }
  let inv : N ⟶ M :=
    { app := fun n ↦ (e n).inv
      comm := fun n ↦ by
        apply (cancel_epi (e (n + 1)).hom).mp
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc, h]
        simp -implicitDefEqProofs only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id] }
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        change CoefficientSystem.Hom.compose hom inv = CoefficientSystem.identity M
        apply systemHom_ext _ _
        intro n
        exact (e n).hom_inv_id
      inv_hom_id := by
        change CoefficientSystem.Hom.compose inv hom = CoefficientSystem.identity N
        apply systemHom_ext _ _
        intro n
        exact (e n).inv_hom_id }

private theorem inverseUnderlying_transition
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T S : Scheme.{u}} {g : T ⟶ S}
    (A : StrictEtaleOrdinaryImage O ell g)
    (PT : StrictEtaleEvaluation T O ell) (PS : StrictEtaleEvaluation S O ell)
    {m n : ℕ} (h : n ≤ m) (M : strictEtaleCoefficientSystem S O ell) :
    SheafOfModules.transitionSets O ell PT h (A.inverse.obj M) ≫
        (strictEtaleInverseUnderlying A n).hom.app M =
      (strictEtaleInverseUnderlying A m).hom.app M ≫
        (Scheme.etaleSetPullback g).map (SheafOfModules.transitionSets O ell PS h M) := by
  have hi := SheafOfModules.ordinaryInverseTransition O ell _ _ _ A PS PT h M
  have hb := SheafOfModules.transition_bridge
    (F₀ := (A.lift n).modules) (F₁ := (A.lift m).modules)
    (RA := coefficientRestriction (J := S.smallEtaleTopology) O ell h)
    (RB := coefficientRestriction (J := T.smallEtaleTopology) O ell h)
    (Ua := coefficientUnderlying (J := S.smallEtaleTopology) O ell m)
    (Un := coefficientUnderlying (J := S.smallEtaleTopology) O ell n)
    (Ub := coefficientUnderlying (J := T.smallEtaleTopology) O ell m)
    (Uq := coefficientUnderlying (J := T.smallEtaleTopology) O ell n)
    (L := Scheme.etaleSetPullback g)
    (ra := coefficientRestrictionUnderlying (J := S.smallEtaleTopology) O ell h)
    (rb := coefficientRestrictionUnderlying (J := T.smallEtaleTopology) O ell h)
    (mu₀ := (A.lift n).moduleUnderlying) (mu₁ := (A.lift m).moduleUnderlying)
    (β := A.restrictInverse h) (A.restrictInverseUnderlying h)
    (M.level n) (M.level m) ((A.inverse.obj M).level n) ((A.inverse.obj M).level m)
    ((A.inverseEvaluation n).hom.app M) ((A.inverseEvaluation m).hom.app M)
    ((PT.strictTransition h).app (A.inverse.obj M)) ((PS.strictTransition h).app M)
  simpa -implicitDefEqProofs only [strictEtaleInverseUnderlying, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.comp_obj, SheafOfModules.transitionSets, coefficientEvaluation] using hb.mp hi

section
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (finite : ∀ n, siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
        (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))

private theorem transport_hom_ext
    {W : Scheme.{u}} {PA : StrictEtaleEvaluation W O ell}
    {PB : StrictEtaleEvaluation W O' mu}
    (U : StrictEtaleCoefficientTransport a W PA PB) (n : ℕ)
    (M : strictEtaleCoefficientSystem W O ell) {N : strictEtaleLevel W O' mu n}
    (f g : (U.ordinary.obj M).level n ⟶ N)
    (h : (U.setUnit n).app M ≫
        (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map f =
      (U.setUnit n).app M ≫
        (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map g) : f = g := by
  apply (cancel_epi ((U.val.evaluation n).inv.app M)).mp
  apply ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf W n)).homEquiv _ _).injective
  apply (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map_injective
  let r := isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf W n))
    (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))
  apply (cancel_mono (r.hom.app N)).mp
  simp -implicitDefEqProofs only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have hf := r.hom.naturality (((U.val.evaluation n).inv.app M) ≫ f)
  have hg := r.hom.naturality (((U.val.evaluation n).inv.app M) ≫ g)
  change (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
      ((SheafOfModules.restrictScalars _).map (((U.val.evaluation n).inv.app M) ≫ f)) ≫
      r.hom.app N = r.hom.app _ ≫
      (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
        (((U.val.evaluation n).inv.app M) ≫ f) at hf
  change (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
      ((SheafOfModules.restrictScalars _).map (((U.val.evaluation n).inv.app M) ≫ g)) ≫
      r.hom.app N = r.hom.app _ ≫
      (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
        (((U.val.evaluation n).inv.app M) ≫ g) at hg
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc] at hf hg
  rw [hf, hg]
  dsimp only [StrictEtaleCoefficientTransport.setUnit, whiskerRight_app] at h
  rw [U.property.2.1 n M] at h
  simpa -implicitDefEqProofs only [siteTensorUnitUnderlying, Functor.map_comp, Category.assoc,
    r, isoWhiskerRight_hom, whiskerRight_app, coefficientUnderlying, Functor.comp_map,
    coefficientEvaluation, Functor.comp_obj]
    using h

private theorem transport_transition
    {W : Scheme.{u}} {PA : StrictEtaleEvaluation W O ell}
    {PB : StrictEtaleEvaluation W O' mu}
    (U : StrictEtaleCoefficientTransport a W PA PB) (n : ℕ)
    (M : strictEtaleCoefficientSystem W O ell) :
    (U.setUnit (n + 1)).app M ≫
        SheafOfModules.transitionSets O' mu PB (Nat.le_succ n) (U.ordinary.obj M) =
      SheafOfModules.transitionSets O ell PA (index.monotone (Nat.le_succ n)) M ≫
        (U.setUnit n).app M := by
  have h := congrArg
    ((sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map)
    (U.property.2.2.1 n M)
  simpa -implicitDefEqProofs only [StrictEtaleCoefficientTransport.setUnit, whiskerRight_app,
    Functor.map_comp, Category.assoc, SheafOfModules.transitionSets,
    coefficientUnderlying, Functor.comp_map, coefficientRestrictionUnderlying,
    coefficientTransitionUnderlying, strictEtaleTransition, PB.transitionsNormalized.2.1,
    isoWhiskerRight_hom, whiskerRight_app]
    using h

private def levelCompare (n : ℕ) :
    (US.ordinary ⋙ B.inverse) ⋙
        coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n ≅
      (A.inverse ⋙ UT.ordinary) ⋙
        coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft US.ordinary (B.inverseEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (US.val.evaluation n) (B.lift n).modules ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (finite n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (A.inverseEvaluation (index n)).symm
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft A.inverse (UT.val.evaluation n).symm ≪≫
    (Functor.associator _ _ _).symm

private theorem insertion_naturality (W : Scheme.{u}) (n : ℕ)
    {M N : strictEtaleLevel W O ell (index n)} (f : M ⟶ N) :
    (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf W n) M) ≫
        (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf W n)).map f) =
      (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map f ≫
        (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf W n) N) := by
  let r := isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf W n))
    (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))
  have h := congrArg
    ((coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map)
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf W n)).unit.naturality f)
  have hr := r.hom.naturality ((siteCoefficientTensor (a.sheaf W n)).map f)
  change (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
      ((SheafOfModules.restrictScalars _).map
        ((siteCoefficientTensor (a.sheaf W n)).map f)) ≫ r.hom.app _ =
      r.hom.app _ ≫ (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
        ((siteCoefficientTensor (a.sheaf W n)).map f) at hr
  change ((coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
      ((siteCoefficientTensorAdj (a.sheaf W n)).unit.app M) ≫ r.hom.app _) ≫
      (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
        ((siteCoefficientTensor (a.sheaf W n)).map f) =
    (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map f ≫
      (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
        ((siteCoefficientTensorAdj (a.sheaf W n)).unit.app N) ≫ r.hom.app _
  rw [Category.assoc, ← hr]
  simpa -implicitDefEqProofs only [Functor.map_comp, Category.assoc, coefficientUnderlying,
    Functor.comp_map, Functor.id_map] using congrArg (fun k ↦ k ≫ r.hom.app
      ((siteCoefficientTensor (a.sheaf W n)).obj N)) h.symm

private theorem setUnit_def
    {W : Scheme.{u}} {PA : StrictEtaleEvaluation W O ell}
    {PB : StrictEtaleEvaluation W O' mu}
    (U : StrictEtaleCoefficientTransport a W PA PB) (n : ℕ)
    (M : strictEtaleCoefficientSystem W O ell) :
    (U.setUnit n).app M =
      (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf W n) (M.level (index n))) ≫
      (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
        ((U.val.evaluation n).inv.app M) := by
  exact (congrArg
    ((sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map)
    (U.property.2.1 n M)).trans (Functor.map_comp _ _ _)

set_option maxHeartbeats 2000000 in
-- Elaborating the composed coefficient functors exceeds the default heartbeat budget.
private theorem levelCompare_unit
    (finite_unit : ∀ n, ∀ M : strictEtaleLevel S O ell (index n),
      (Scheme.etaleSetPullback g).map
          ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
            (siteTensorUnitUnderlying (a.sheaf S n) M)) ≫
          (B.lift n).moduleUnderlying.inv.app
            ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
            ((finite n).hom.app M) =
        (A.lift (index n)).moduleUnderlying.inv.app M ≫
          (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
            (siteTensorUnitUnderlying (a.sheaf T n) ((A.lift (index n)).modules.obj M)))
    (n : ℕ) (M : strictEtaleCoefficientSystem S O ell) :
    (strictEtaleInverseUnderlying A (index n)).hom.app M ≫
        (Scheme.etaleSetPullback g).map ((US.setUnit n).app M) ≫
        (strictEtaleInverseUnderlying B n).inv.app (US.ordinary.obj M) ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((levelCompare UT US A B finite n).hom.app M) =
      (UT.setUnit n).app (A.inverse.obj M) := by
  simp -implicitDefEqProofs only [strictEtaleInverseUnderlying, levelCompare,
    Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerRight_inv,
    whiskerRight_app, isoWhiskerLeft_hom, isoWhiskerLeft_inv, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  have hn := (B.lift n).moduleUnderlying.inv.naturality ((US.val.evaluation n).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← reassoc_of% hn]
  erw [← (Scheme.etaleSetPullback g).map_comp_assoc]
  have hc : (US.setUnit n).app M ≫
      (coefficientUnderlying (J := S.smallEtaleTopology) O' mu n).map
        ((US.val.evaluation n).hom.app M) =
      (sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf S n) (M.level (index n))) := by
    let V := coefficientUnderlying (J := S.smallEtaleTopology) O' mu n
    let ev := (US.val.evaluation n).app M
    let i :=
      (sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf S n) (M.level (index n)))
    change (US.setUnit n).app M ≫ V.map ev.hom = i
    calc
      _ = (i ≫ V.map ev.inv) ≫ V.map ev.hom :=
        congrArg (fun k ↦ k ≫ V.map ev.hom) (setUnit_def US n M)
      _ = i ≫ (V.map ev.inv ≫ V.map ev.hom) := Category.assoc _ _ _
      _ = i ≫ 𝟙 _ := congrArg (fun k ↦ i ≫ k) (V.mapIso ev).inv_hom_id
      _ = i := Category.comp_id _
  erw [hc]
  erw [reassoc_of% (finite_unit n (M.level (index n))) ]
  erw [Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% (insertion_naturality (a := a) T n
    ((A.inverseEvaluation (index n)).inv.app M))]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp -implicitDefEqProofs only [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (setUnit_def UT n (A.inverse.obj M)).symm

set_option maxHeartbeats 2000000 in
-- The transition diagram contains several composed coefficient functors.
private theorem levelCompare_transition
    (hn : ∀ n M,
      (UT.setUnit n).app (A.inverse.obj M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
            ((levelCompare UT US A B finite n).inv.app M) ≫
          (strictEtaleInverseUnderlying B n).hom.app (US.ordinary.obj M) =
        (strictEtaleInverseUnderlying A (index n)).hom.app M ≫
          (Scheme.etaleSetPullback g).map ((US.setUnit n).app M))
    (M : strictEtaleCoefficientSystem S O ell) (n : ℕ) :
    (levelCompare UT US A B finite (n + 1)).inv.app M ≫
        (B.inverse.obj (US.ordinary.obj M)).transition n =
      (UT.ordinary.obj (A.inverse.obj M)).transition n ≫
        (coefficientRestriction (J := T.smallEtaleTopology) O' mu (Nat.le_succ n)).map
          ((levelCompare UT US A B finite n).inv.app M) := by
  apply transport_hom_ext UT (n + 1) (A.inverse.obj M)
  apply (cancel_mono
    ((coefficientRestrictionUnderlying (J := T.smallEtaleTopology) O' mu
        (Nat.le_succ n)).hom.app ((B.inverse.obj (US.ordinary.obj M)).level n) ≫
      (strictEtaleInverseUnderlying B n).hom.app (US.ordinary.obj M))).mp
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  have hr := (coefficientRestrictionUnderlying (J := T.smallEtaleTopology) O' mu
    (Nat.le_succ n)).hom.naturality ((levelCompare UT US A B finite n).inv.app M)
  change (coefficientUnderlying (J := T.smallEtaleTopology) O' mu (n + 1)).map
      ((coefficientRestriction (J := T.smallEtaleTopology) O' mu (Nat.le_succ n)).map
        ((levelCompare UT US A B finite n).inv.app M)) ≫
      (coefficientRestrictionUnderlying (J := T.smallEtaleTopology) O' mu
        (Nat.le_succ n)).hom.app ((B.inverse.obj (US.ordinary.obj M)).level n) =
    (coefficientRestrictionUnderlying (J := T.smallEtaleTopology) O' mu
      (Nat.le_succ n)).hom.app ((UT.ordinary.obj (A.inverse.obj M)).level n) ≫
      (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
        ((levelCompare UT US A B finite n).inv.app M) at hr
  erw [reassoc_of% hr]
  have hs (X : strictEtaleCoefficientSystem T O' mu) :
      SheafOfModules.transitionSets O' mu PTB (Nat.le_succ n) X =
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu (n + 1)).map
          (X.transition n) ≫
        (coefficientRestrictionUnderlying (J := T.smallEtaleTopology) O' mu
          (Nat.le_succ n)).hom.app (X.level n) := by
    simp -implicitDefEqProofs only [SheafOfModules.transitionSets,
      PTB.transitionsNormalized.2.1]
  erw [← reassoc_of% (hs (B.inverse.obj (US.ordinary.obj M))),
    ← reassoc_of% (hs (UT.ordinary.obj (A.inverse.obj M)))]
  erw [inverseUnderlying_transition B PTB PSB (Nat.le_succ n)
      (US.ordinary.obj M),
    reassoc_of% (hn (n + 1) M),
    ← (Scheme.etaleSetPullback g).map_comp,
    transport_transition US n M,
    (Scheme.etaleSetPullback g).map_comp]
  erw [← reassoc_of% (inverseUnderlying_transition A PTA PSA
    (index.monotone (Nat.le_succ n)) M)]
  erw [← hn n M, ← reassoc_of% (transport_transition UT n (A.inverse.obj M))]
  rfl


end

/-- Ordinary coefficient extension commutes with geometric inverse image on strict
systems, with the comparison fixed by the tensor insertions on underlying set sheaves.
Source: Zheng, Construction 4.1 and Construction 5.15; Stacks Project, Tag 03EL.
(blueprint: lem-pur-strict-etale-ordinary-inverse-transport).

Proof: conjugate each supplied normalized finite comparison by the ordinary
transport-evaluation and inverse-evaluation isomorphisms. Its finite_unit equation
fixes the comparison on scalar insertions in underlying set sheaves.
For each successor transition, precompose the two candidate component words with
the scalar tensor insertion. The transport transition law and the geometric
inverse-transition law reduce them to inverse image of the same original transition,
followed by the insertion at n. The scalar adjunction makes this test injective,
so the component isomorphisms commute with transitions. Naturality follows from
naturality of the three component comparisons. Their componentwise inverses give
the inverse strict-system map. The unit equations of the level comparisons,
conjugated by the evaluation isomorphisms, give the displayed normalization. -/
theorem nonempty_strictEtaleOrdinaryInverseTransport
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (finite : ∀ n, siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
        (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (finite_unit : ∀ n,
      ∀ M : strictEtaleLevel S O ell (index n),
        (Scheme.etaleSetPullback g).map
            ((sheafCompose S.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
              (siteTensorUnitUnderlying (a.sheaf S n) M)) ≫
            (B.lift n).moduleUnderlying.inv.app
              ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) ≫
            (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map ((finite n).hom.app M) =
          (A.lift (index n)).moduleUnderlying.inv.app M ≫
            (sheafCompose T.smallEtaleTopology
              (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
              (siteTensorUnitUnderlying (a.sheaf T n) ((A.lift (index n)).modules.obj M))) :
    ∃ ordinary : US.ordinary ⋙ B.inverse ≅ A.inverse ⋙ UT.ordinary,
      ∀ n M,
        (UT.setUnit n).app (A.inverse.obj M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
            ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
              (ordinary.inv.app M)) ≫
          (strictEtaleInverseUnderlying B n).hom.app (US.ordinary.obj M) =
        (strictEtaleInverseUnderlying A (index n)).hom.app M ≫
          (Scheme.etaleSetPullback g).map ((US.setUnit n).app M) := by
  let e := levelCompare UT US A B finite
  have hn (n : ℕ) (M : strictEtaleCoefficientSystem S O ell) :
      (UT.setUnit n).app (A.inverse.obj M) ≫
          (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
            ((e n).inv.app M) ≫
          (strictEtaleInverseUnderlying B n).hom.app (US.ordinary.obj M) =
        (strictEtaleInverseUnderlying A (index n)).hom.app M ≫
          (Scheme.etaleSetPullback g).map ((US.setUnit n).app M) := by
    apply (cancel_mono
      ((strictEtaleInverseUnderlying B n).inv.app (US.ordinary.obj M) ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
          ((e n).hom.app M))).mp
    simp -implicitDefEqProofs only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    exact (levelCompare_unit UT US A B finite finite_unit n M).symm
  let ordinary : A.inverse ⋙ UT.ordinary ≅ US.ordinary ⋙ B.inverse :=
    NatIso.ofComponents
      (fun M ↦ systemIso (fun n ↦ (e n).symm.app M)
        (levelCompare_transition UT US A B finite hn M))
      (fun {M N} f ↦ by
        apply systemHom_ext
        intro n
        exact (e n).inv.naturality f)
  exact ⟨ordinary.symm, hn⟩

end AlgebraicGeometry
