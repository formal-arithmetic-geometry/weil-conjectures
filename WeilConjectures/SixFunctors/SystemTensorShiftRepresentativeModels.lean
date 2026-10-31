/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOperationShiftData

/-! # Simultaneous representative formula for the prescribed system tensor shifts

Source: Stacks 011G, 014E, 06YU, 0FPQ and 0FNH; the maps-used sentence of
blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.Functor

namespace WeilConjectures.IntegralSystemRealization

private theorem composeShiftSquares
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    (L : C ⥤ D) [L.CommShift ℤ] (a b : ℤ) {X₀ X₁ X₂ : C}
    (β : X₁ ≅ X₀⟦a⟧) (γ : X₂ ≅ X₁⟦b⟧) {Y₀ Y₁ Y₂ : D}
    (c₀ : L.obj X₀ ≅ Y₀) (c₁ : L.obj X₁ ≅ Y₁) (c₂ : L.obj X₂ ≅ Y₂)
    (f : Y₂ ⟶ Y₁⟦b⟧) (g : Y₁ ⟶ Y₀⟦a⟧)
    (hf : f = c₂.inv ≫ L.map γ.hom ≫ (L.commShiftIso b).hom.app X₁ ≫ c₁.hom⟦b⟧')
    (hg : g = c₁.inv ≫ L.map β.hom ≫ (L.commShiftIso a).hom.app X₀ ≫ c₀.hom⟦a⟧') :
    f ≫ g⟦b⟧' ≫ (shiftFunctorAdd D a b).inv.app Y₀ =
      c₂.inv ≫ L.map (γ.hom ≫ β.hom⟦b⟧' ≫
        (shiftFunctorAdd C a b).inv.app X₀) ≫
        (L.commShiftIso (a + b)).hom.app X₀ ≫ c₀.hom⟦a + b⟧' := by
  rw [hf, hg, L.commShiftIso_add]
  simp only [Functor.CommShift.isoAdd_hom_app, L.map_comp, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← L.commShiftIso_hom_naturality_assoc]
  simp only [← L.map_comp_assoc, Iso.inv_hom_id_app]
  have hn : (shiftFunctor D b).map ((shiftFunctor D a).map c₀.hom) ≫
      (shiftFunctorAdd D a b).inv.app Y₀ =
      (shiftFunctorAdd D a b).inv.app (L.obj X₀) ≫ c₀.hom⟦a + b⟧' :=
    (shiftFunctorAdd D a b).inv.naturality c₀.hom
  rw [hn]
  erw [Category.comp_id ((shiftFunctor C b).map β.hom)]

private theorem composeShiftCasts {C : Type*} [Category* C] [Preadditive C]
    (K : CochainComplex C ℤ) (a b n m k : ℤ)
    (hm : m = n + b) (hk : k = m + a) (h : k = n + (a + b)) :
    (K.shiftFunctorObjXIso a m k hk).inv ≫
        ((K⟦a⟧).shiftFunctorObjXIso b n m hm).inv ≫
        ((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n =
      (K.shiftFunctorObjXIso (a + b) n k h).inv := by
  simp only [CochainComplex.shiftFunctorObjXIso,
    CochainComplex.shiftFunctorAdd_inv_app_f, HomologicalComplex.XIsoOfEq, eqToIso.inv, eqToIso.hom]
  erw [eqToHom_trans, eqToHom_trans]
  rfl

attribute [local irreducible] pullbackTensorCalculus tensorShifts
  DerivedCategory.Q DerivedCategory.Qh coefficientTotalTensor coefficientTensorGenerator

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option maxHeartbeats 1600000 in
-- The fixed whole-system comparison has a large elaborated type.
/-- Combine the two normalized tensor-slot comparisons on every K-flat pair.
Source: Stacks 011G and 06YU; the parent proof, Step 4.
(blueprint: lem-pur-system-tensor-shift-representative-models).

Proof: use the second-slot normalization on (P[a],Q), then apply [b] to the
first-slot normalization on (P,Q), and finally identify [a][b] with [a+b].
The two normalizations provide K-flatness of P[a] and Q[b]. Compose their
actual chain isomorphisms in that order. On the shifted (i,j)-summand the
first map has coefficient (-1)^(bi), and the next map has coefficient 1.
Reindexing gives precisely the displayed generator formula, including the
signed differential and every coefficient transition. Substitute the two
normalizing derived squares, use naturality of Q's shift isomorphisms and
of the tensor comparisons, and cancel the intermediate representative
isomorphism. The resulting square is the displayed equality. When a
representative lacks flat terms, replace it by a flat-term K-flat resolution;
K-flatness in both variables makes the comparison a quasi-isomorphism, so
the equality descends back by naturality and cancellation. The argument
includes zero and negative shifts because the chain formulas hold for all
integers. -/
theorem systemTensorShiftRepresentativeModels (W : Scheme.{u}) :
    let t := fun a b : ℤ ↦
      isoWhiskerLeft (tensorShiftFirst (System l E W) a) ((tensorShifts l E).systemRight W b) ≪≫
        isoWhiskerRight ((tensorShifts l E).systemLeft W a) (shiftFunctor (System l E W) b) ≪≫
        isoWhiskerLeft (calculus l E W).systemClosed.tensor
          (shiftFunctorAdd (System l E W) a b).symm
    ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q) (a b : ℤ),
        ∃ (hPa : systemKFlat l E W (P⟦a⟧)) (hQb : systemKFlat l E W (Q⟦b⟧))
          (α : (systemTotalTensor l E W).obj (P⟦a⟧, Q⟦b⟧) ≅
            ((systemTotalTensor l E W).obj (P, Q))⟦a + b⟧),
          (∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
        (x : (P.X (i + a)).val.obj U) (y : (Q.X (j + b)).val.obj U),
        ((α.hom.f (i + j)).val.app U)
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)
            (P⟦a⟧) (Q⟦b⟧) i j (i + j) rfl U x y) =
        ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
          (a + b) (i + j) ((i + a) + (j + b)) (by omega)).inv.val.app U)
          ((b * i).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W)
            P Q (i + a) (j + b) ((i + a) + (j + b)) rfl U x y)) ∧
          (calculus l E W).systemClosed.tensor.map
              (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).hom.app P)
                ((DerivedCategory.Q.commShiftIso b).hom.app Q)) ≫
              (t a b).hom.app
                (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
            ((calculus l E W).systemTensorModel.iso
              (coefficientSequenceTopology (ProEt.topology W))
              (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
              (P⟦a⟧) (Q⟦b⟧) hPa hQb).inv ≫ DerivedCategory.Q.map α.hom ≫
            (DerivedCategory.Q.commShiftIso (a + b)).hom.app
              ((systemTotalTensor l E W).obj (P, Q)) ≫
            (shiftFunctor (System l E W) (a + b)).map
              (((calculus l E W).systemTensorModel.iso
                (coefficientSequenceTopology (ProEt.topology W))
                (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
                P Q hP hQ).hom) := by
  dsimp only
  intro P Q hP hQ a b
  obtain ⟨hPa, β, hβ, eβ⟩ :=
    (tensorShifts l E).systemLeft_normalized W a P Q hP hQ
  obtain ⟨hQb, γ, hγ, eγ⟩ :=
    (tensorShifts l E).systemRight_normalized W b (P⟦a⟧) Q hPa hQ
  let α := γ ≪≫ (shiftFunctor _ b).mapIso β ≪≫
    ((shiftFunctorAdd _ a b).app ((systemTotalTensor l E W).obj (P, Q))).symm
  refine ⟨hPa, hQb, α, ?_, ?_⟩
  · intro i j U x y
    have hg := hγ i j U x y
    have hb := hβ i (j + b) U x y
    change (((γ.hom.f (i + j) ≫ β.hom.f ((i + j) + b) ≫
      ((shiftFunctorAdd _ a b).inv.app
        ((systemTotalTensor l E W).obj (P, Q))).f (i + j)).val.app U) _) = _
    rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hg]
    erw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val]
    erw [← HomologicalComplex.XIsoOfEq_inv_naturality_assoc]
    rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    simp only [Units.smul_def, _root_.map_zsmul]
    erw [hb]
    apply congrArg (fun z ↦ (↑(b * i).negOnePow : ℤ) • z)
    let K := (systemTotalTensor l E W).obj (P, Q)
    have hc := composeShiftCasts K a b (i + j) (i + (j + b)) ((i + a) + (j + b))
      (by omega) (by omega) (by omega)
    exact congrArg (fun f : K.X ((i + a) + (j + b)) ⟶ K.X ((i + j) + (a + b)) ↦
      f.val.app U
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        P Q (i + a) (j + b) ((i + a) + (j + b)) rfl U x y)) hc
  · let F := (calculus l E W).systemClosed.tensor
    let sP := (DerivedCategory.Q.commShiftIso a).hom.app P
    let sQ := (DerivedCategory.Q.commShiftIso b).hom.app Q
    let σR := (tensorShifts l E).systemRight W b
    let σL := (tensorShifts l E).systemLeft W a
    let c₀ := (calculus l E W).systemTensorModel.iso
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed P Q hP hQ
    let c₁ := (calculus l E W).systemTensorModel.iso
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
      (P⟦a⟧) Q hPa hQ
    let c₂ := (calculus l E W).systemTensorModel.iso
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
      (P⟦a⟧) (Q⟦b⟧) hPa hQb
    let f := F.map (Prod.mkHom (𝟙 _) sQ) ≫
      σR.hom.app (DerivedCategory.Q.obj (P⟦a⟧), DerivedCategory.Q.obj Q)
    let g := F.map (Prod.mkHom sP (𝟙 _)) ≫
      σL.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
    have hs := composeShiftSquares DerivedCategory.Q a b β γ c₀ c₁ c₂ f g eγ eβ
    refine Eq.trans ?_ hs
    change F.map (Prod.mkHom sP sQ) ≫
      σR.hom.app ((DerivedCategory.Q.obj P)⟦a⟧, DerivedCategory.Q.obj Q) ≫
      (shiftFunctor _ b).map (σL.hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (shiftFunctorAdd _ a b).inv.app _ = _
    have he : Prod.mkHom sP sQ =
        Prod.mkHom (𝟙 _) sQ ≫ (completedTensorShiftSecond (System l E W) b).map
          (Prod.mkHom sP (𝟙 (DerivedCategory.Q.obj Q))) := by
      ext <;> simp [completedTensorShiftSecond]
    erw [he, F.map_comp, Category.assoc, σR.hom.naturality_assoc]
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map]
    dsimp only [f, g]
    erw [(shiftFunctor (System l E W) b).map_comp, Category.assoc, Category.assoc]
    rfl


end WeilConjectures.IntegralSystemRealization
