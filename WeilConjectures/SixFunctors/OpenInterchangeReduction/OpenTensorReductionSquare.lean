/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import WeilConjectures.SixFunctors.GeneratorReduction.CanonicalOpenReductionIsIso
import WeilConjectures.SixFunctors.GeneratorReduction.CanonicalReductionPullTensor

/-! # The coefficient square for the open tensor projection formula
Source: the open-adjunction and clopen expansion of the coherence proof.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

private theorem projection_inverse_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (μA : TA ⋙ R ⟶ R.prod R ⋙ TC) (μB : TB ⋙ T ⟶ T.prod T ⋙ TD)
    (χ : Q ⋙ R ⟶ T ⋙ G) (ρ : P ⋙ T ⟶ R ⋙ F)
    (θ : TB ⋙ Q ≅ Q.prod Q ⋙ TA) (ψ : TD ⋙ G ≅ G.prod G ⋙ TC)
    (hu : ∀ M, R.map (a.unit.app M) ≫ χ.app (P.obj M) ≫
      G.map (ρ.app M) = b.unit.app (R.obj M))
    (hc : ∀ H, ρ.app (Q.obj H) ≫ F.map (χ.app H) ≫
      b.counit.app (T.obj H) = T.map (a.counit.app H))
    (ht : ∀ H N, R.map (θ.hom.app (H, N)) ≫ μA.app (Q.obj H, Q.obj N) ≫
        TC.map (Prod.mkHom (χ.app H) (χ.app N)) =
      χ.app (TB.obj (H, N)) ≫ G.map (μB.app (H, N)) ≫
        ψ.hom.app (T.obj H, T.obj N))
    (M : A) (N : B)
    (γ : P.obj (TA.obj (M, Q.obj N)) ⟶ TB.obj (P.obj M, N))
    (δ : F.obj (TC.obj (R.obj M, G.obj (T.obj N))) ⟶ TD.obj (F.obj (R.obj M), T.obj N))
    (hγ : a.homEquiv _ _ γ =
      TA.map (Prod.mkHom (a.unit.app M) (𝟙 _)) ≫ θ.inv.app (P.obj M, N))
    (hδ : b.homEquiv _ _ δ =
      TC.map (Prod.mkHom (b.unit.app (R.obj M)) (𝟙 _)) ≫
        ψ.inv.app (F.obj (R.obj M), T.obj N)) :
    ρ.app (TA.obj (M, Q.obj N)) ≫
        F.map (μA.app (M, Q.obj N) ≫ TC.map (Prod.mkHom (𝟙 _) (χ.app N))) ≫ δ =
      T.map γ ≫ μB.app (P.obj M, N) ≫ TD.map (Prod.mkHom (ρ.app M) (𝟙 _)) := by
  let H := TB.obj (P.obj M, N)
  let q := μB.app (P.obj M, N) ≫ TD.map (Prod.mkHom (ρ.app M) (𝟙 _))
  let τ := TA.map (Prod.mkHom (a.unit.app M) (𝟙 (Q.obj N))) ≫
    θ.inv.app (P.obj M, N)
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at *
  have hi : μA.app (Q.obj (P.obj M), Q.obj N) ≫
        TC.map (Prod.mkHom (χ.app (P.obj M)) (χ.app N)) ≫
        ψ.inv.app (T.obj (P.obj M), T.obj N) =
      R.map (θ.inv.app (P.obj M, N)) ≫ χ.app H ≫ G.map (μB.app (P.obj M, N)) := by
    apply (cancel_epi (R.map (θ.hom.app (P.obj M, N)))).1
    simp only [← R.map_comp_assoc, Iso.hom_inv_id_app, R.map_id, Category.id_comp]
    rw [reassoc_of% ht]
    simp only [Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hn := ψ.inv.naturality (Prod.mkHom (ρ.app M) (𝟙 (T.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [G.map_id] at hn
  have hμ := μA.naturality (Prod.mkHom (a.unit.app M) (𝟙 (Q.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hμ
  simp only [R.map_id] at hμ
  have htau : (μA.app (M, Q.obj N) ≫ TC.map (Prod.mkHom (𝟙 _) (χ.app N))) ≫
        b.homEquiv _ _ δ = R.map τ ≫ χ.app H ≫ G.map q := by
    erw [hδ, ← hu M]
    simp only [Category.assoc, ← TC.map_comp_assoc, prod_comp,
      Category.id_comp]
    erw [Category.comp_id]
    rw [show Prod.mkHom (R.map (a.unit.app M) ≫ χ.app (P.obj M) ≫
        G.map (ρ.app M)) (χ.app N) =
      Prod.mkHom (R.map (a.unit.app M)) (𝟙 (R.obj (Q.obj N))) ≫
        Prod.mkHom (χ.app (P.obj M)) (χ.app N) ≫
          Prod.mkHom (G.map (ρ.app M)) (𝟙 (G.obj (T.obj N))) by
      ext <;> simp]
    erw [TC.map_comp, TC.map_comp, ← Category.assoc, ← Category.assoc, ← hμ]
    simp only [Category.assoc]
    erw [hn, reassoc_of% hi]
    simp only [τ, q, R.map_comp, G.map_comp, Category.assoc]
  have hγ' : γ = P.map τ ≫ a.counit.app H := by
    have hγ0 : a.homEquiv _ _ γ = τ := hγ
    rw [← hγ0]
    exact ((a.homEquiv _ _).symm_apply_apply γ).symm
  have hδ' : δ = F.map (b.homEquiv _ _ δ) ≫ b.counit.app _ :=
    ((b.homEquiv _ _).symm_apply_apply δ).symm
  erw [hδ', ← F.map_comp_assoc, htau]
  simp only [F.map_comp, Category.assoc]
  erw [← Category.assoc, ← ρ.naturality τ]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  erw [b.counit.naturality q]
  dsimp only [Functor.comp_map, Functor.id_map]
  erw [reassoc_of% hc H, ← T.map_comp_assoc, ← hγ']


private theorem forward_of_inverse
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y : A} {M N : B} (f : X ≅ Y) (g : M ≅ N)
    (q : R.obj X ⟶ M) (r : R.obj Y ⟶ N)
    (h : r ≫ g.inv = R.map f.inv ≫ q) :
    q ≫ g.hom = R.map f.hom ≫ r := by
  apply (cancel_mono g.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]


private theorem ordinary_open_tensor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {S : Type s} {W : S → Scheme.{u}}
    {I : Type i} {location : I → S} {a b : S}
    (j : W a ⟶ W b) (hj : IsOpenImmersion j) (hq : QuasiCompact j)
    (B : Word W location a) (C : Word W location b)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.tensor (Word.open j hj hq B) C).ordinaryR l E o K ≫
        (GeneratorKind.openTensor j hj hq B C).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W b)).reduction.map
          ((GeneratorKind.openTensor j hj hq B C).ringedMap l E W location o K) ≫
        (Word.open j hj hq (Word.tensor B
          (Word.pull j (by let := hj; infer_instance)
            (by let := hj; infer_instance) hq C))).ordinaryR l E o K := by
  let := hj
  let R := (IntegralSystemRealization.calculus l E (W a)).reduction
  let T := (IntegralSystemRealization.calculus l E (W b)).reduction
  let P := IntegralSystemRealization.ringedOpen l E j
  let Q := IntegralSystemRealization.ringedPull l E j
  let F := IntegralSystemRealization.Operations.shriek l E o.system j
  let G := IntegralSystemRealization.pull l E j
  let TA := (o.ringed.tensor (W a)).ordinary.tensor
  let TB := (o.ringed.tensor (W b)).ordinary.tensor
  let TC := (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor
  let TD := (IntegralSystemRealization.calculus l E (W b)).systemClosed.tensor
  let χ := (o.realization.reductionPull j).hom
  let α := o.realization.openReduction l E j
  have hα (M) : IsIso (α.app M) := canonicalOpenReduction_isIso l E o j M
  let : IsIso α := NatIso.isIso_of_isIso_app α
  let ρ := inv α
  let M := B.ringedValue l E W location o K
  let N := C.ringedValue l E W location o K
  let x := B.ordinaryR l E o K
  let y := C.ordinaryR l E o K
  let V : Word W location b := Word.open j hj hq (Word.tensor B
    (Word.pull j (by let := hj; infer_instance) (by let := hj; infer_instance) hq C))
  have hu (M) : R.map ((IntegralSystemRealization.ringedOpenAdj l E j).unit.app M) ≫
      χ.app (P.obj M) ≫ G.map (ρ.app M) = (o.system.extension j).adj.unit.app (R.obj M) := by
    have : IsIso (((mateEquiv (IntegralSystemRealization.ringedOpenAdj l E j)
      (o.system.extension j).adj).symm χ).natTrans.app M) := hα M
    have h := inverse_mate_unit_square (IntegralSystemRealization.ringedOpenAdj l E j)
      (o.system.extension j).adj χ (𝟙 (R.obj M))
    change 𝟙 (R.obj M) ≫ (o.system.extension j).adj.unit.app (R.obj M) =
      R.map ((IntegralSystemRealization.ringedOpenAdj l E j).unit.app M) ≫
        χ.app (P.obj M) ≫ G.map (inverseOrZero (α.app M) ≫ F.map (𝟙 _)) at h
    simp only [F.map_id, Category.id_comp] at h
    erw [Category.comp_id] at h
    simpa only [inverseOrZero_eq_inv, ρ, NatIso.isIso_inv_app] using h.symm
  have hc (H) : ρ.app (Q.obj H) ≫ F.map (χ.app H) ≫
      (o.system.extension j).adj.counit.app (T.obj H) =
        T.map ((IntegralSystemRealization.ringedOpenAdj l E j).counit.app H) := by
    have : IsIso (((mateEquiv (IntegralSystemRealization.ringedOpenAdj l E j)
      (o.system.extension j).adj).symm χ).natTrans.app (Q.obj H)) := hα (Q.obj H)
    have h := inverse_mate_counit_square (IntegralSystemRealization.ringedOpenAdj l E j)
      (o.system.extension j).adj χ (𝟙 (T.obj H))
    change inverseOrZero (α.app (Q.obj H)) ≫ F.map (χ.app H ≫ G.map (𝟙 _)) ≫
      (o.system.extension j).adj.counit.app (T.obj H) =
        T.map ((IntegralSystemRealization.ringedOpenAdj l E j).counit.app H) ≫ 𝟙 _ at h
    simp only [G.map_id, Category.comp_id] at h
    erw [Category.comp_id] at h
    simpa only [inverseOrZero_eq_inv, ρ, NatIso.isIso_inv_app] using h
  have he := projection_inverse_square
    (IntegralSystemRealization.ringedOpenAdj l E j) (o.system.extension j).adj
    TA TB TC TD (tensorOrdinaryR l E o (W a)) (tensorOrdinaryR l E o (W b)) χ ρ
    (IntegralSystemRealization.ringedTensorPull l E o.ringed j)
    (pullbackTensorSystemComparison l E j) hu hc
    (fun H N ↦ canonicalReductionPullTensor l E o j H N)
    M N ((o.ringedOpens.projection j).inv.app (M, N))
    ((o.opens.projection j).inv.app (R.obj M, T.obj N))
    (o.ringedOpens.projection_transpose j M N)
    (o.opens.projection_transpose j (R.obj M) (T.obj N))
  let qL := (tensorOrdinaryR l E o (W b)).app (P.obj M, N) ≫
    TD.map (Prod.mkHom (ρ.app M) (𝟙 (T.obj N)))
  let qR := ρ.app (TA.obj (M, Q.obj N)) ≫
    F.map ((tensorOrdinaryR l E o (W a)).app (M, Q.obj N) ≫
      TC.map (Prod.mkHom (𝟙 (R.obj M)) (χ.app N)))
  have he' : qR ≫ (o.opens.projection j).inv.app (R.obj M, T.obj N) =
      T.map ((o.ringedOpens.projection j).inv.app (M, N)) ≫ qL := by
    simpa only [qR, qL, Category.assoc] using he
  have hn := (o.opens.projection j).inv.naturality (Prod.mkHom x y)
  dsimp only [IntegralSystemRealization.openTensorLeft,
    IntegralSystemRealization.openTensorRight, Functor.comp_map, Functor.prod_map,
    Functor.id_map] at hn
  have hL : (Word.tensor (Word.open j hj hq B) C).ordinaryR l E o K =
      qL ≫ TD.map (Prod.mkHom (F.map x) y) := by
    change (tensorOrdinaryR l E o (W b)).app (P.obj M, N) ≫
        TD.map (Prod.mkHom (inverseOrZero (α.app M) ≫ F.map x) y) = _
    simp only [qL, ρ, inverseOrZero_eq_inv, NatIso.isIso_inv_app, Category.assoc,
      ← TD.map_comp, prod_comp]
    erw [Category.id_comp]
  have hR : V.ordinaryR l E o K =
      qR ≫ F.map (TC.map (Prod.mkHom x (G.map y))) := by
    change inverseOrZero (α.app (TA.obj (M, Q.obj N))) ≫
      F.map ((tensorOrdinaryR l E o (W a)).app (M, Q.obj N) ≫
        TC.map (Prod.mkHom x (χ.app N ≫ G.map y))) = _
    simp only [qR, ρ, inverseOrZero_eq_inv, NatIso.isIso_inv_app, Category.assoc,
      ← F.map_comp, ← TC.map_comp, prod_comp]
    all_goals erw [Category.id_comp]
  have hinv :
      V.ordinaryR l E o K ≫
          (o.opens.projection j).inv.app
            (B.systemValue l E W location o (inputReduction l E W location K),
              C.systemValue l E W location o (inputReduction l E W location K)) =
        T.map ((o.ringedOpens.projection j).inv.app (M, N)) ≫
          (Word.tensor (Word.open j hj hq B) C).ordinaryR l E o K := by
    rw [hR, hL]
    simp only [Category.assoc]
    rw [hn, reassoc_of% he']
  exact forward_of_inverse T
    ((o.ringedOpens.projection j).app (M, N))
    ((o.opens.projection j).app
      (B.systemValue l E W location o (inputReduction l E W location K),
        C.systemValue l E W location o (inputReduction l E W location K)))
    ((Word.tensor (Word.open j hj hq B) C).ordinaryR l E o K)
    (V.ordinaryR l E o K) hinv

/-- The coefficient square for the open tensor projection formula.
Source: blueprint `fix-prop-coherence.proof.md`, open-adjunction/clopen expansion
(blueprint: lem-sf-open-tensor-reduction-square).
Proof: Work first with the ordinary word comparison. The canonical open reduction
mate is invertible, and its inverse satisfies the open unit and counit squares.
Use canonicalReductionPullTensor for the ordinary restriction/tensor square.
The prescribed projection transpose fields express the two inverse projection
maps through the tensor unit and the restriction/tensor isomorphism. Tensor
naturality and the unit square identify their transposes; naturality of the
inverse open mate and the counit square identify their adjuncts. Insert the two
child word comparisons by naturality, then invert the resulting projection
square. Finally the ordinary-to-completed comparison and invertibility of the
stipulated short endpoint completion maps give Assertion. Every calculation is
on whole systems before finite evaluation. -/
theorem openTensorReductionSquare
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    (hStructural : StructuralSquares.{u, s, i} Cf.l E D o)
    {S : Type s} (W : S → Scheme.{u}) (hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
      (hq : QuasiCompact j) (B : Word W location a) (C : Word W location b)
    (hSourceLength : (Word.tensor (Word.open j hj hq B) C).length ≤ 3)
    (hTargetLength : (Word.open j hj hq (Word.tensor B (Word.pull j (by let := hj; infer_instance)
          (by let := hj; infer_instance) hq C))).length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hSource : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.tensor
      (Word.open j hj hq B) C))
    (hTarget : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.open j hj hq
      (Word.tensor B
      (Word.pull j (by let := hj; infer_instance)
          (by let := hj; infer_instance) hq C))))
    (hGenerator : GeneratorKind.admissible Cf.l E W location o K lo hi torLo torHi
      (GeneratorKind.openTensor j hj hq B C)) :
    Assertion Cf.l E W location o K (GeneratorKind.openTensor j hj hq B C) := by
  have _ : StructuralSquares.{u, s, i} Cf.l E D o := hStructural
  have _ := hW
  have _ := hGenerator
  exact assertion_of_ordinary_square Cf.l E o K lo hi torLo torHi hInputs
    (GeneratorKind.openTensor j hj hq B C) hSourceLength hTargetLength hSource hTarget
    (ordinary_open_tensor Cf.l E o j hj hq B C K)
end WeilConjectures.OpenInterchangeReduction
