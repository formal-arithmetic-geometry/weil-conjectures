/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module


/-!
# Work in progress: internal composition and the composite of tensor products

Not imported anywhere. Notes for resuming
`AlgebraicGeometry.WeilComplex.nonempty_iso_tensorLisse_comp`
and the Weil compatibility `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarIhomComparison_comm`.

Plan for `tensorLisse_comp` (`a = G^∨`, `b = H^∨`, `T = [a, H] = G ⊗ H`, `D = T^∨`): build the
Weil iso `[D, K] ≅ [a, [b, K]]` natural in `K`, with `Ψ = ihomComp b D K ≫ ihomMap δ̂` where
`δ̂ : a ⟶ [b, D]` is `transpose (ihom a).map (transpose 𝟙_b) ≫ σ`, `σ` the internal swap
`transpose (transpose 𝟙 ≫ ihomComp ..)`. Weil compatibility via `ProEtaleWeilSheaf.homToIhom`;
isomorphy for lisse `a` by checking on a weakly étale cover trivialising `a` (as in
`IsAdicLisseSheaf.isIso_adicUpperStarIhomComparison`), reducing to `a = ℚ̄_ℓ` by additivity.

Kernel performance: avoid any defeq between `((g)^*ᵃ[l].obj M).X` / `((g)_*ᵃ[l].obj M).X` and
`(g)^*[_].obj M.X` / `(g)_*[_].obj M.X` in kernel-checked terms (`erw`, `exact` up to defeq):
the kernel unfolds the sheaf functors and takes minutes. State helper lemmas for variable
isomorphisms/functors (cf. `inv_app_adicUpperStar_obj_X`).

Proof of `upperStarIhomComparison_comm` that elaborates but is too slow in the kernel:
```
  have h3 := uncurryHom_adicUpperStarIhomComparison
    (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) A.carrier B.carrier
  rw [Mod.uncurryHom] at h3
  refine ProEtaleWeilSheaf.homToIhom_comm _ _ _ _ ?_
  erw [h3]
  exact upperStarStr_pairing
    (c := (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
      (comp_over φ (Spec (CommRingCat.of k₀)))).symm)
    ((ihomFunctor k₀ l Y A).obj B).str A.str B.str (Mod.evaluation A.carrier B.carrier)
    (ProEtaleWeilSheaf.ihom_evaluation_str A B)
```

WIP gadget (proofs not finished):
```
namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {Z : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

/-- The evaluation `𝓗om(M, N) ⊗ M ⟶ N` is linear in `M`. -/
set_option maxHeartbeats 60000 in
lemma isLinearRight_evaluation (M N : AdicSheaf l Z) :
    Mod.IsLinearRight (X := ((AdicSheaf.ihom M).obj N).X) (Mod.evaluation M N) := by
  rw [Mod.IsLinearRight, Mod.whiskerLeft_act_evaluation]
  simp only [Mod.rightAct, comp_whiskerRight, Category.assoc]
  rw [Mod.act_whiskerRight_evaluation]

/-- The uncurried internal composition `(g ⊗ f) ⊗ m ↦ g (f m)`. -/
noncomputable abbrev ihomCompAux (M N K : AdicSheaf l Z) :
    (((AdicSheaf.ihom N).obj K).X ⊗ ((AdicSheaf.ihom M).obj N).X) ⊗ M.X ⟶ K.X :=
  (α_ _ _ _).hom ≫ ((AdicSheaf.ihom N).obj K).X ◁ Mod.evaluation M N ≫ Mod.evaluation N K

set_option maxHeartbeats 60000 in
lemma isLinearRight_ihomCompAux (M N K : AdicSheaf l Z) :
    Mod.IsLinearRight (ihomCompAux M N K) := by
  have h₁ := isLinearRight_evaluation M N
  have h₂ := isLinearRight_evaluation N K
  rw [Mod.IsLinearRight] at h₁ h₂
  rw [Mod.IsLinearRight]
  unfold ihomCompAux
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, h₁]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [h₂, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, BraidedCategory.braiding_tensor_left_hom]
  simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  monoidal

/-- The internal composition, curried once: `g ⊗ f ↦ g ∘ f`. -/
noncomputable abbrev ihomCompCurry (M N K : AdicSheaf l Z) :
    ((AdicSheaf.ihom N).obj K).X ⊗ ((AdicSheaf.ihom M).obj N).X ⟶
      ((AdicSheaf.ihom M).obj K).X :=
  Mod.curry (ihomCompAux M N K) (isLinearRight_ihomCompAux M N K)

set_option maxHeartbeats 60000 in
lemma ihomCompCurry_evaluation (M N K : AdicSheaf l Z) :
    ihomCompCurry M N K ▷ M.X ≫ Mod.evaluation M K = ihomCompAux M N K :=
  Mod.curry_evaluation _ _

set_option maxHeartbeats 60000 in
lemma isLinearRight_ihomCompCurry (M N K : AdicSheaf l Z) :
    Mod.IsLinearRight (ihomCompCurry M N K) := by
  have h₂ := isLinearRight_evaluation N K
  rw [Mod.IsLinearRight] at h₂
  apply Mod.hom_ext_of_evaluation (D := M)
  rw [comp_whiskerRight, Category.assoc, ihomCompCurry_evaluation]
  simp only [comp_whiskerRight, Category.assoc]
  conv_rhs => rw [Mod.act_whiskerRight_evaluation, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ihomCompCurry_evaluation]
  unfold ihomCompAux
  conv_lhs => rw [associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Mod.act_whiskerRight_evaluation]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [h₂, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  trace_state
  sorry

set_option maxHeartbeats 60000 in
lemma ihomCompCurry_linear_left (M N K : AdicSheaf l Z) :
    Mod.act ((AdicSheaf.ihom N).obj K).X ▷ ((AdicSheaf.ihom M).obj N).X ≫
        ihomCompCurry M N K =
      (α_ _ _ _).hom ≫ adicConstantSheaf l Z ◁ ihomCompCurry M N K ≫
        Mod.act ((AdicSheaf.ihom M).obj K).X := by
  apply Mod.hom_ext_of_evaluation (D := M)
  rw [comp_whiskerRight, Category.assoc, ihomCompCurry_evaluation]
  simp only [comp_whiskerRight, Category.assoc]
  conv_rhs => rw [Mod.act_whiskerRight_evaluation, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ihomCompCurry_evaluation]
  unfold ihomCompAux
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    Mod.act_whiskerRight_evaluation]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  trace_state
  sorry

/-- **Internal composition** `𝓗om(N, K) ⟶ 𝓗om(𝓗om(M, N), 𝓗om(M, K))`, `g ↦ (f ↦ g ∘ f)`. -/
noncomputable def ihomComp (M N K : AdicSheaf l Z) :
    (AdicSheaf.ihom N).obj K ⟶
      (AdicSheaf.ihom ((AdicSheaf.ihom M).obj N)).obj ((AdicSheaf.ihom M).obj K) :=
  AdicSheaf.curryHom (ihomCompCurry M N K) (isLinearRight_ihomCompCurry M N K)
    (ihomCompCurry_linear_left M N K)

/-- The uncurried form of the internal composition. -/
set_option maxHeartbeats 60000 in
lemma ihomComp_evaluation (M N K : AdicSheaf l Z) :
    (ihomComp M N K).hom ▷ ((AdicSheaf.ihom M).obj N).X ≫
        Mod.evaluation ((AdicSheaf.ihom M).obj N) ((AdicSheaf.ihom M).obj K) =
      ihomCompCurry M N K :=
  AdicSheaf.curryHom_evaluation _ _ _

end AlgebraicGeometry.ProEtale.AdicSheaf
```

Former `IhomLisse/UpperStarWeil.lean` (did not build within the time limit, the kernel check of
`ihomFunctorCompUpperStarIso` being too slow) and the corresponding part of
`FourierInversion/UpperStar.lean`:
```
namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The comparison `φ^* [A, B] ⟶ [φ^* A, φ^* B]` is compatible with the Weil structures. -/
lemma upperStarIhomComparison_comm (A B : ProEtaleWeilSheaf k₀ l Y) :
    (WeilSheaf.frobeniusPullback k₀ l X).map (adicUpperStarIhomComparison l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
        A.carrier B.carrier) ≫
      ((ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A)).obj ((upperStar k₀ l φ).obj B)).obj.str =
    ((upperStar k₀ l φ).obj ((ihomFunctor k₀ l Y A).obj B)).obj.str ≫
      adicUpperStarIhomComparison l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
        A.carrier B.carrier := by
  -- TODO: the proof below (via `ProEtaleWeilSheaf.homToIhom_comm` and
  -- `ProEtale.upperStarStr_pairing`) elaborates but is too slow in the kernel; see
  -- `WeilConjectures/WeilSheaf/IhomLisse/CompWip.lean`.
  sorry

/-- **Pullback commutes with the internal hom out of a lisse pro-étale Weil sheaf**:
`φ^* [A, -] ≅ [φ^* A, φ^* -]`. -/
noncomputable def ihomFunctorCompUpperStarIso (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : IsAdicLisseSheaf A.carrier) :
    ihomFunctor k₀ l Y A ⋙ upperStar k₀ l φ ≅
      upperStar k₀ l φ ⋙ ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A) :=
  NatIso.ofComponents (fun B ↦
    have := hA.isIso_adicUpperStarIhomComparison
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) B.carrier
    IsoAlgebra.isoMk (asIso (adicUpperStarIhomComparison l
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
      A.carrier B.carrier)) (upperStarIhomComparison_comm φ A B))
    fun f ↦ IsoAlgebra.hom_ext (adicUpperStarIhomComparison_naturality _ _ f.hom.f)

end AlgebraicGeometry.ProEtaleWeilSheaf
/-- The dual of the pullback of a lisse Weil sheaf is the pullback of its dual. -/
noncomputable def WeilSheaf.upperStarDualIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    ((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ≅
      (WeilSheaf.upperStar φ).obj (G.dual hG) :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj G.obj)).mapIso
        ((ObjectProperty.ι _).mapIso (WeilSheaf.upperStarAdicConstantIso φ)).symm ≪≫
      ((ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso φ G.obj hG).app
        (ProEtaleWeilSheaf.adicConstant k₀ l Y)).symm)

/-- Pullback of pro-étale Weil sheaves commutes with the internal hom out of the dual of a lisse
Weil sheaf. -/
noncomputable def ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    ProEtaleWeilSheaf.ihomFunctor k₀ l Y (G.dual hG).obj ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ ≅
      ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ ProEtaleWeilSheaf.ihomFunctor k₀ l X
        (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj :=
  ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso φ (G.dual hG).obj hG.dual ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft
      ((ObjectProperty.ι _).mapIso (WeilSheaf.upperStarDualIso φ G hG)))

/-- Pullback commutes with the tensor product with a lisse Weil sheaf:
`φ^*(G ⊗ K) ≅ φ^* G ⊗ φ^* K`. -/
theorem WeilComplex.nonempty_iso_tensorLisse_comp_upperStar {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty (WeilComplex.tensorLisse G hG ⋙ WeilComplex.upperStar φ ≅
      WeilComplex.upperStar φ ⋙ WeilComplex.tensorLisse ((WeilSheaf.upperStar φ).obj G)
        (ProEtale.IsAdicLisseSheaf.upperStar _ hG)) := by
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (G.dual hG).obj hG.dual
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor
    (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj
    (ProEtale.IsAdicLisseSheaf.upperStar _ hG).dual
  exact ⟨((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.ihomLisseCompιIso _ hG.dual) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _ ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso
            (ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso φ G hG) ≪≫
          Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorIsoMapDerivedCategory _).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (WeilComplex.ihomLisseCompιIso _ _).symm ≪≫
      (Functor.associator _ _ _).symm)⟩


end AlgebraicGeometry
```
-/
