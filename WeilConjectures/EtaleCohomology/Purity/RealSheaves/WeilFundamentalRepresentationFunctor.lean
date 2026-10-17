/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.RealizationNatural

/-!
# The Weil fundamental representation as a tensor functor

The Weil fundamental representation `ℱ ↦ (ℱ_t, ρ_ℱ)` of `def-wf-fundamental-representation`
(`AlgebraicGeometry.WeilGroup.fundamentalRep`) is a functor from lisse Weil sheaves to
representations of the Weil group, a morphism acting on the stalks at the base point
(`AlgebraicGeometry.WeilGroup.fundamentalRepFunctor`). It is a tensor functor:

* the identification `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t`, built from the evaluation pairings
  `(ℱ ⊗ 𝒢)_t × (ℱ^∨)_t → 𝒢_t` and `(ℱ^∨)_t × ℱ_t → ℚ̄_ℓ`, is an isomorphism of representations
  natural in `ℱ` and `𝒢` (`AlgebraicGeometry.WeilGroup.fundamentalRepTensorIso`), the evaluation
  pairings being dinatural;
* the Weil fundamental representation of the constant sheaf `ℚ̄_ℓ` is the trivial
  representation on `ℚ̄_ℓ` (`AlgebraicGeometry.WeilGroup.fundamentalRepUnitEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

variable [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
  {B : BasePointData W}

section StalkMap

/-- The stalk at the base point of the identity is the identity. -/
lemma stalkMap_id (X : LisseWeilSheaf K l C) :
    stalkMap (B := B) (𝟙 X : X ⟶ X).hom X.property X.property = LinearMap.id := by
  have h : WeilSheaf.toLisseMap (𝟙 X : X ⟶ X).hom X.property X.property = 𝟙 _ := rfl
  rw [stalkMap, h, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- Stalks at the base point are compatible with composition. -/
lemma stalkMap_comp {X Y Z : LisseWeilSheaf K l C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    stalkMap (B := B) (f ≫ g).hom X.property Z.property =
      stalkMap (B := B) g.hom Y.property Z.property ∘ₗ
        stalkMap (B := B) f.hom X.property Y.property := by
  have h : WeilSheaf.toLisseMap (f ≫ g).hom X.property Z.property =
      WeilSheaf.toLisseMap f.hom X.property Y.property ≫
        WeilSheaf.toLisseMap g.hom Y.property Z.property := rfl
  rw [stalkMap, h, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- The stalk at the base point of `f ⊗ g = [f^∨, g]`. -/
lemma stalkMap_tensorHom_apply {F F' G G' : WeilSheaf K l C} (f : F ⟶ F') (g : G ⟶ G')
    (hF : F.IsLisse) (hF' : F'.IsLisse) (hG : G.IsLisse) (hG' : G'.IsLisse)
    (z : LisseMonodromy.StalkSpace B.t ((F.tensorObj G hF).toLisse (hF.tensorObj hG))) :
    stalkMap (B := B) (WeilSheaf.tensorHom f g hF hF') (hF.tensorObj hG) (hF'.tensorObj hG') z =
      ((stalkFunctor l B.t).map
        ((Mod.ihomMap (WeilSheaf.dualMap f hF hF').hom.hom.f).app G'.obj.carrier).hom).hom
        (((stalkFunctor l B.t).map
          ((AdicSheaf.ihom (F.dual hF).obj.carrier).map g.hom.hom.f).hom).hom z) := by
  have h : (lisseStalk l B.t).map (WeilSheaf.toLisseMap (WeilSheaf.tensorHom f g hF hF')
      (hF.tensorObj hG) (hF'.tensorObj hG')) =
      (stalkFunctor l B.t).map ((AdicSheaf.ihom (F.dual hF).obj.carrier).map g.hom.hom.f).hom ≫
        (stalkFunctor l B.t).map
          ((Mod.ihomMap (WeilSheaf.dualMap f hF hF').hom.hom.f).app G'.obj.carrier).hom := by
    rw [← Functor.map_comp]
    rfl
  rw [stalkMap, h]
  rfl

/-- The evaluation pairing `(ℱ ⊗ 𝒢)_t × (ℱ^∨)_t → 𝒢_t` of the stalks at the base point is
dinatural: `f ⊗ g` corresponds to `x ↦ g ∘ x ∘ f^∨`. -/
lemma tensorStalkLinearMap_stalkMap_tensorHom {F F' G G' : WeilSheaf K l C} (f : F ⟶ F')
    (g : G ⟶ G') (hF : F.IsLisse) (hF' : F'.IsLisse) (hG : G.IsLisse) (hG' : G'.IsLisse)
    (z : LisseMonodromy.StalkSpace B.t ((F.tensorObj G hF).toLisse (hF.tensorObj hG)))
    (d : LisseMonodromy.StalkSpace B.t ((F'.dual hF').toLisse hF'.dual)) :
    tensorStalkLinearMap B F' G' hF' hG'
        (stalkMap (B := B) (WeilSheaf.tensorHom f g hF hF') (hF.tensorObj hG)
          (hF'.tensorObj hG') z) d =
      stalkMap (B := B) g hG hG' (tensorStalkLinearMap B F G hF hG z
        (stalkMap (B := B) (WeilSheaf.dualMap f hF hF') hF'.dual hF.dual d)) := by
  rw [tensorStalkLinearMap_apply, tensorStalkLinearMap_apply,
    stalkMap_tensorHom_apply f g hF hF' hG hG']
  erw [Mod.evaluationPairing_ihomMap, Mod.evaluationPairing_naturality]
  rfl

/-- The evaluation pairing `(ℱ^∨)_t × ℱ_t → ℚ̄_ℓ` of the stalks at the base point is dinatural:
`f^∨` is the transpose of `f`. -/
lemma dualStalkLinearMap_stalkMap_dualMap {F F' : WeilSheaf K l C} (f : F ⟶ F')
    (hF : F.IsLisse) (hF' : F'.IsLisse)
    (d : LisseMonodromy.StalkSpace B.t ((F'.dual hF').toLisse hF'.dual))
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    dualStalkLinearMap B F hF (stalkMap (B := B) (WeilSheaf.dualMap f hF hF') hF'.dual hF.dual d)
        v =
      dualStalkLinearMap B F' hF' d (stalkMap (B := B) f hF hF' v) := by
  simp only [dualStalkLinearMap, WeilCoefficients.dualLinearMap_apply]
  congr 2
  exact Mod.evaluationPairing_ihomMap (stalkFunctor l B.t) f.hom.hom.f (AdicSheaf.unit l _) d v

end StalkMap

variable (D : WeilMonodromyData B)

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence` (subsection `sk-i-real-sheaves`):
the functor `ℱ ↦ (ℱ_t, ρ_ℱ)` from lisse Weil sheaves to representations of the Weil group,
sending a lisse Weil sheaf to its Weil fundamental representation
(`def-wf-fundamental-representation`, `AlgebraicGeometry.WeilGroup.fundamentalRep`) on its stalk
at the base point, and a morphism to its stalk at the base point. -/
noncomputable def fundamentalRepFunctor :
    LisseWeilSheaf K l C ⥤ Rep.{u + 1} (PadicAlgCl l) W.carrier where
  obj X := Rep.of (fundamentalRep M D X.obj X.property)
  map {X Y} f := Rep.ofHom ⟨stalkMap f.hom X.property Y.property, fun w ↦
    LinearMap.ext fun v ↦ stalkMap_fundamentalRep D f.hom _ _ w v⟩
  map_id X := Rep.hom_ext (Representation.IntertwiningMap.ext (stalkMap_id X))
  map_comp f g := Rep.hom_ext (Representation.IntertwiningMap.ext (stalkMap_comp f g))

lemma fundamentalRepFunctor_map_hom_apply {X Y : LisseWeilSheaf K l C} (f : X ⟶ Y)
    (v : LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property)) :
    ((fundamentalRepFunctor M D).map f).hom v = stalkMap f.hom X.property Y.property v :=
  rfl

/-- The Weil fundamental representation of the dual `ℱ^∨` is the contragredient of that of `ℱ`,
through the evaluation pairing of the stalks at the base point
(`AlgebraicGeometry.WeilGroup.nonempty_equiv_fundamentalRep_dual`). -/
noncomputable def fundamentalRepDualEquiv (F : WeilSheaf K l C) (hF : F.IsLisse) :
    (fundamentalRep M D (F.dual hF) hF.dual).Equiv (fundamentalRep M D F hF).dual :=
  Representation.Equiv.mk (LinearEquiv.ofBijective _ (bijective_dualStalkLinearMap F hF))
    fun w ↦ LinearMap.ext fun d ↦ by
      change dualStalkLinearMap B F hF (fundamentalRep M D _ _ w d) =
        (fundamentalRep M D F hF).dual w (dualStalkLinearMap B F hF d)
      refine intertwines_of_geometric_frobLift D _ _ (dualStalkLinearMap B F hF)
        (fun u hu d ↦ ?_) (fun d ↦ ?_) w d
      · refine apply_eq_dual_of_invariant _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_geometric M D _ _ ⟨u, hu⟩, fundamentalRep_geometric M D F hF ⟨u, hu⟩]
        exact dualStalkLinearMap_rep M F hF _ d v
      · refine apply_eq_dual_of_invariant _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_frobLift, fundamentalRep_frobLift]
        exact dualStalkLinearMap_frobStalk M F hF d v

lemma fundamentalRepDualEquiv_apply (F : WeilSheaf K l C) (hF : F.IsLisse) (d) :
    fundamentalRepDualEquiv M D F hF d = dualStalkLinearMap B F hF d :=
  rfl

/-- The Weil fundamental representation of `ℱ ⊗ 𝒢` is the representation on
`Hom((ℱ^∨)_t, 𝒢_t)`, through the evaluation pairing of the stalks at the base point
(`AlgebraicGeometry.WeilGroup.nonempty_equiv_fundamentalRep_tensorObj_linHom`). -/
noncomputable def fundamentalRepTensorObjLinHomEquiv (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    (fundamentalRep M D (F.tensorObj G hF) (hF.tensorObj hG)).Equiv
      (Representation.linHom (fundamentalRep M D (F.dual hF) hF.dual)
        (fundamentalRep M D G hG)) :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective _ (bijective_tensorStalkLinearMap F G hF hG))
    fun w ↦ LinearMap.ext fun d ↦ by
      change tensorStalkLinearMap B F G hF hG (fundamentalRep M D _ _ w d) =
        Representation.linHom _ _ w (tensorStalkLinearMap B F G hF hG d)
      refine intertwines_of_geometric_frobLift D _ _ (tensorStalkLinearMap B F G hF hG)
        (fun u hu d ↦ ?_) (fun d ↦ ?_) w d
      · refine apply_eq_linHom_of_equivariant _ _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_geometric M D _ _ ⟨u, hu⟩, fundamentalRep_geometric M D _ _ ⟨u, hu⟩,
          fundamentalRep_geometric M D G hG ⟨u, hu⟩]
        exact tensorStalkLinearMap_rep M F G hF hG _ d v
      · refine apply_eq_linHom_of_equivariant _ _ _ _ _ (fun d v ↦ ?_) d
        rw [fundamentalRep_frobLift, fundamentalRep_frobLift, fundamentalRep_frobLift]
        exact tensorStalkLinearMap_frobStalk M F G hF hG d v

lemma fundamentalRepTensorObjLinHomEquiv_apply (F G : WeilSheaf K l C) (hF : F.IsLisse)
    (hG : G.IsLisse) (z) :
    fundamentalRepTensorObjLinHomEquiv M D F G hF hG z = tensorStalkLinearMap B F G hF hG z :=
  rfl

/-- The identification `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t` of Weil fundamental representations
(`AlgebraicGeometry.WeilGroup.nonempty_equiv_fundamentalRep_tensorObj`): the composite of
`(ℱ ⊗ 𝒢)_t ≅ Hom((ℱ^∨)_t, 𝒢_t)` and `ℱ_t ⊗ 𝒢_t ≅ Hom((ℱ^∨)_t, 𝒢_t)`, `(ℱ^∨)_t ≅ (ℱ_t)^∨`. -/
noncomputable def fundamentalRepTensorEquiv (X Y : LisseWeilSheaf K l C) :
    (fundamentalRep M D (X.obj.tensorObj Y.obj X.property)
        (X.property.tensorObj Y.property)).Equiv
      ((fundamentalRep M D X.obj X.property).tprod (fundamentalRep M D Y.obj Y.property)) :=
  (fundamentalRepTensorObjLinHomEquiv M D X.obj Y.obj X.property Y.property).trans
    (Representation.Equiv.tprodEquivLinHomOfDual
      (fundamentalRepDualEquiv M D X.obj X.property)).symm

/-- The identification `(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t` is natural in `ℱ` and `𝒢`. -/
lemma fundamentalRepTensorEquiv_naturality {X X' Y Y' : LisseWeilSheaf K l C} (f : X ⟶ X')
    (g : Y ⟶ Y')
    (z : LisseMonodromy.StalkSpace B.t
      ((X.obj.tensorObj Y.obj X.property).toLisse (X.property.tensorObj Y.property))) :
    fundamentalRepTensorEquiv M D X' Y' (stalkMap (B := B)
        (WeilSheaf.tensorHom f.hom g.hom X.property X'.property)
        (X.property.tensorObj Y.property) (X'.property.tensorObj Y'.property) z) =
      TensorProduct.map (stalkMap f.hom X.property X'.property)
        (stalkMap g.hom Y.property Y'.property) (fundamentalRepTensorEquiv M D X Y z) := by
  have hT (X Y : LisseWeilSheaf K l C) (z) :
      Representation.Equiv.tprodEquivLinHomOfDual (σ := fundamentalRep M D Y.obj Y.property)
          (fundamentalRepDualEquiv M D X.obj X.property) (fundamentalRepTensorEquiv M D X Y z) =
        tensorStalkLinearMap B X.obj Y.obj X.property Y.property z := by
    rw [fundamentalRepTensorEquiv, Representation.Equiv.trans_apply,
      Representation.Equiv.apply_symm_apply]
    rfl
  apply EquivLike.injective (Representation.Equiv.tprodEquivLinHomOfDual
    (σ := fundamentalRep M D Y'.obj Y'.property) (fundamentalRepDualEquiv M D X'.obj X'.property))
  rw [hT, Representation.Equiv.tprodEquivLinHomOfDual_map
    (fundamentalRepDualEquiv M D X.obj X.property) (fundamentalRepDualEquiv M D X'.obj X'.property)
    (stalkMap (B := B) f.hom X.property X'.property)
    (stalkMap (B := B) g.hom Y.property Y'.property)
    (stalkMap (B := B) (WeilSheaf.dualMap f.hom X.property X'.property) X'.property.dual
      X.property.dual)
    (fun d v ↦ dualStalkLinearMap_stalkMap_dualMap f.hom X.property X'.property d v), hT]
  ext d
  exact tensorStalkLinearMap_stalkMap_tensorHom f.hom g.hom X.property X'.property Y.property
    Y'.property z d

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence` (subsection `sk-i-real-sheaves`):
the Weil fundamental representation is a tensor functor. The identification
`(ℱ ⊗ 𝒢)_t ≅ ℱ_t ⊗ 𝒢_t` (`AlgebraicGeometry.WeilGroup.fundamentalRepTensorEquiv`) is an
isomorphism of bifunctors from pairs of lisse Weil sheaves to representations of the Weil
group. -/
noncomputable def fundamentalRepTensorIso :
    LisseWeilSheaf.tensor K l C ⋙ fundamentalRepFunctor M D ≅
      (fundamentalRepFunctor M D).prod (fundamentalRepFunctor M D) ⋙
        Rep.tprodFunctor.{u + 1} (PadicAlgCl l) W.carrier :=
  NatIso.ofComponents (fun X ↦ Rep.mkIso (fundamentalRepTensorEquiv M D X.1 X.2)) fun f ↦
    Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z ↦
      fundamentalRepTensorEquiv_naturality M D f.1 f.2 z))

lemma fundamentalRepTensorIso_hom_app_hom_apply (X : LisseWeilSheaf K l C × LisseWeilSheaf K l C)
    (z : LisseMonodromy.StalkSpace B.t
      ((X.1.obj.tensorObj X.2.obj X.1.property).toLisse (X.1.property.tensorObj X.2.property))) :
    ((fundamentalRepTensorIso M D).hom.app X).hom z = fundamentalRepTensorEquiv M D X.1 X.2 z :=
  rfl

/-- The Weil fundamental representation of the constant sheaf `ℚ̄_ℓ` is trivial: the transport
along loops and the Frobenius `Φ` act trivially on its stalk at the base point. -/
lemma fundamentalRep_adicConstant_apply (w : W.carrier)
    (v : LisseMonodromy.StalkSpace B.t
      ((WeilSheaf.adicConstant K l C).toLisse (WeilSheaf.isLisse_adicConstant K l C))) :
    fundamentalRep M D (WeilSheaf.adicConstant K l C) (WeilSheaf.isLisse_adicConstant K l C) w v =
      v := by
  refine intertwines_of_geometric_frobLift D
    (fundamentalRep M D (WeilSheaf.adicConstant K l C) (WeilSheaf.isLisse_adicConstant K l C))
    (Representation.trivial (PadicAlgCl l) W.carrier _) LinearMap.id (fun u hu v ↦ ?_) (fun v ↦ ?_)
    w v
  · rw [fundamentalRep_geometric M D _ _ ⟨u, hu⟩, LisseMonodromy.rep_apply,
      LisseMonodromy.monoLinear]
    erw [mono_hom_app_unit M]
    rfl
  · have h : (frobStalkIso M B (WeilSheaf.adicConstant K l C)
        (WeilSheaf.isLisse_adicConstant K l C)).hom = 𝟙 _ := by
      rw [frobStalkIso_hom_eq]
      exact mono_comp_stalkFrobTransport_unit M
    rw [fundamentalRep_frobLift]
    exact congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) h

/-- Blueprint `prop-wf-weil-sheaf-representation-equivalence` (subsection `sk-i-real-sheaves`):
the Weil fundamental representation of the constant sheaf `ℚ̄_ℓ` is the trivial representation
on `ℚ̄_ℓ`: its stalk is a line, on which the Weil group acts trivially. -/
noncomputable def fundamentalRepUnitEquiv :
    (fundamentalRep M D (LisseWeilSheaf.unit K l C).obj (LisseWeilSheaf.unit K l C).property).Equiv
      (Representation.trivial (PadicAlgCl l) W.carrier (PadicAlgCl l)) :=
  Representation.Equiv.mk (LinearEquiv.ofFinrankEq _ _
    ((finrank_globalSections_upperStar_adicConstantSheaf B.t).trans
      (Module.finrank_self (PadicAlgCl l)).symm))
    fun w ↦ LinearMap.ext fun v ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply]
      exact congrArg _ (fundamentalRep_adicConstant_apply M D w v)

end AlgebraicGeometry.WeilGroup
