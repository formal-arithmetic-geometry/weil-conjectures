/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.CechModuleSheafFunctor

/-! # Comparing the sheaf and sectionwise Čech complexes

Source: blueprint `lem-pc-cech-resolution`, displayed complex and proof paragraph 1.
(blueprint: lem-pc-cech-module-sheaf-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry

/-- Forget to the presheaf of modules over global functions. -/
private noncomputable def cechForgetModuleSheaf (X : Scheme.{u}) :
    X.Modules ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op

private instance cechForgetModuleSheaf_preservesProducts (X : Scheme.{u}) (α : Type u) :
    PreservesLimitsOfShape (Discrete α) (cechForgetModuleSheaf X) := by
  apply preservesLimitsOfShape_of_evaluation
  intro V
  change PreservesLimitsOfShape (Discrete α)
    (SheafOfModules.evaluation X.ringCatSheaf V ⋙
      ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (isTerminalTop.op.to V)).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the intersection sheaf amounts to precomposing by binary product. -/
private noncomputable def cechIntersectionPresheafIso {X : Scheme.{u}} (F : X.Modules)
    (W : X.Opens) :
    (cechForgetModuleSheaf X).obj (cechIntersectionSheaf F W) ≅
      (prod.functor.obj W).op ⋙ F.presheafModuleCat := by
  refine NatIso.ofComponents (fun V => ?_) ?_
  · refine (ModuleCat.restrictScalarsComp'App
      (X.ringCatSheaf.obj.map (isTerminalTop.op.to V)).hom
      (X.ringCatSheaf.obj.map (prod.snd : W ⨯ V.unop ⟶ V.unop).op).hom
      (X.ringCatSheaf.obj.map (isTerminalTop.op.to (op (W ⨯ V.unop)))).hom ?_
      (F.val.obj (op (W ⨯ V.unop)))).symm
    rw [← RingCat.hom_comp, ← Functor.map_comp]
    congr 2
  · intro V T g
    ext x
    rfl

/-- Product comparisons are natural on formal coproducts. -/
private noncomputable def formalEvalOpCompIso
    {C A B : Type*} [Category C] [Category A] [Category B]
    [HasProducts.{u} A] [HasProducts.{u} B] (P : Cᵒᵖ ⥤ A) (G : A ⥤ B)
    [∀ α : Type u, PreservesLimitsOfShape (Discrete α) G] :
    (FormalCoproduct.evalOp.{u} C A).obj P ⋙ G ≅
      (FormalCoproduct.evalOp.{u} C B).obj (P ⋙ G) := by
  refine NatIso.ofComponents (fun T =>
    asIso (piComparison G (fun i => P.obj (op (T.unop.obj i))))) ?_
  intro T Z f
  apply Pi.hom_ext
  intro i
  simp only [FormalCoproduct.evalOp, Functor.comp_obj, Functor.comp_map, asIso_hom,
    Category.assoc]
  rw [piComparison_comp_π G (fun i => P.obj (op (Z.unop.obj i))) i]
  rw [← Category.assoc, ← G.map_comp]
  simp only [Pi.lift_π, Functor.map_comp, Category.assoc, piComparison_comp_π_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The scalar comparisons form an isomorphism of opposite-opens functors. -/
private noncomputable def cechIntersectionFunctorIso {X : Scheme.{u}} (F : X.Modules) :
    cechModuleSheafFunctor F ⋙ cechForgetModuleSheaf X ≅
      (prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat := by
  refine NatIso.ofComponents (fun W => cechIntersectionPresheafIso F W.unop) ?_
  intro W Z f
  ext V x
  rfl

/-- Cosimplicial comparison obtained from natural product comparisons. -/
private noncomputable def cechModuleSheafCosimplicialIso
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules) :
    ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        (cechModuleSheafFunctor F)) ⋙ cechForgetModuleSheaf X ≅
      (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat) :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
      (formalEvalOpCompIso (cechModuleSheafFunctor F) (cechForgetModuleSheaf X)) ≪≫
    isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
      ((FormalCoproduct.evalOp _ _).mapIso (cechIntersectionFunctorIso F))

/-- Product comparison, followed by the sectionwise scalar comparison. -/
private noncomputable def cechModuleSheafDegreeIso {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (p : ℕ) :
    (cechForgetModuleSheaf X).obj ((cechModuleSheafComplex U F).X p) ≅
      ((cechComplexFunctor U).obj
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p :=
  asIso (piComparison (cechForgetModuleSheaf X)
      (fun y : Fin (p + 1) → ι => cechIntersectionSheaf F (∏ᶜ fun l => U (y l)))) ≪≫
    Pi.mapIso (fun y => cechIntersectionPresheafIso F (∏ᶜ fun l => U (y l)))

set_option backward.isDefEq.respectTransparency false in
/-- Projection equation for the degree comparison. -/
private theorem cechModuleSheafDegreeIso_hom_π {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (p : ℕ) (y : Fin (p + 1) → ι) :
    (cechModuleSheafDegreeIso U F p).hom ≫
        Pi.π (fun y : Fin (p + 1) → ι =>
          (prod.functor.obj (∏ᶜ fun l => U (y l))).op ⋙ F.presheafModuleCat) y =
      (cechForgetModuleSheaf X).map
        (Pi.π (fun y : Fin (p + 1) → ι =>
          cechIntersectionSheaf F (∏ᶜ fun l => U (y l))) y) ≫
        (cechIntersectionPresheafIso F (∏ᶜ fun l => U (y l))).hom := by
  simp only [cechModuleSheafDegreeIso, Iso.trans_hom, Category.assoc, asIso_hom]
  rw [Pi.mapIso_hom_π
    (fun y : Fin (p + 1) → ι => cechIntersectionPresheafIso F (∏ᶜ fun l => U (y l))) y]
  rw [piComparison_comp_π_assoc]

private instance cechForgetModuleSheaf_additive (X : Scheme.{u}) :
    (cechForgetModuleSheaf X).Additive where
  map_add := by intros; rfl

/-- Coface compatibility follows from the cosimplicial comparison. -/
private theorem cechModuleSheafDegreeIso_coface {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (p : ℕ) (i : Fin (p + 2)) :
    (cechForgetModuleSheaf X).map
        (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
          (cechModuleSheafFunctor F)).δ i) ≫
      (cechModuleSheafDegreeIso U F (p + 1)).hom =
    (cechModuleSheafDegreeIso U F p).hom ≫
      (((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
        ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
          (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).δ i) := by
  have hc (n : ℕ) : (cechModuleSheafCosimplicialIso U F).hom.app
      (SimplexCategory.mk n) = (cechModuleSheafDegreeIso U F n).hom := by
    dsimp [cechModuleSheafCosimplicialIso, formalEvalOpCompIso,
      cechIntersectionFunctorIso, cechModuleSheafDegreeIso,
      FormalCoproduct.evalOp, Pi.mapIso]
    rfl
  simpa only [Functor.comp_map, CosimplicialObject.δ, hc] using
    (cechModuleSheafCosimplicialIso U F).hom.naturality (SimplexCategory.δ i)

set_option backward.isDefEq.respectTransparency false in
/-- The concrete module-sheaf Čech complex agrees with the Čech complex of its
section presheaves, including the coordinates of the degree-zero restriction map.
Source: blueprint `lem-pc-cech-resolution`, displayed complex and proof paragraph 1.
(blueprint: lem-pc-cech-module-sheaf-comparison)

Proof: write G for the forgetful functor from module sheaves to presheaves of global
modules. For every W and V, the over-site definition of cechIntersectionSheaf has
sections F(W × V). Its O_X(V)-action is restriction along prod.snd. Applying G restricts
scalars once more along O_X(X) -> O_X(V). The composite is the unique restriction
O_X(X) -> O_X(W × V), so restrictionScalarsComp gives a natural isomorphism
G(P(W)) ≅ (V ↦ F(W × V)) of presheaves of global modules. Restriction in both variables
is induced by F, so these isomorphisms commute with every morphism of opposite opens.
G preserves products: module-sheaf products are computed on sections, and restriction
of scalars preserves products. In degree p compose the product comparison for G with
the product of the preceding isomorphisms at W = product_l U(y(l)). Projection to y
identifies every coface with the restriction along the corresponding product map.
Consequently the isomorphisms commute with the alternating sums, giving the differential
identity. In degree zero the augmentation₀ is Pi.lift of the over-adjunction units.
Its projection on V is precisely F.map prod.snd.op. The product comparison and scalar
restriction isomorphisms preserve that underlying map, yielding the coordinate identity.
No covering hypothesis is used. When ι is empty, products are terminal objects and the
same product comparison and projection arguments apply; the coordinate assertion is
vacuous. -/
theorem exists_cechModuleSheafComparison
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (F : X.Modules) :
    ∃ (e : ∀ p : ℕ,
      (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj
          ((cechModuleSheafComplex U F).X p).val ≅
        ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).X p),
      (∀ p : ℕ,
        (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((cechModuleSheafComplex U F).d p (p + 1)).val ≫ (e (p + 1)).hom =
          (e p).hom ≫ ((cechComplexFunctor U).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1)) ∧
      (∀ (y : Fin 1 → ι) (V : X.Opens),
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (cechModuleSheafAugmentation₀ U F).val ≫ (e 0).hom ≫
          Pi.π (fun y : Fin 1 → ι =>
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat).obj
                (op (∏ᶜ fun l => U (y l)))) y).app (op V) =
          F.presheafModuleCat.map (prod.snd : (∏ᶜ fun l => U (y l)) ⨯ V ⟶ V).op) := by
  refine ⟨cechModuleSheafDegreeIso U F, ?_, ?_⟩
  · intro p
    have h₁ : (cechModuleSheafComplex U F).d p (p + 1) =
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
            (cechModuleSheafFunctor F)) p :=
      CochainComplex.of_d
        (fun n => ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj (cechModuleSheafFunctor F)).obj
            (SimplexCategory.mk n))
        (AlgebraicTopology.AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
            (cechModuleSheafFunctor F))) p
    have h₂ : ((cechComplexFunctor U).obj
          ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
            (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).d p (p + 1) =
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)) p :=
      CochainComplex.of_d
        (fun n => ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)).obj
                (SimplexCategory.mk n))
        (AlgebraicTopology.AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat))) p
    rw [h₁, h₂]
    change (cechForgetModuleSheaf X).map
        (AlgebraicTopology.AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
            (cechModuleSheafFunctor F)) p) ≫
        (cechModuleSheafDegreeIso U F (p + 1)).hom =
      (cechModuleSheafDegreeIso U F p).hom ≫
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
            ((prod.functor (C := X.Opens)).op ⋙ Functor.opHom _ _ ⋙
              (Functor.whiskeringRight _ _ _).obj F.presheafModuleCat)) p
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum,
      Functor.map_zsmul, Preadditive.sum_comp, Preadditive.comp_sum,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    exact Finset.sum_congr rfl fun i _ =>
      congrArg (fun f => ((-1 : ℤ) ^ (i : ℕ)) • f)
        (cechModuleSheafDegreeIso_coface U F p i)
  · intro y V
    change ((cechForgetModuleSheaf X).map (cechModuleSheafAugmentation₀ U F) ≫
        (cechModuleSheafDegreeIso U F 0).hom ≫
          Pi.π (fun y : Fin 1 → ι =>
            (prod.functor.obj (∏ᶜ fun l => U (y l))).op ⋙ F.presheafModuleCat) y).app
          (op V) = _
    rw [cechModuleSheafDegreeIso_hom_π U F 0 y, ← Category.assoc,
      ← Functor.map_comp]
    have hπ := Pi.lift_π
      (fun y : Fin 1 → ι => cechIntersectionRestriction F (∏ᶜ fun l => U (y l))) y
    refine (congrArg (fun f => ((cechForgetModuleSheaf X).map f ≫
      (cechIntersectionPresheafIso F (∏ᶜ fun l => U (y l))).hom).app (op V)) hπ).trans ?_
    ext x
    rfl

end AlgebraicGeometry
