/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.CechComparisonMapNaturality
public import Sheaf.Paper.CechRefinementCochainMap
public import Sheaf.Paper.CechCupProduct
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.EtaleTensorSections

/-! # Cech cup products and pullback

Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
The comparison maps, refinement cochain map and both bilinear cup products are
characterized by their constructions. The equalities hold for every covering;
isomorphisms are required only to identify the products through inverse comparisons.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Coefficient maps act componentwise in the intersection description of cochains. -/
private theorem cech_coefficient_apply {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F H : X.Modules} (φ : F ⟶ H) (n : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U H.presheafModuleCat n
        (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            φ.val)).f n a) y =
      φ.val.app (op (⨅ j, U (y j)))
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a y) := by
  let ψ := (PresheafOfModules.forgetToPresheafModuleCat
    (op ⊤) isTerminalTop.op).map φ.val
  have hπ := TopCat.Presheaf.cechComplexFunctor_map_f_π U F.presheafModuleCat ψ n y
  have hπa := congrArg (fun k ↦ k a) hπ
  change TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat n y
    (((cechComplexFunctor U).map ψ).f n a) =
    ψ.app _ (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y a) at hπa
  change H.presheaf.map _
    (TopCat.Presheaf.cechComplexFunctorπ U H.presheafModuleCat n y
      (((cechComplexFunctor U).map ψ).f n a)) = _
  rw [hπa]
  exact (Hom.app_presheaf_map φ (homOfLE (TopCat.Presheaf.iInf_le_piObj U y))
    (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y a)).symm

/-- The Alexander--Whitney cochain formula commutes with coefficient morphisms. -/
private theorem cup_coefficient_cochain {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G F₁ G₁ : X.Modules} (φ : F ⟶ F₁) (ψ : G ⟶ G₁)
    (p q : ℕ) (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    (((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        (φ ⊗ₘ ψ).val)).f (p + q)) (cechCupCochain U F G p q a b) =
      cechCupCochain U F₁ G₁ p q
        (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            φ.val)).f p a)
        (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ψ.val)).f q b) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
    (F₁ ⊗ G₁).presheafModuleCat (p + q)).injective
  funext y
  rw [cech_coefficient_apply]
  unfold cechCupCochain
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  erw [tensorHom_app_tmulSection, cech_coefficient_apply, cech_coefficient_apply]
  congr 1
  · exact Hom.app_presheaf_map φ (cupFaceRestriction U y (cupFront p q)) _
  · exact Hom.app_presheaf_map ψ (cupFaceRestriction U y (cupBack p q)) _

private theorem restriction_comp {X : Scheme.{v}}
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{v}) {V W Z : X.Opensᵒᵖ}
    (i : V ⟶ W) (j : W ⟶ Z) (k : V ⟶ Z) (a : P.obj V) :
    P.map j (P.map i a) = P.map k a := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  congr 2

/-- Restricting a pulled-back face section agrees with pulling back its restriction. -/
private theorem refinement_face_apply {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) (n m : ℕ) (y : Fin (n + 1) → ι')
    (face : Fin (m + 1) → Fin (n + 1))
    (a : Γ(F, ⨅ j, U (refine (y (face j))))) :
    ((tensorPullback f).obj F).presheaf.map
        (cechRefinementIntersection f U U' refine hrefine n y).op
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app
          (⨅ j, U (refine (y j)))
          (F.presheaf.map (cupFaceRestriction U (refine ∘ y) face).op a)) =
      ((tensorPullback f).obj F).presheaf.map (cupFaceRestriction U' y face).op
        (((tensorPullback f).obj F).presheaf.map
          (cechRefinementIntersection f U U' refine hrefine m (y ∘ face)).op
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app
            (⨅ j, U (refine (y (face j)))) a)) := by
  have hu := Hom.app_presheaf_map
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F)
    (cupFaceRestriction U (refine ∘ y) face) a
  change ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app
      (⨅ j, U (refine (y j)))
      (F.presheaf.map (cupFaceRestriction U (refine ∘ y) face).op a) =
    ((tensorPullback f).obj F).presheaf.map
      ((Opens.map f.base).map (cupFaceRestriction U (refine ∘ y) face)).op
      (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app
        (⨅ j, U (refine (y (face j)))) a) at hu
  rw [hu]
  let k := ((Opens.map f.base).map (cupFaceRestriction U (refine ∘ y) face)).op ≫
    (cechRefinementIntersection f U U' refine hrefine n y).op
  exact (restriction_comp ((tensorPullback f).obj F).presheaf _ _ k _).trans
    (restriction_comp ((tensorPullback f).obj F).presheaf _ _ k _).symm

/-- Every homology class has a representative in the concrete kernel of the differential. -/
private theorem cycle_class_surjective {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).1 inferInstance

/-- Transport a concrete cocycle through a cochain map. -/
private def map_cycle {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (L.sc n).moduleCatLeftHomologyData.K :=
  (L.sc n).moduleCatCyclesIso.hom
    (HomologicalComplex.cyclesMap φ n ((K.sc n).moduleCatCyclesIso.inv a))

private theorem map_cycle_val {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (map_cycle φ n a).val = φ.f n a.val := by
  have h : (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
      (L.sc n).moduleCatCyclesIso.hom ≫ (L.sc n).moduleCatLeftHomologyData.i =
      (K.sc n).moduleCatLeftHomologyData.i ≫ φ.f n := by
    rw [ShortComplex.moduleCatCyclesIso_hom_i]
    change (K.sc n).moduleCatCyclesIso.inv ≫
      ShortComplex.cyclesMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) ≫
        (L.sc n).iCycles = _
    rw [ShortComplex.cyclesMap_i, ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
    rfl
  exact congrArg (fun k ↦ k a) h

private theorem map_cycle_class {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    HomologicalComplex.homologyMap φ n (cupCycleClass K n a) =
      cupCycleClass L n (map_cycle φ n a) := by
  have h : (K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ ≫
      HomologicalComplex.homologyMap φ n =
      (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
        (L.sc n).homologyπ := by
    exact congrArg ((K.sc n).moduleCatCyclesIso.inv ≫ ·)
      (ShortComplex.homologyπ_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))
  have h' : (K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ ≫
      HomologicalComplex.homologyMap φ n =
      (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
        (L.sc n).moduleCatCyclesIso.hom ≫ (L.sc n).moduleCatCyclesIso.inv ≫
          (L.sc n).homologyπ := by
    rw [Iso.hom_inv_id_assoc]
    exact h
  exact congrArg (fun k ↦ k a) h'

private theorem cycle_val_d {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n m : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) : K.d n m a.val = 0 := by
  have h : (K.sc n).moduleCatCyclesIso.inv ≫ K.iCycles n ≫ K.d n m = 0 := by
    rw [K.iCycles_d, comp_zero]
  change (K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).iCycles ≫ K.d n m = 0 at h
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc] at h
  exact congrArg (fun k ↦ k a) h

/-- Leibniz makes the cup of two concrete cocycles a concrete cocycle. -/
private def cup_cycle {X : Scheme.{v}} {ι : Type v} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K) :
    (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K := by
  refine ⟨cechCupCochain U F G p q a.val b.val, ?_⟩
  have hz : ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).d
      (p + q) (p + q + 1) (cechCupCochain U F G p q a.val b.val) = 0 := by
    rw [cechCupCochain_leibniz, cycle_val_d _ p (p + 1) a, cycle_val_d _ q (q + 1) b]
    have hl : cechCupCochain U F G (p + 1) q 0 b.val = 0 := by
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
        (F ⊗ G).presheafModuleCat (p + 1 + q)).injective
      simp only [cechCupCochain, AddEquiv.apply_symm_apply, map_zero,
        Pi.zero_apply, zero_tmulSection]
      rfl
    have hr : cechCupCochain U F G p (q + 1) a.val 0 = 0 := by
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
        (F ⊗ G).presheafModuleCat (p + (q + 1))).injective
      simp only [cechCupCochain, AddEquiv.apply_symm_apply, map_zero,
        Pi.zero_apply, tmulSection_zero]
      rfl
    rw [hl, hr]
    simp only [map_zero, smul_zero, add_zero]
  change ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).d
    (p + q) ((ComplexShape.up ℕ).next (p + q)) (cechCupCochain U F G p q a.val b.val) = 0
  rw [(ComplexShape.up ℕ).next_eq' (show p + q + 1 = p + q + 1 from rfl)]
  exact hz

/-- Refinement pullback and the signed Cech cup product commute with the canonical
Cech-to-module-cohomology comparisons. If these comparisons are isomorphisms, the
products identify through them. Coefficient and pullback naturality are stated below.
Source: Stacks Project, Tags 01FD, 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).

Proof:
1. Tag 01FD constructs gamma by pulling back tuple sections and restricting to the
refined intersections. Resolve F by J and f-star F by I, resolve f-star I pushed
forward by J-prime, and lift J to J-prime over the adjunction unit. With the four
Cech double complexes B=Cech(U,J), B-prime=Cech(U,J-prime),
B-double-prime=Cech(U,f-star I pushed forward), and A=Cech(U-prime,I), the refinement
formula defines B-double-prime to A. The pentagon commutes by the lift equation and
the other squares by restriction. Inverting the global-sections-to-total alpha
quasi-isomorphisms gives the refinement equality. The canonical comparisons are
those of lem-sc-cech-comparison-map-naturality, characterized by alpha and beta.
2. Tag 07MB restricts the front and back factors to the common intersection and
inserts the total-complex signs. Expanding the alternating differential cancels
adjacent omitted-vertex terms, giving Leibniz and the product on cohomology.
3. Tag 0FKV, for F and G in degree zero, gives the commuting derived square with
RGamma and its cup map mu, followed by RGamma of the map from derived tensor to
ordinary tensor (def-pc-tensor-complex-sheaves supplies the signs). Its proof uses
Godement resolutions, where global sections, total Cech, and RGamma agree, and
reduces to the naive signed pairing. The horizontal comparisons are exactly those
of lem-sc-cech-comparison-map-naturality. Taking classes gives the cup equality.
When the comparisons are isomorphisms, apply their inverses for the final clause.
4. Pullback of a tensor section is the tensor of the two pulled-back sections.
Restrictions, coefficient maps and composition of refinements preserve these
formulas, giving the naturality statements below.
-/
theorem cechCupPullbackCompat (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens) (hU' : iSup U' = ⊤)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cF : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hcF : IsModuleCechComparison U F p cF)
    (cF' : ((cechComplexFunctor U').obj
        ((tensorPullback f).obj F).presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X'.toRingedSpace p).obj ((tensorPullback f).obj F))
    (hcF' : IsModuleCechComparison U' ((tensorPullback f).obj F) p cF')
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (cG : ((cechComplexFunctor U).obj G.presheafModuleCat).homology q ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G)
    (hcG : IsModuleCechComparison U G q cG)
    (cFG : ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q) ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj (@id X.Modules (F ⊗ G)))
    (hcFG : IsModuleCechComparison U (F ⊗ G) (p + q) cFG)
    (cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q))
    (hcup : IsCechCupProduct U F G p q cup)
    (sheafCup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hsheafCup : IsModuleCupProduct F G p q sheafCup) :
    (cechRefinementHomology gamma p ≫ (forget₂ _ AddCommGrpCat).map cF' =
      (forget₂ _ AddCommGrpCat).map cF ≫ moduleCohomologyPullback f F p) ∧
    (∀ a b, cFG (cup a b) = sheafCup (cF a) (cG b)) ∧
    (∀ (hF : IsIso cF) (hG : IsIso cG) (hFG : IsIso cFG) a b,
      cup (inv (I := hF) cF a) (inv (I := hG) cG b) =
        inv (I := hFG) cFG (sheafCup a b)) := by
  sorry

/-- The sheaf cup product is natural in both coefficient sheaves.
Source: Stacks Project, Tags 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: coefficient maps commute with restriction and the section tensor pairing.
Apply them to the Godement-resolution pairing in Step 3 of cechCupPullbackCompat;
the derived tensor map and its augmentation are natural. Taking cohomology gives
the displayed equality, as asserted in Step 4 of the node's proof. -/
theorem moduleCup_coefficient_naturality (X : Scheme.{v})
    (F G F₁ G₁ : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F₁.IsQuasicoherent] [G₁.IsQuasicoherent] (φ : F ⟶ F₁) (ψ : G ⟶ G₁) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hc : IsModuleCupProduct F G p q cup)
    (cup₁ : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F₁ →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G₁ →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F₁ ⊗ G₁)))
    (hc₁ : IsModuleCupProduct F₁ G₁ p q cup₁) :
    ∀ a b, (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).map
        (@id (F ⊗ G ⟶ F₁ ⊗ G₁) (φ ⊗ₘ ψ)) (cup a b) =
      cup₁ ((RingedSpace.moduleCohomology X.toRingedSpace p).map φ a)
        ((RingedSpace.moduleCohomology X.toRingedSpace q).map ψ b) := by
  sorry

/-- Pullback carries the sheaf cup product to the product of pulled-back classes,
using the canonical tensor-pullback comparison on the coefficient sheaves.
Source: Stacks Project, Tags 01FD, 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: on each refined intersection pullback of a tensor is the tensor of pullbacks;
the total sign depends only on the degrees (Step 4). For acyclic Godement models this
commutes with the derived cup map mu and with the map to the ordinary tensor.
Apply the cohomology comparisons of Step 3 and the pullback comparison of Step 1.
The tensor coefficient comparison is lem-weil-pbc-module-pullback-tensor, normalized
on section tensors, so its cohomology map gives precisely the displayed equality. -/
theorem moduleCup_pullback_naturality (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
        (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
          (@id X.Modules (F ⊗ G)))
    (hc : IsModuleCupProduct F G p q cup)
    (cup' : (RingedSpace.moduleCohomology X'.toRingedSpace p).obj
        ((tensorPullback f).obj F) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace q).obj
        ((tensorPullback f).obj G) →ₗ[Γ(X', ⊤)]
      (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).obj
        (@id X'.Modules ((tensorPullback f).obj F ⊗ (tensorPullback f).obj G)))
    (hc' : IsModuleCupProduct ((tensorPullback f).obj F) ((tensorPullback f).obj G)
      p q cup') :
    ∀ a b, (RingedSpace.moduleCohomology X'.toRingedSpace (p + q)).map
        ((Classical.choose (module_pullback_tensor f)) F G).hom
        (moduleCohomologyPullback f (@id X.Modules (F ⊗ G)) (p + q) (cup a b)) =
      cup' (moduleCohomologyPullback f F p a) (moduleCohomologyPullback f G q b) := by
  sorry

/-- Refinement of Cech cochains is natural in the coefficient module.
Source: Stacks Project, Tag 01FD
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: on each tuple, the tensor-pullback unit is natural in the module map, and
module morphisms commute with restriction. Apply these two identities to the tuple
formula defining gamma (Steps 1 and 4). The equality holds in every degree, hence
also after taking cohomology and the comparison maps of Step 1. -/
theorem cechRefinement_coefficient_naturality (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F F₁ : X.Modules) [F.IsQuasicoherent] [F₁.IsQuasicoherent] (φ : F ⟶ F₁)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (gamma₁ : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F₁.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F₁).presheafModuleCat))
    (hgamma₁ : IsCechRefinementMap f U U' refine hrefine F₁ gamma₁) :
    ∀ (n : ℕ) (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n),
      gamma₁.f n (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            φ.val)).f n a) =
        ((cechComplexFunctor U').map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((tensorPullback f).map φ).val)).f n (gamma.f n a) := by
  intro n a
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U'
    ((tensorPullback f).obj F₁).presheafModuleCat n).injective
  funext y
  rw [hgamma₁, cech_coefficient_apply, cech_coefficient_apply, hgamma]
  have hu := (Classical.choose (exists_tensorPullbackAdjunction f)).unit_naturality φ
  have hs := congrArg (fun k ↦ k.val.app (op (⨅ j, U (refine (y j))))
    (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
      (refine ∘ y))) hu
  have hn := Hom.app_presheaf_map ((tensorPullback f).map φ)
    (cechRefinementIntersection f U U' refine hrefine n y)
    ((((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).val.app
      (op (⨅ j, U (refine (y j)))))
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
        (refine ∘ y)))
  exact (congrArg (((tensorPullback f).obj F₁).presheaf.map
    (cechRefinementIntersection f U U' refine hrefine n y).op) hs.symm).trans hn.symm

set_option maxHeartbeats 800000 in
-- The three homology transports require additional elaboration steps.
/-- The Cech cup product is natural in both coefficient sheaves.
Source: Stacks Project, Tags 07MB and 0FKV
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: the two coefficient maps commute with restriction and send a tensor of two
sections to the tensor of their images. Apply this on each intersection to the
front/back cup formula of Step 2. This gives the equality on cocycles and therefore
on their classes. Combining with comparison-map naturality in Step 3 proves that
the cup comparison square is natural, as asserted by Step 4. -/
theorem cechCup_coefficient_naturality (X : Scheme.{v}) {ι : Type v} (U : ι → X.Opens)
    (F G F₁ G₁ : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    [F₁.IsQuasicoherent] [G₁.IsQuasicoherent] (φ : F ⟶ F₁) (ψ : G ⟶ G₁) (p q : ℕ)
    (cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q))
    (hc : IsCechCupProduct U F G p q cup)
    (cup₁ : ((cechComplexFunctor U).obj F₁.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G₁.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F₁ ⊗ G₁).presheafModuleCat).homology (p + q))
    (hc₁ : IsCechCupProduct U F₁ G₁ p q cup₁) :
    ∀ a b, HomologicalComplex.homologyMap ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (φ ⊗ₘ ψ).val)) (p + q) (cup a b) =
      cup₁ (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            φ.val)) p a)
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ψ.val)) q b) := by
  intro a b
  obtain ⟨a, rfl⟩ := cycle_class_surjective
    ((cechComplexFunctor U).obj F.presheafModuleCat) p a
  obtain ⟨b, rfl⟩ := cycle_class_surjective
    ((cechComplexFunctor U).obj G.presheafModuleCat) q b
  let φC := (cechComplexFunctor U).map
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map φ.val)
  let ψC := (cechComplexFunctor U).map
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map ψ.val)
  let τC := (cechComplexFunctor U).map
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
      (φ ⊗ₘ ψ).val)
  rw [hc a b (cup_cycle U F G p q a b) rfl]
  erw [map_cycle_class, map_cycle_class, map_cycle_class]
  apply (hc₁ (map_cycle φC p a) (map_cycle ψC q b)
    (map_cycle τC (p + q) (cup_cycle U F G p q a b)) ?_).symm
  rw [map_cycle_val, map_cycle_val, map_cycle_val]
  exact cup_coefficient_cochain U φ ψ p q a.val b.val


/-- Successive specified refinements compose after the canonical coefficient identification.
The last two equalities give the composite comparison square and functoriality of the
usual cohomology pullback, respectively.
Source: Stacks Project, Tag 01FD; Step 4 of the node's proof
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: on a tuple of indices, successive restrictions compose and pullback of sections
through the two adjunction units is pullback through their composite unit. The existing
unit-normalized tensorSectionsComp identifies this unit with the unit for f₁ ≫ f.
Thus the degree maps agree for the composite index function, giving the cochain equality.
Apply homology and its canonical forgetful comparisons, then the Tag 01FD comparison
square, to obtain the second equality. Finally, compose the two resolution diagrams
for the units defining moduleCohomologyPullback. Under tensorSectionsComp the composite
unit is the unit for f₁ ≫ f; resolution independence yields the third equality. This
argument uses no comparison isomorphism and applies to every open covering. -/
theorem cechRefinement_composition_naturality
    (X X' X'' : Scheme.{v}) (f : X' ⟶ X) (f₁ : X'' ⟶ X')
    {ι ι' ι'' : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (U' : ι' → X'.Opens) (hU' : iSup U' = ⊤)
    (U'' : ι'' → X''.Opens) (hU'' : iSup U'' = ⊤)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (refine₁ : ι'' → ι') (hrefine₁ : ∀ i, U'' i ≤ f₁ ⁻¹ᵁ U' (refine₁ i))
    (hrefineComp : ∀ i, U'' i ≤ (f₁ ≫ f) ⁻¹ᵁ U ((refine ∘ refine₁) i))
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj
          (F).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U').obj
          ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (gamma₁ : ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U').obj
          ((tensorPullback f).obj F).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X'', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U'').obj
          ((tensorPullback f₁).obj ((tensorPullback f).obj F)).presheafModuleCat))
    (hgamma₁ : IsCechRefinementMap f₁ U' U'' refine₁ hrefine₁ ((tensorPullback f).obj F) gamma₁)
    (gammaComp : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj
          (F).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X'', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U'').obj
          ((tensorPullback (f₁ ≫ f)).obj F).presheafModuleCat))
    (hgammaComp : IsCechRefinementMap (f₁ ≫ f) U U'' (refine ∘ refine₁) hrefineComp F gammaComp)
    (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
    (hc : IsModuleCechComparison U F p c)
    (cComp : ((cechComplexFunctor U'').obj
        ((tensorPullback (f₁ ≫ f)).obj F).presheafModuleCat).homology p ⟶
      (RingedSpace.moduleCohomology X''.toRingedSpace p).obj
        ((tensorPullback (f₁ ≫ f)).obj F))
    (hcComp : IsModuleCechComparison U'' ((tensorPullback (f₁ ≫ f)).obj F) p cComp) :
    (gamma ≫ gamma₁ ≫
      ((forget₂ (ModuleCat.{v} Γ(X'', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
          ((cechComplexFunctor U'').map
            ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
              ((tensorSectionsComp f₁ f).hom.app F).val)) = gammaComp) ∧
    (cechRefinementHomology gamma p ≫ cechRefinementHomology gamma₁ p ≫
      (forget₂ _ AddCommGrpCat).map
        (HomologicalComplex.homologyMap ((cechComplexFunctor U'').map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((tensorSectionsComp f₁ f).hom.app F).val)) p) ≫
      (forget₂ _ AddCommGrpCat).map cComp =
        (forget₂ _ AddCommGrpCat).map c ≫ moduleCohomologyPullback (f₁ ≫ f) F p) ∧
    (moduleCohomologyPullback f F p ≫
      moduleCohomologyPullback f₁ ((tensorPullback f).obj F) p ≫
      (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.moduleCohomology X''.toRingedSpace p).map
          ((tensorSectionsComp f₁ f).hom.app F)) =
      moduleCohomologyPullback (f₁ ≫ f) F p) := by
  sorry

set_option maxHeartbeats 800000 in
-- The tuplewise tensor-pullback calculation needs additional elaboration steps.
/-- The specified refinement carries the Cech cup cochain to the cup of the refined
cochains, after the canonical tensor-pullback coefficient identification.
Source: Stacks Project, Tags 01FD and 07MB; Step 4 of the node's proof
(blueprint: lem-sc-picard-cech-cup-pullback-compat).
Proof: evaluate on a tuple of refined indices. The front and back tuples commute
with the specified index function. Pullback of sections commutes with restriction,
and the section-normalized module_pullback_tensor sends the pullback of a tensor
to the tensor of the pullbacks. These identities identify each tuple component of
the two sides. The product projections then give the cochain equality. Together
with Leibniz this descends to cohomology and makes the cup comparison square
natural under refinement and pullback, without any comparison isomorphism. -/
theorem cechCup_refinement_naturality (X X' : Scheme.{v}) (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (p q : ℕ)
    (gammaF : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgammaF : IsCechRefinementMap f U U' refine hrefine F gammaF)
    (gammaG : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj G.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj G).presheafModuleCat))
    (hgammaG : IsCechRefinementMap f U U' refine hrefine G gammaG)
    (gammaFG : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj (F ⊗ G)).presheafModuleCat))
    (hgammaFG : IsCechRefinementMap f U U' refine hrefine (F ⊗ G) gammaFG)
    : ∀ (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
      (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q),
      (((cechComplexFunctor U').map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (((Classical.choose (module_pullback_tensor f)) F G).hom).val)).f (p + q))
        (gammaFG.f (p + q) (cechCupCochain U F G p q a b)) =
      cechCupCochain U' ((tensorPullback f).obj F) ((tensorPullback f).obj G) p q
        (gammaF.f p a) (gammaG.f q b) := by
  intro a b
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U'
    (((tensorPullback f).obj F) ⊗ ((tensorPullback f).obj G)).presheafModuleCat
    (p + q)).injective
  funext y
  rw [cech_coefficient_apply, hgammaFG]
  unfold cechCupCochain
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hn := Hom.app_presheaf_map
    (((Classical.choose (module_pullback_tensor f)) F G).hom)
    (cechRefinementIntersection f U U' refine hrefine (p + q) y)
    (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (F ⊗ G)).app
      (⨅ j, U (refine (y j)))
      (tmulSection
        (F.presheaf.map (cupFaceRestriction U (refine ∘ y) (cupFront p q)).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat p a
            ((refine ∘ y) ∘ cupFront p q)))
        (G.presheaf.map (cupFaceRestriction U (refine ∘ y) (cupBack p q)).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U G.presheafModuleCat q b
            ((refine ∘ y) ∘ cupBack p q)))))
  erw [hn, (Classical.choose_spec (module_pullback_tensor f)).2,
    tmulSection_map]
  rw [hgammaF, hgammaG]
  congr 1
  · exact refinement_face_apply f U U' refine hrefine F (p + q) p y (cupFront p q) _
  · exact refinement_face_apply f U U' refine hrefine G (p + q) q y (cupBack p q) _


end
end AlgebraicGeometry.Scheme.Modules
