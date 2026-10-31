/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteTensorOrdinaryComparison
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-! # Ordinary finite restriction square on prescribed signed total complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

namespace PinnedRestriction

private theorem total_map
    {X : Scheme.{u}} {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {P P' Q Q' : CochainComplex (Mod R) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (total R).map (Prod.mkHom a b) =
      HomologicalComplex.mapBifunctorMap a b (tensor R) (.up ℤ) := by
  simp only [total, Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

private theorem pinned_summand
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (s : FiniteTensorTotal e) (hs : finiteTensorPure e s)
    (P Q : CochainComplex (FiniteModules A X) ℤ) (p q n : ℤ) (hn : p + q = n)
    (c : e.equivalence.functor.obj (P.X p ⊗ Q.X q) ⟶
      ((tensor R).obj (e.equivalence.functor.obj (P.X p))).obj
        (e.equivalence.functor.obj (Q.X q)))
    (hc : ∀ W x y, c.val.app W
      ((e.underlying.inv.app (P.X p ⊗ Q.X q)).hom.app W
        (finitePure (P.X p) (Q.X q) W x y)) =
      pure R _ _ W ((e.underlying.inv.app (P.X p)).hom.app W x)
        ((e.underlying.inv.app (Q.X q)).hom.app W y)) :
    e.equivalence.functor.map
        (HomologicalComplex.ιMapBifunctor P Q (curriedTensor (FiniteModules A X))
          (.up ℤ) p q n hn) ≫ (s P Q).hom.f n =
      c ≫ HomologicalComplex.ιMapBifunctor ((finiteComplexRealization e).obj P)
        ((finiteComplexRealization e).obj Q) (tensor R) (.up ℤ) p q n hn := by
  apply TensorOrdinary.realized_tensor_ext_any e (P.X p) (Q.X q)
  intro W x y
  change ((s P Q).hom.f n).val.app W
      ((e.equivalence.functor.map _).val.app W
        ((TensorOrdinary.sections e _ W).symm (finitePure _ _ W x y))) = _
  rw [TensorOrdinary.sections_inv_map]
  erw [hs P Q p q n hn W x y]
  change _ = (HomologicalComplex.ιMapBifunctor ((finiteComplexRealization e).obj P)
    ((finiteComplexRealization e).obj Q) (tensor R) (.up ℤ)
    p q n hn).val.app W (c.val.app W _)
  exact congrArg
    ((HomologicalComplex.ιMapBifunctor ((finiteComplexRealization e).obj P)
      ((finiteComplexRealization e).obj Q) (tensor R) (.up ℤ) p q n hn).val.app W)
    (hc W x y).symm

private theorem upperStar_pure
    (A : Type (u + 1)) [CommRing A] [Finite A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M N : FiniteModules A X)
    (W : U.ProEtᵒᵖ)
    (x : ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj M).obj.obj W)
    (y : ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N).obj.obj W) :
    ((ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app
        (M ⊗ N)).hom.app W
      ((Functor.LaxMonoidal.μ (ProEtale.upperStar (ModuleCat.{u + 1} A) j) M N).hom.app W
        (finitePure _ _ W x y)) =
    finitePure M N ((openInclusion .ordinary j).op.obj W)
      (((ProEtale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} A) j).hom.app M).hom.app W x)
      (((ProEtale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} A) j).hom.app N).hom.app W y) := by
  let B := ModuleCat.{u + 1} A
  let H := Functor.sheafPushforwardContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j))
    B (ProEt.topology U) (ProEt.topology X)
  let a := ProEtale.upperStarIsoSheafPushforward B j (inferInstance : WeaklyEtale j)
  have ht := NatTrans.IsMonoidal.tensor (τ := a.hom) M N
  have h := congrArg (fun z ↦ z.hom.app W (finitePure _ _ W x y)) ht
  change _ = (Functor.LaxMonoidal.μ H M N).hom.app W
    ((a.hom.app M ⊗ₘ a.hom.app N).hom.app W (finitePure _ _ W x y)) at h
  rw [TensorOrdinary.fixed_pure_map] at h
  refine h.trans ?_
  exact congrArg (fun z ↦ z
    (((a.hom.app M).hom.app W x) ⊗ₜ[A] ((a.hom.app N).hom.app W y)))
      (Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)) B
        (ProEt.topology U) (ProEt.topology X) M N W)

end PinnedRestriction

set_option maxHeartbeats 2000000 in
-- Elaborating the prescribed realization and operation records needs a larger budget.
/-- The ordinary signed-total square for the pinned finite realization.
Source: Stacks 03EK and 06YN; step 2 of
lem-sf-finite-tensor-restriction-coherence.

Proof: test in degree n on every signed-total summand indexed by p+q=n.
Use the finite tensor pins to identify the pure generators with ring-sheaf
pure generators. The native open tensor comparison preserves the restricted
pure generators, and the open pin identifies their sections. The restriction
tensor comparison has precisely the same pure-section formula. Bilinearity,
sheafification and the direct-sum universal property prove equality in degree n.
All these are chain maps with the same signed-total differential.
(blueprint: lem-sf-finite-restriction-pinned-total-square) -/
theorem finite_restriction_pinned_total_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) :
    let R := (finiteInput A gU j' j g sq).R
    letI : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
    let fc := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)
    let h := (restrict .ordinary j R).mapHomologicalComplex (.up ℤ)
    let v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)
    ∀ P Q : CochainComplex (FiniteModules A X) ℤ,
      (finiteComplexRealization e.realizeU).map
          (inv (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
            (ProEtale.upperStar (ModuleCat.{u + 1} A) j)).app P).app Q)) ≫
        v.app (finiteTotal A X P Q) ≫
        h.map (e.tensorX_pin.totalIso P Q).hom =
      (e.tensorU_pin.totalIso (fc.obj P) (fc.obj Q)).hom ≫
        (total (restrictRing .ordinary j R)).map
          (Prod.mkHom (v.app P) (v.app Q)) ≫
        totalMap o.tensorX o.tensorU (restrict .ordinary j R) o.restrictionTensor
          o.tensorComparison.comm ((finiteComplexRealization e.realizeX).obj P)
            ((finiteComplexRealization e.realizeX).obj Q) := by
  dsimp only
  intro P Q
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
    (finiteInput A gU j' j g sq).R
  let S := restrictRing .ordinary j R
  let F := ProEtale.upperStar (ModuleCat.{u + 1} A) j
  let L := restrict .ordinary j R
  let EU := e.realizeU.equivalence.functor
  let EX := e.realizeX.equivalence.functor
  let : L.Additive := (restriction_exact .ordinary j R).1
  let fc := F.mapHomologicalComplex (.up ℤ)
  let v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)
  choose cX hcX using TensorOrdinary.front_exists e.realizeX
  choose cU hcU using TensorOrdinary.front_exists e.realizeU
  have hstar (M : FiniteModules A X) (W : U.ProEtᵒᵖ)
      (x : (F.obj M).obj.obj W) :
      (e.open_pin.star.hom.app M).val.app W
          ((TensorOrdinary.sections e.realizeU (F.obj M) W).symm x) =
        (TensorOrdinary.sections e.realizeX M
          ((openInclusion .ordinary j).op.obj W)).symm
          (((ProEtale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} A) j).hom.app M).hom.app W x) := by
    apply (TensorOrdinary.sections e.realizeX M
      ((openInclusion .ordinary j).op.obj W)).injective
    change (e.realizeX.underlying.hom.app M).hom.app _
      ((e.open_pin.star.hom.app M).val.app W _) = _
    rw [e.open_pin.sections]
    change ((ProEtale.upperStarIsoOpenImmersionRestriction
      (ModuleCat.{u + 1} A) j).hom.app M).hom.app W
        ((TensorOrdinary.sections e.realizeU (F.obj M) W)
          ((TensorOrdinary.sections e.realizeU (F.obj M) W).symm x)) =
      (TensorOrdinary.sections e.realizeX M _)
        ((TensorOrdinary.sections e.realizeX M _).symm _)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hmu (M N : Mod R) (W : U.ProEtᵒᵖ)
      (x : M.val.obj ((openInclusion .ordinary j).op.obj W))
      (y : N.val.obj ((openInclusion .ordinary j).op.obj W)) :
      (o.restrictionTensor M N).inv.val.app W
          (pure S (L.obj M) (L.obj N) W x y) =
        pure R M N ((openInclusion .ordinary j).op.obj W) x y := by
    rw [← o.restrictionTensor_sections M N W x y]
    exact congrArg (fun f ↦ f.val.app W
      (pure R M N ((openInclusion .ordinary j).op.obj W) x y))
      (o.restrictionTensor M N).hom_inv_id
  have hord (M N : FiniteModules A X) :
      EU.map (Functor.LaxMonoidal.μ F M N) ≫ e.open_pin.star.hom.app (M ⊗ N) ≫
          L.map (cX M N) =
        cU (F.obj M) (F.obj N) ≫
          (Functor.uncurry.obj (tensor S)).map
            (Prod.mkHom (e.open_pin.star.hom.app M) (e.open_pin.star.hom.app N)) ≫
          (o.restrictionTensor (EX.obj M) (EX.obj N)).inv := by
    apply TensorOrdinary.realized_tensor_ext_any e.realizeU (F.obj M) (F.obj N)
    intro W x y
    change (L.map (cX M N)).val.app W
        ((e.open_pin.star.hom.app (M ⊗ N)).val.app W
          ((EU.map (Functor.LaxMonoidal.μ F M N)).val.app W
            ((TensorOrdinary.sections e.realizeU _ W).symm (finitePure _ _ W x y)))) = _
    rw [TensorOrdinary.sections_inv_map, hstar, PinnedRestriction.upperStar_pure]
    change (cX M N).val.app ((openInclusion .ordinary j).op.obj W) _ =
      (o.restrictionTensor _ _).inv.val.app W
        (((Functor.uncurry.obj (tensor S)).map
          (Prod.mkHom (e.open_pin.star.hom.app M) (e.open_pin.star.hom.app N))).val.app W
          ((cU (F.obj M) (F.obj N)).val.app W _))
    rw [hcX, hcU]
    change _ = (o.restrictionTensor _ _).inv.val.app W
      (((e.open_pin.star.hom.app M) ⊗ₘ (e.open_pin.star.hom.app N)).val.app W
        (CochainScalarConstruction.pure S _ _ W _ _))
    erw [CochainScalarConstruction.pure_map S]
    erw [hstar, hstar]
    exact (hmu (EX.obj M) (EX.obj N) W _ _).symm
  apply HomologicalComplex.hom_ext
  intro n
  simp only [finiteComplexRealization, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map EU
  intro p q hn
  have hinv :
      inv (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
        (F.mapCochainComplexμIso P Q).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← Functor.mapCochainComplexμIso_inv F P Q, Iso.inv_hom_id]
  have hnative := Functor.ιTensorObj_mapCochainComplexμIso_hom_f F P Q p q n hn
  rw [← hinv] at hnative
  have hX := PinnedRestriction.pinned_summand e.realizeX e.tensorX_pin.totalIso
    e.tensorX_pin.pure_summands P Q p q n hn (cX _ _) (hcX _ _)
  have hU := PinnedRestriction.pinned_summand e.realizeU e.tensorU_pin.totalIso
    e.tensorU_pin.pure_summands (fc.obj P) (fc.obj Q) p q n hn (cU _ _) (hcU _ _)
  have hnat := e.open_pin.star.hom.naturality
    (HomologicalComplex.ιMapBifunctor P Q (curriedTensor (FiniteModules A X))
      (.up ℤ) p q n hn)
  dsimp only [Functor.comp_map] at hnat
  have hmap :
      HomologicalComplex.ιMapBifunctor ((finiteComplexRealization e.realizeU).obj (fc.obj P))
          ((finiteComplexRealization e.realizeU).obj (fc.obj Q)) (tensor S)
          (.up ℤ) p q n hn ≫
        ((total S).map (Prod.mkHom (v.app P) (v.app Q))).f n =
      (Functor.uncurry.obj (tensor S)).map
          (Prod.mkHom (e.open_pin.star.hom.app (P.X p))
            (e.open_pin.star.hom.app (Q.X q))) ≫
        HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj
          ((finiteComplexRealization e.realizeX).obj P))
          ((L.mapHomologicalComplex (.up ℤ)).obj
            ((finiteComplexRealization e.realizeX).obj Q))
          (tensor S) (.up ℤ) p q n hn := by
    erw [PinnedRestriction.total_map, HomologicalComplex.ι_mapBifunctorMap]
    simp only [Functor.uncurry_obj_map, Category.assoc]
    rfl
  have hchain :
      HomologicalComplex.ιMapBifunctor
          ((L.mapHomologicalComplex (.up ℤ)).obj ((finiteComplexRealization e.realizeX).obj P))
          ((L.mapHomologicalComplex (.up ℤ)).obj ((finiteComplexRealization e.realizeX).obj Q))
          (tensor S) (.up ℤ) p q n hn ≫
        (totalMap o.tensorX o.tensorU L o.restrictionTensor o.tensorComparison.comm
          ((finiteComplexRealization e.realizeX).obj P)
          ((finiteComplexRealization e.realizeX).obj Q)).f n =
      (o.restrictionTensor (EX.obj (P.X p)) (EX.obj (Q.X q))).inv ≫
        L.map (HomologicalComplex.ιMapBifunctor
          ((finiteComplexRealization e.realizeX).obj P)
          ((finiteComplexRealization e.realizeX).obj Q) (tensor R) (.up ℤ) p q n hn) := by
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.monoidalCategory S
    let := o.tensorX.preadditive
    let := o.tensorU.preadditive
    simp only [totalMap, totalComponent, tensorPullbackTotalComponent,
      HomologicalComplex.ι_mapBifunctorDesc]
    rfl
  erw [← EU.map_comp_assoc, hnative, EU.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hnat]
  erw [← L.map_comp, hX, L.map_comp]
  erw [reassoc_of% hU, reassoc_of% hmap, hchain]
  erw [reassoc_of% (hord (P.X p) (Q.X q))]
  rfl

end SheafOfModules.OpenTensorNormalization
