/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.CechComplexAugmentations
public import Sheaf.Paper.CechRefinementCochainMap
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Tuple restriction on pushed-forward complexes

Source: Stacks Project, Tag 01FD, the map B-double-prime to A.
(blueprint: lem-sc-cech-pushforward-tuple-total)
-/

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Restrict a pushed-forward cochain to the refined tuples, forgetting scalars.
Source: Stacks 01FD (blueprint: lem-sc-cech-pushforward-tuple-total). -/
def cechPushforwardTupleMap {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (G : X'.Modules) (q : ℕ) :
    (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).obj
      (((cechComplexFunctor U).obj ((pushforward f).obj G).presheafModuleCat).X q) ⟶
    (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).obj
      (((cechComplexFunctor U').obj G.presheafModuleCat).X q) :=
  let c := TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat q
  AddCommGrpCat.ofHom <| c.symm.toAddMonoidHom.comp <|
    (AddMonoidHom.pi fun y ↦
      (G.presheaf.map (cechRefinementIntersection f U U' refine hrefine q y).op).hom.comp
        (Pi.evalAddMonoidHom _ (refine ∘ y))).comp
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
        ((pushforward f).obj G).presheafModuleCat q).toAddMonoidHom

/-- The tuple formula for the concrete refinement component.
Source: Stacks 01FD (blueprint: lem-sc-cech-pushforward-tuple-total). -/
theorem cechPushforwardTupleMap_apply {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (G : X'.Modules) (q : ℕ)
    (x : ((cechComplexFunctor U).obj ((pushforward f).obj G).presheafModuleCat).X q)
    (y : Fin (q + 1) → ι') :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat q
      (cechPushforwardTupleMap f U U' refine hrefine G q x) y =
    G.presheaf.map (cechRefinementIntersection f U U' refine hrefine q y).op
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U
        ((pushforward f).obj G).presheafModuleCat q x (refine ∘ y)) := by
  change (TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat q)
    ((TopCat.Presheaf.cechComplexFunctorXAddEquiv U' G.presheafModuleCat q).symm _) y = _
  rw [AddEquiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tupleCoeff_apply {X : Scheme.{v}} {ι : Type v}
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
  exact (PresheafOfModules.naturality_apply φ.val
    (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
    (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y a)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tupleMap_naturality {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    {G H : X'.Modules} (φ : G ⟶ H) (q : ℕ) :
    (forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).map
        (((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            ((pushforward f).map φ).val)).f q) ≫
      cechPushforwardTupleMap f U U' refine hrefine H q =
    cechPushforwardTupleMap f U U' refine hrefine G q ≫
      (forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).map
        (((cechComplexFunctor U').map
          ((PresheafOfModules.forgetToPresheafModuleCat
            (op ⊤) isTerminalTop.op).map φ.val)).f q) := by
  apply AddCommGrpCat.ext
  intro x
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U' H.presheafModuleCat q).injective
  funext y
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U' H.presheafModuleCat q
    (cechPushforwardTupleMap f U U' refine hrefine H q
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          ((pushforward f).map φ).val)).f q x)) y =
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U' H.presheafModuleCat q
      (((cechComplexFunctor U').map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          φ.val)).f q (cechPushforwardTupleMap f U U' refine hrefine G q x)) y
  rw [cechPushforwardTupleMap_apply, tupleCoeff_apply, tupleCoeff_apply,
    cechPushforwardTupleMap_apply]
  dsimp only [pushforward_map_app]
  exact (PresheafOfModules.naturality_apply φ.val
    (cechRefinementIntersection f U U' refine hrefine q y).op _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def tupleRowMap {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (G : X'.Modules) :
    ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj
        ((pushforward f).obj G).presheafModuleCat) ⟶
    ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj ((cechComplexFunctor U').obj G.presheafModuleCat) := by
  let P := ((pushforward f).obj G).presheafModuleCat ⋙ forget₂ _ AddCommGrpCat
  let Q := G.presheafModuleCat ⋙ forget₂ _ AddCommGrpCat
  let t (n : ℕ) : TopCat.Presheaf.CechCochain U P n →+
      TopCat.Presheaf.CechCochain U' Q n :=
    AddMonoidHom.pi fun y ↦
      (G.presheaf.map (cechRefinementIntersection f U U' refine hrefine n y).op).hom.comp
        (Pi.evalAddMonoidHom _ (refine ∘ y))
  have t_apply (n : ℕ) (a : TopCat.Presheaf.CechCochain U P n)
      (y : Fin (n + 1) → ι') : t n a y =
      G.presheaf.map (cechRefinementIntersection f U U' refine hrefine n y).op
        (a (refine ∘ y)) := rfl
  have ht (n : ℕ) (a : TopCat.Presheaf.CechCochain U P n) :
      ((TopCat.Presheaf.cechComplex U').obj Q).d n (n + 1) (t n a) =
        t (n + 1) (((TopCat.Presheaf.cechComplex U).obj P).d n (n + 1) a) := by
    funext y
    simp only [t_apply, TopCat.Presheaf.cechComplex_d_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    change G.presheaf.map _ (G.presheaf.map _ _) =
      G.presheaf.map _ (G.presheaf.map _ _)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← G.presheaf.map_comp, ← G.presheaf.map_comp]
    congr 2
  let γ : (TopCat.Presheaf.cechComplex U).obj P ⟶
      (TopCat.Presheaf.cechComplex U').obj Q :=
    { f := fun n ↦ AddCommGrpCat.ofHom (t n)
      comm' := by
        rintro n _ rfl
        exact AddCommGrpCat.ext (ht n) }
  exact (TopCat.Presheaf.cechComplexFunctorIso U
    ((pushforward f).obj G).presheafModuleCat).hom ≫ γ ≫
      (TopCat.Presheaf.cechComplexFunctorIso U' G.presheafModuleCat).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tupleRowMap_f {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (G : X'.Modules) (q : ℕ) :
    (tupleRowMap f U U' refine hrefine G).f q =
      cechPushforwardTupleMap f U U' refine hrefine G q := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- There is a unique cochain map of forgotten totals having the tuple-restriction
formula on every bidegree summand. No augmentations, resolutions or covers occur.
Source: Stacks 01FD, construction of B-double-prime to A.
(blueprint: lem-sc-cech-pushforward-tuple-total)

Proof: In bidegree (r,q), take the component at refine composed with the tuple and
restrict along the inclusion of the refined intersection in its inverse image.
The explicit additive maps are cechPushforwardTupleMap. Naturality of restriction
in the coefficient morphisms makes these maps commute with the r differential.
For the q differential, each omitted-vertex restriction commutes with the same
map, by functoriality of the presheaf and uniqueness of open inclusions. Summing
with the alternating signs gives commutation with the Cech differential. In each
total degree there are finitely many summands (r,q) with r+q=n. Forgetting scalars
preserves this finite coproduct. Use its universal property to assemble the degree
maps. The two differential identities prove they form a cochain map, since the
total differential is d_r + (-1)^r d_q. Uniqueness follows from the same coproduct
inclusions in every degree. This also covers empty tuple products and n=0. -/
theorem exists_unique_cechPushforward_tuple_total {X X' : Scheme.{v}} (f : X' ⟶ X)
    {ι ι' : Type v} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (K : CochainComplex X'.Modules ℕ) :
    let P := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
    let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
    let e' := forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}
    ∃! t : (e.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((moduleCechTotalFunctor U).obj P) ⟶
      (e'.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((moduleCechTotalFunctor U').obj K),
      ∀ (r q n : ℕ) (h : r + q = n),
        e.map (((moduleCechDoubleFunctor U).obj P).ιTotal
          (ComplexShape.up ℕ) r q n h) ≫ t.f n =
        cechPushforwardTupleMap f U U' refine hrefine (K.X r) q ≫
          e'.map (((moduleCechDoubleFunctor U').obj K).ιTotal
            (ComplexShape.up ℕ) r q n h) := by
  let P := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
  let e' := forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}
  let B := (moduleCechDoubleFunctor U).obj P
  let B' := (moduleCechDoubleFunctor U').obj K
  let ρ : (e.mapHomologicalComplex₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj B ⟶
      (e'.mapHomologicalComplex₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj B' :=
    { f := fun r ↦ tupleRowMap f U U' refine hrefine (K.X r)
      comm' := by
        intro r s h
        ext q : 1
        simpa only [HomologicalComplex.comp_f, tupleRowMap_f,
          Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_map_f,
          Functor.comp_map, moduleCechDoubleFunctor, B, B', P,
          SheafOfModules.forget_map] using
          (tupleMap_naturality f U U' refine hrefine (K.d r s) q).symm }
  let a := HomologicalComplex₂.mapTotalIso e B (ComplexShape.up ℕ)
  let b := HomologicalComplex₂.mapTotalIso e' B' (ComplexShape.up ℕ)
  let t := a.inv ≫ HomologicalComplex₂.total.map ρ (ComplexShape.up ℕ) ≫ b.hom
  refine ⟨t, ?_, ?_⟩
  · intro r q n h
    change e.map (B.ιTotal (ComplexShape.up ℕ) r q n h) ≫
      (HomologicalComplex₂.mapTotalXIso e B (ComplexShape.up ℕ) n).inv ≫
      (HomologicalComplex₂.total.map ρ (ComplexShape.up ℕ)).f n ≫
      (HomologicalComplex₂.mapTotalXIso e' B' (ComplexShape.up ℕ) n).hom = _
    rw [← Category.assoc, HomologicalComplex₂.map_ι_mapTotalXIso_inv,
      HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ι_mapTotalXIso_hom]
    rfl
  · intro s hs
    ext n : 1
    apply (cancel_epi (a.hom.f n)).mp
    apply HomologicalComplex₂.total.hom_ext
    intro r q h
    change _ ≫ (HomologicalComplex₂.mapTotalXIso e B (ComplexShape.up ℕ) n).hom ≫
      s.f n = _ ≫ (HomologicalComplex₂.mapTotalXIso e B (ComplexShape.up ℕ) n).hom ≫ t.f n
    rw [HomologicalComplex₂.ι_mapTotalXIso_hom_assoc,
      HomologicalComplex₂.ι_mapTotalXIso_hom_assoc, hs r q n h]
    change _ = e.map (B.ιTotal (ComplexShape.up ℕ) r q n h) ≫
      (HomologicalComplex₂.mapTotalXIso e B (ComplexShape.up ℕ) n).inv ≫
      (HomologicalComplex₂.total.map ρ (ComplexShape.up ℕ)).f n ≫
      (HomologicalComplex₂.mapTotalXIso e' B' (ComplexShape.up ℕ) n).hom
    rw [HomologicalComplex₂.map_ι_mapTotalXIso_inv_assoc,
      HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ι_mapTotalXIso_hom]
    rfl

end
end AlgebraicGeometry.Scheme.Modules
