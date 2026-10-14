/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.CechComplexAugmentations
public import Sheaf.Paper.CechRefinementCochainMap

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
            (ComplexShape.up ℕ) r q n h) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
