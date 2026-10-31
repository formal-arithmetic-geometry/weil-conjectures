/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleWeilFundamentalRepresentation
import WeilConjectures.AlgebraicGeometry.GaloisLisseRepresentations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic

/-! # A degree-one fibre operator detects its descent isomorphism

Source: Weil II (1.1.6), (1.1.10), and the faithful fibre comparison of
`cor-galois-lisse-representations`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseAlgebraicFiber etaleAlgebraicPathIso
  lisseAlgebraicAutomorphismFiberIso lisseAlgebraicAutomorphismPullback

variable (l : ℕ) [Fact l.Prime] (Q : Type (u + 1)) [Field Q]
  [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  {Y : Scheme.{u}} [ConnectedSpace Y] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

private theorem algebraicFiber_faithful (t : Spec (.of Ω) ⟶ Y) :
    (lisseAlgebraicFiberFunctor l Y t Q).Faithful := by
  obtain ⟨P, act, hP⟩ := FiniteEtale.exists_isFundamentalGroup t
  let := act
  let := hP
  obtain ⟨c, hc⟩ := galois_lisse_representations t P
  obtain ⟨a⟩ := hc l Q
  exact Functor.Faithful.of_iso a.τA

/-- With the carrier fixed, one degree-one fibre operator determines the descent map.
Source: Weil II (1.1.6), (1.1.10), and cor-galois-lisse-representations.
(blueprint: lem-wf-etale-frobenius-injective).

Proof: the Galois correspondence identifies the algebraic fibre functor with the
composite of an equivalence, a full-subcategory inclusion and the faithful underlying
module functor on representations. Thus it is faithful. In the formula for Frobenius,
the factors before and after the image of the descent map are fixed isomorphisms.
Cancel them, apply faithfulness, and then use that an isomorphism is determined by its
forward arrow. This argument allows zero-rank sheaves as well. -/
theorem etaleWeilFrobenius_injective (h : Y ≅ Y) (t : Spec (.of Ω) ⟶ Y)
    (path : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ h.hom))
    (F : LisseAlgebraicSheaf l Y Q) :
    Function.Injective (fun theta : (lisseAlgebraicAutomorphismPullback h l Q).obj F ≅ F ↦
      (show Module.End Q (lisseAlgebraicFiber l Y Q t F) from
        (etaleWeilFrobenius l Q h t path
          (Endofunctor.IsoAlgebra.mk F theta)).toLinearMap)) := by
  let T := lisseAlgebraicFiberFunctor l Y t Q
  let : T.Faithful := algebraicFiber_faithful l Q t
  let pre := etaleAlgebraicPathIso l Q F path ≪≫
    (lisseAlgebraicAutomorphismFiberIso h l Q t F).symm ≪≫
    (eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q _)).symm
  let post := eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q F)
  intro theta psi he
  have hi : pre ≪≫ T.mapIso theta ≪≫ post = pre ≪≫ T.mapIso psi ≪≫ post := by
    apply Iso.ext
    apply ModuleCat.hom_ext
    simpa only [etaleWeilFrobenius, Endofunctor.IsoAlgebra.mk_carrier,
      Endofunctor.IsoAlgebra.mk_str, Iso.toLinearMap_toLinearEquiv,
      pre, post, T, Iso.trans_assoc] using he
  have hm : T.mapIso theta = T.mapIso psi := by
    have hh := congrArg (fun e ↦ pre.symm ≪≫ e ≪≫ post.symm) hi
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
      Iso.trans_refl] using hh
  apply Iso.ext
  exact T.map_injective (congrArg Iso.hom hm)

end AlgebraicGeometry.Scheme
