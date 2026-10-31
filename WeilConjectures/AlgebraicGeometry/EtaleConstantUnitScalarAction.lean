/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleConstantUnitFrobeniusOne
import WeilConjectures.AlgebraicGeometry.GaloisLisseRepresentations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic

/-! # Scalar action on the constant-unit descent comparison

Source: Weil II (1.1.1) c)-d), (1.1.6), and the constant-line construction in
`def-wf-constant-weil-twist`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseAlgebraicFiber etaleAlgebraicPathIso
  lisseAlgebraicAutomorphismFiberIso lisseAlgebraicAutomorphismPullback

private theorem scalarIsoLift
    {R : Type w} [CommRing R] {C : Type u} [Category C]
    {D : Type v} [Category D] [Preadditive D] [Linear R D]
    (E : C ⥤ D) [E.Full] [E.Faithful]
    (U : D ⥤ ModuleCat R) [U.Linear R]
    (T : C ⥤ ModuleCat R) (τ : E ⋙ U ≅ T)
    (b : Rˣ) {X Y : C} (theta : X ≅ Y) :
    ∃ theta' : X ≅ Y, T.map theta'.hom = (b : R) • T.map theta.hom := by
  let e : E.obj X ≅ E.obj Y :=
    { hom := (b : R) • E.map theta.hom
      inv := ((b⁻¹ : Rˣ) : R) • E.map theta.inv
      hom_inv_id := by simp [smul_smul]
      inv_hom_id := by simp [smul_smul] }
  let theta' := E.preimageIso e
  have hm : E.map theta'.hom = (b : R) • E.map theta.hom := by
    simp [theta', e]
  refine ⟨theta', ?_⟩
  apply (cancel_epi (τ.hom.app X)).1
  rw [← τ.hom.naturality theta'.hom]
  change U.map (E.map theta'.hom) ≫ τ.hom.app Y = _
  rw [hm, Functor.map_smul]
  simp only [Linear.smul_comp, Linear.comp_smul]
  exact congrArg (fun f ↦ (b : R) • f) (τ.hom.naturality theta.hom)



/-- Rescaling a constant-unit descent comparison scales its displayed fibre operator.
Source: Weil II (1.1.1) c)-d), (1.1.6), and
literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
`def-wf-constant-weil-twist.md`.
(blueprint: new-t2-etale-constant-unit-scalar-action).

Proof: the Galois correspondence identifies algebraic lisse sheaves with a full
subcategory of representations. Scale the image of the forward comparison by the
unit and the image of its inverse by the inverse unit, and lift the resulting
isomorphism by full faithfulness. Naturality of the fibre comparison shows that its
fibre map is scaled by the same unit. In the degree-one formula, composition with
the fixed path and pullback comparisons is linear, so the scalar factors out. -/
theorem etaleConstantUnit_scalar_action
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [ConnectedSpace Y] [IsNoetherian Y]
    [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (h : Y ≅ Y) (b : Qˣ)
    {κ : Type u} [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ Y)
    (path : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ h.hom))
    (theta₁ : (lisseAlgebraicAutomorphismPullback h l Q).obj
        (lisseAlgebraicUnit l Y Q) ≅ lisseAlgebraicUnit l Y Q) :
    ∃ theta : (lisseAlgebraicAutomorphismPullback h l Q).obj
        (lisseAlgebraicUnit l Y Q) ≅ lisseAlgebraicUnit l Y Q,
      (etaleWeilFrobenius l Q h t path
        (Endofunctor.IsoAlgebra.mk (lisseAlgebraicUnit l Y Q) theta)).toLinearMap =
        (b : Q) •
          (etaleWeilFrobenius l Q h t path
            (Endofunctor.IsoAlgebra.mk (lisseAlgebraicUnit l Y Q) theta₁)).toLinearMap := by
  obtain ⟨P, act, hP⟩ := FiniteEtale.exists_isFundamentalGroup t
  let := act
  let := hP
  obtain ⟨c, hc⟩ := galois_lisse_representations t P
  obtain ⟨a⟩ := hc l Q
  let E := a.eA.functor ⋙ ObjectProperty.ι _
  let U := forget₂ (Rep.{u + 1} Q P) (ModuleCat.{u + 1} Q)
  let T := lisseAlgebraicFiberFunctor l Y t Q
  obtain ⟨theta, ht⟩ := scalarIsoLift E U T a.τA b theta₁
  refine ⟨theta, ?_⟩
  let pre := etaleAlgebraicPathIso l Q (lisseAlgebraicUnit l Y Q) path ≪≫
    (lisseAlgebraicAutomorphismFiberIso h l Q t (lisseAlgebraicUnit l Y Q)).symm ≪≫
    (eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q _)).symm
  let post := eqToIso (lisseAlgebraicFiberFunctor_obj l Y t Q (lisseAlgebraicUnit l Y Q))
  have hi : (pre ≪≫ T.mapIso theta ≪≫ post).hom =
      (b : Q) • (pre ≪≫ T.mapIso theta₁ ≪≫ post).hom := by
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [ht]
    simp
  exact congrArg ModuleCat.Hom.hom hi

end AlgebraicGeometry.Scheme
