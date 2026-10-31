/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicDataFromFinite
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicRationalProperties
import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicAlgebraicProperties

/-! # Adic reconstruction from finite Galois modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor
  Padic Padic.coefficientExtensionIntegers Representation.IsContinuousIntegral
  Representation.IsContinuousCoefficient Representation.IsLAdic
  IsLisseIntegralDiagram galoisUnderlyingSetSheaf


private theorem moduleIso_cast_cancel
    {R : Type (u + 1)} [Ring R] {M N P : ModuleCat.{u + 1} R}
    (e : M ≅ N) (h : N = P) (z : M) :
    e.inv (eqToHom h.symm (eqToHom h (e.hom z))) = z := by
  cases h
  exact ModuleCat.inv_hom_apply e z

section ConstructionConsequences

variable {Y : Scheme.{u}} [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (c : GaloisLisseFiniteCorrespondence y G)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  (d : GaloisLisseAdicData y G c l Q)

set_option maxHeartbeats 8000000 in
-- The normalized stalk and tensor comparisons have large dependent module types.
private theorem integralEvaluation_from_construction
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisIntegralEvaluationAction y G c l Q d := by
  unfold galoisIntegralEvaluationAction
  intro E F n
  have hi := GaloisAdicCanonicalConstruction.inverseLimit
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  rcases hi with ⟨V, hV⟩
  rcases hV with ⟨α, hα⟩
  rcases hα with ⟨C, hC⟩
  rcases hC with ⟨e, _, hp, hfinite⟩
  have hf := hfinite n
  rcases hf with ⟨h, hκ⟩
  rcases hκ with ⟨κ, hgerm, haction⟩
  refine ⟨h, κ, hgerm, ?_⟩
  intro g z
  have hproj (w : ((d.eI E).functor.obj F).obj.V) :
      (α.hom.app (op n)) ((e.inv ≫ C.π.app (op n)).hom w) =
        limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
          ((d.τI E).hom.app F w) := by
    exact congrArg (fun f ↦ f w) (hp n)
  calc
    _ = κ ((α.hom.app (op n))
        ((e.inv ≫ C.π.app (op n)).hom (((d.eI E).functor.obj F).obj.ρ g z))) :=
      congrArg κ (hproj _).symm
    _ = κ ((α.hom.app (op n))
        ((V.obj (op n)).ρ g ((e.inv ≫ C.π.app (op n)).hom z))) :=
      congrArg (fun w ↦ κ ((α.hom.app (op n)) w))
        (Rep.hom_comm_apply (e.inv ≫ C.π.app (op n)) g z)
    _ = _ := haction g _
    _ = _ := congrArg (fun w ↦ (c.γ g).hom.app
      (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
        (F.obj.obj (op n)) h) (κ w)) (hproj z)

set_option maxHeartbeats 8000000 in
-- The normalized stalk and tensor comparisons have large dependent module types.
private theorem rationalEvaluation_from_construction
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisRationalEvaluationAction y G c l Q d := by
  unfold galoisRationalEvaluationAction
  intro E F g a z
  have hr := GaloisAdicCanonicalConstruction.localization
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  rcases hr with ⟨η, haction, hnormal⟩
  have hpre : (d.τR E).inv.app F
      (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F).symm
        (TensorProduct.tmul _ a ((d.τI E).hom.app F.integral z))) =
      η (TensorProduct.tmul _ a z) := by
    have hh := congrArg (fun w ↦ (d.τR E).inv.app F
      (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F).symm w))
        (hnormal a z)
    exact hh.symm.trans (moduleIso_cast_cancel ((d.τR E).app F)
      (lisseRationalFiberFunctor_obj l E.val Y y F) (η (TensorProduct.tmul _ a z)))
  let T := fun w : ((d.eR E).functor.obj F).obj.V ↦
    eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F) ((d.τR E).hom.app F w)
  calc
    _ = T (((d.eR E).functor.obj F).obj.ρ g (η (TensorProduct.tmul _ a z))) :=
      congrArg (fun w ↦ T (((d.eR E).functor.obj F).obj.ρ g w)) hpre
    _ = T (η (TensorProduct.tmul _ a
        (((d.eI E).functor.obj F.integral).obj.ρ g z))) :=
      congrArg T (haction g a z).symm
    _ = _ := hnormal a _

set_option maxHeartbeats 8000000 in
-- The normalized stalk and tensor comparisons have large dependent module types.
private theorem algebraicModel_from_construction
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisAlgebraicModelScalarExtension y G c l Q d := by
  unfold galoisAlgebraicModelScalarExtension
  intro E F
  have ha := GaloisAdicCanonicalConstruction.colimit
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  rcases ha with ⟨η, haction, hnormal⟩
  refine ⟨η, ?_, hnormal⟩
  intro g z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
      change η (TensorProduct.tmul _ a (((d.eR E).functor.obj F).obj.ρ g z)) = _
      exact haction g a z
  | add z w hz hw => simp only [map_add, hz, hw]

end ConstructionConsequences

/-- Reconstruct the adic correspondence from the normalized finite correspondence.
Source: Deligne, Weil II (1.1.1), (1.1.6); Stanford Weil II seminar L19,
Proposition 1.1.9; proof steps 6--10 of `cor-galois-lisse-representations`.
(blueprint: new-e4-galois-adic-from-finite).

Proof: `galois_adic_data_from_finite` constructs adic data `d` with the supplied `P` and
`δ`, together with its normalized construction comparisons `hcanon`
(`GaloisAdicCanonicalConstruction`). Integral evaluation follows from `hcanon.inverseLimit`:
each normalized limit projection is a cone projection followed by the stalk isomorphism;
cone projections are representation morphisms, and the finite stalk action is `c.γ`.
Rational evaluation follows from `hcanon.localization`: the transported pure tensor is the
value of the equivariant rationalization isomorphism, whose fibre formula is normalized.
The algebraic model scalar comparison is `hcanon.colimit`, extended from pure tensors by
tensor induction. All equivalences preserve finite limits and colimits. The abelian,
monoidal, tensor, unit and coefficient-extension clauses are
`galois_adic_rational_properties` and `galois_adic_algebraic_properties` applied to
`hcanon`; assemble the structure `GaloisLisseAdicCorrespondence` from these clauses. -/
theorem galois_adic_from_finite
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] :
    ∃ a : GaloisLisseAdicCorrespondence y G c l Q, a.P = P ∧ HEq a.δ δ := by
  classical
  obtain ⟨d, hdP, hdδ, hcanon⟩ :=
    galois_adic_data_from_finite y G c P δ l Q
  obtain ⟨hRS, hRR, hIM, hRM, hIT, hIU, hRT, hRU⟩ :=
    galois_adic_rational_properties y G c l Q d hcanon
  obtain ⟨hAS, hAR, hAM, hAT, hAU, hIS, hRSX⟩ :=
    galois_adic_algebraic_properties y G c l Q d hcanon
  have hRL : galoisRationalFiniteLimits y G c l Q d := fun _ ↦ inferInstance
  have hRC : galoisRationalFiniteColimits y G c l Q d := fun _ ↦ inferInstance
  have hAL : galoisAlgebraicFiniteLimits y G c l Q d := by
    unfold galoisAlgebraicFiniteLimits
    infer_instance
  have hAC : galoisAlgebraicFiniteColimits y G c l Q d := by
    unfold galoisAlgebraicFiniteColimits
    infer_instance
  have hIE := integralEvaluation_from_construction y G c l Q d hcanon
  have hRE := rationalEvaluation_from_construction y G c l Q d hcanon
  have hMS := algebraicModel_from_construction y G c l Q d hcanon
  let a : GaloisLisseAdicCorrespondence y G c l Q :=
    { toGaloisLisseAdicData := d
      rationalSheavesAbelian := hRS
      rationalRepresentationsAbelian := hRR
      rationalFiniteLimits := hRL
      rationalFiniteColimits := hRC
      algebraicSheavesAbelian := hAS
      algebraicRepresentationsAbelian := hAR
      algebraicFiniteLimits := hAL
      algebraicFiniteColimits := hAC
      integralEvaluationAction := hIE
      rationalEvaluationAction := hRE
      integralMonoidal := hIM
      rationalMonoidal := hRM
      algebraicMonoidal := hAM
      integralTensor := hIT
      integralUnit := hIU
      rationalTensor := hRT
      rationalUnit := hRU
      algebraicTensor := hAT
      algebraicUnit := hAU
      algebraicModelScalarExtension := hMS
      integralScalarExtension := hIS
      rationalScalarExtension := hRSX }
  exact ⟨a, hdP, hdδ⟩

end AlgebraicGeometry.Scheme
