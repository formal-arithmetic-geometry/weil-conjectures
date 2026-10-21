/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.CommonStageLocallyFree
public import Sheaf.Paper.CommonStageWeilLinearDual
public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra

import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback
import Sheaf.Paper.PointFibreDerivedTensor
import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.SixFunctors.FrobeniusPointTransport
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso

/-! # Dual stalks and contragredient local Frobenius

Source: blueprint sec-purity-real-sheaves/sk-r-real-linear,
lem-tw-dual-negation.proof.md, first sentence; Bhatt--Scholze 6.8.14(2), 6.8.15;
Stacks 0FNY and 0GMX (blueprint: lem-tw-dual-stalk-frobenius).
The source's linear dual is represented by evaluation's universal property in the actual
common-stage coefficient category. Every representative of that dual has the assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The lisse linear dual exists, is again lisse and in the constructible heart, and its
closed-point stalk is the linear dual stalk with inverse-transpose geometric Frobenius.
The universal-property formulation includes every choice of representative of Hom(F,Omega_Y).
Source: blueprint lem-tw-dual-negation.proof.md, first sentence
(blueprint: lem-tw-dual-stalk-frobenius).

Proof:
1. Use lem-tw-lisse-rational-realization and def-weil-weil-sheaf-complex to choose one
   common finite coefficient stage for F, theta, and theta inverse. Realize its lisse
   carrier as a finite locally free E_Y-module. No stable integral lattice is used.
2. On a free chart use the coordinate dual, evaluation, and the coevaluation
   1 |-> sum e_i tensor e_i*. Under a basis change the two matrices cancel, so these
   tensors glue by lem-pur-sheaf-hom-cover-gluing. Both triangle identities hold on
   charts, hence globally. This includes rank zero and varying local ranks.
3. Apply lem-pur-ringed-site-finite-free-dual-pullback to g_Y and precompose by
   theta inverse. Evaluation is Weil-equivariant. The resulting dual realizes the
   internal Hom universal property above, and is lisse and constructible. Any other
   representing dual is uniquely evaluation-isomorphic to it; equivariance of the
   two evaluations makes that isomorphism a Weil isomorphism.
4. Iterate evaluation equivariance through theta^[r], where r is the residue degree.
   Use def-weil-local-frobenius-trace's return g_Y^r x=x g_s^r, and its specified
   pullback-composition maps. Restriction and the coprojections in
   def-weil-frobenius-point-transport preserve evaluation and constant scalars.
   The realized stalk pairing therefore satisfies b(F_dual d,F v)=b(d,v).
5. By lem-sf-point-fibre-derived-tensor the triangle identities pass to point fibres.
   If coevaluation(1)=sum v_j tensor d_j, the transpose c of evaluation has inverse
   lambda |-> sum lambda(v_j) d_j. The stalk is finite-dimensional by
   def-weil-local-frobenius-trace. Part 1 of
   lem-weil-frobenius-cohomology-transport-iso makes point transport invertible
   (use its auxiliary model Spec(k0), so Y0 needs no separatedness). Thus F is an
   automorphism A. Substitute A inverse v into b(F_dual d,A v)=b(d,v). This gives
   the pointwise formula and its equivalent conjugacy equation. All comparisons
   commute with extension from E to Omega by lem-tw-lisse-rational-realization. -/
theorem dual_stalk_frobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (F : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (_hF : @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber Y₀).left
      (sfWeilPrimeInvertible D l hl Y₀) F.obj.carrier) :
    (∃ Fv : sfCommonStageWeilComplex D l hl Y₀ Ω,
      IsCommonStageWeilLinearDual D l hl Y₀ Ω F.obj Fv) ∧
    ∀ Fv : sfCommonStageWeilComplex D l hl Y₀ Ω,
      IsCommonStageWeilLinearDual D l hl Y₀ Ω F.obj Fv →
        @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber Y₀).left
          (sfWeilPrimeInvertible D l hl Y₀) Fv.carrier ∧
        sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω Fv.carrier ∧
        ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
          (ι : Y₀.left.residueField y.val →+* D.k)
          (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
          FiniteDimensional Ω (localQbarClosedStalk l Ω D hl Y₀ F.obj y ι hι) ∧
          ∃ A : localQbarClosedStalk l Ω D hl Y₀ F.obj y ι hι ≃ₗ[Ω]
              localQbarClosedStalk l Ω D hl Y₀ F.obj y ι hι,
            A.toLinearMap = (localQbarClosedFrobeniusStalk l Ω D hl Y₀ F.obj y ι hι).hom ∧
            ∃ c : localQbarClosedStalk l Ω D hl Y₀ Fv y ι hι ≃ₗ[Ω]
                Module.Dual Ω (localQbarClosedStalk l Ω D hl Y₀ F.obj y ι hι),
              (∀ (φ : localQbarClosedStalk l Ω D hl Y₀ Fv y ι hι)
                (v : localQbarClosedStalk l Ω D hl Y₀ F.obj y ι hι),
                c ((localQbarClosedFrobeniusStalk l Ω D hl Y₀ Fv y ι hι).hom φ) v =
                  c φ (A.symm v)) ∧
              c.toLinearMap.comp
                ((localQbarClosedFrobeniusStalk l Ω D hl Y₀ Fv y ι hι).hom.comp
                  c.symm.toLinearMap) = LinearMap.dualMap A.symm.toLinearMap := by
  sorry

end WeilConjectures
