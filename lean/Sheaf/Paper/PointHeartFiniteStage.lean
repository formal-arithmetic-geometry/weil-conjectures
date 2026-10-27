/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.Paper.PointHeartFiniteStageData
import Sheaf.Paper.PointHeartFiniteStageEquivalences
import Sheaf.Paper.PointHeartFiniteStageTruncations
import Sheaf.Paper.PointHeartFiniteStageScalars
import Sheaf.Paper.PointWeilFiniteStageDescent
import Sheaf.Paper.PointHeartExactness

/-! # Exact point hearts and finite-stage Weil representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Exact rational and common-stage point hearts, canonical truncation comparisons,
normalized scalar compatibility, and simultaneous finite-stage descent of a Weil pair.
No continuity condition on powers of the Frobenius isomorphism is imposed.

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-point-heart-finite-stage).

Proof: (1) Exact sections and exact rational localization make the specified finite
point realization t-exact. Standard module truncations preserve bounded finite-dimensional
cohomology. Apply the point-fibre equivalence.
(2) Its canonical truncation comparisons are characterized by counit and unit. Full
faithfulness reflects zero objects; applying this to the two complementary truncations
reflects both standard halves. Thus the equivalence restricts to the hearts.
(3) Degree-zero cohomology identifies the module heart with finite-dimensional spaces:
the canonical roof C <- tauLE(0) C -> H^0(C)[0] consists of quasi-isomorphisms.
The derived single embedding is fully faithful and H^0(V[0])=V.
(4) Compose the specified sections/scalar and cohomology/scalar comparisons. Their
unit and tower equations give the displayed scalar normalizations. Uniqueness of
truncation comparisons gives the scalar squares for both signs.
(5) Every common-stage heart object has a finite-stage heart model obtained by
tauGE(0) tauLE(0). The canonical maps identify this with the original object.
(6) Common-stage Hom is the colimit of finite-stage Hom. A linear map over Omega
is a finite matrix, whose entries lie in a common finite extension. A matrix becoming
zero over Omega was already zero. Standard free spaces give essential surjectivity.
(7) Full faithfulness and essential surjectivity transport and reflect the universal
properties of kernels, cokernels and zero objects. Additivity gives the asserted
short-exact equivalence and finite limit/colimit properties.
(8) Transport the given Frobenius by the finite-stage heart identification, using
alpha=e^-1 theta g*(e) and its explicit inverse. Functoriality proves intertwining.
(9) Represent these arrows, their inverses and the original target structure at finite
stages. There are finitely many inverse and intertwining equations in Hom colimits.
Each holds at a finite extension; their compositum makes them all hold at once.
The transported source remains in the heart. These representatives give u, M.obj.str,
targetTheta and e in the simultaneous witness on the recorded geometric-fibre category.
(10) Apply H^0 of the specified common-stage fibre to e^-1 and compose with the
specified scalar comparison. This is precisely fibre_normalization. Zero objects,
identity extensions and repeated fields satisfy the same formulas. -/
theorem zl_point_heart_finite_stage :
    (∀ E' : Padic.FiniteCoefficientFields l Ω,
      ZlPointHeartExact E'.val (zlPointHeartOmega D l hl E'.val)) ∧
    ZlPointHeartExact Ω (zlPointCommonHeartOmega D l hl Ω) ∧
    (∃ c : ∀ (E' : Type u) [Field E'] [Algebra (Padic l) E']
        [FiniteDimensional (Padic l) E'],
        ZlPointTruncationComparison E' (zlPointT D l hl E') (zlPointAmbient D l hl E'),
      (∀ (E' L' : Type u) [Field E'] [Algebra (Padic l) E']
        [FiniteDimensional (Padic l) E'] [Field L'] [Algebra (Padic l) L']
        [FiniteDimensional (Padic l) L'] (i : E' →ₐ[Padic l] L'),
        ZlPointScalarTruncationSquare D l hl E' L' i (c E') (c L'))) ∧
    Nonempty (ZlPointTruncationComparison Ω
      (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
      (zlPointCommonAmbient D l hl Ω)) ∧
    (∀ (E' : Type u) [Field E'] [Algebra (Padic l) E']
        [FiniteDimensional (Padic l) E']
        (K : sfRationalConstructibleCategory l E' (Spec (.of D.k))),
      (pointRationalFibre D l hl E' ⋙ DerivedCategory.coefficientFdCohomology E' 0).mapIso
         ((sfRationalScalarUnit l E' (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime))).app K) =
        zlPointHeartScalar D l hl E' E' (AlgHom.id (Padic l) E') K ≪≫
          (ModuleCat.extendScalarsId E').app
            ((pointRationalFibre D l hl E' ⋙
              DerivedCategory.coefficientFdCohomology E' 0).obj K)) ∧
    (∀ (E' L' N' : Type u) [Field E'] [Algebra (Padic l) E']
        [FiniteDimensional (Padic l) E'] [Field L'] [Algebra (Padic l) L']
        [FiniteDimensional (Padic l) L'] [Field N'] [Algebra (Padic l) N']
        [FiniteDimensional (Padic l) N']
        (i : E' →ₐ[Padic l] L') (j : L' →ₐ[Padic l] N')
        (K : sfRationalConstructibleCategory l E' (Spec (.of D.k))),
      (pointRationalFibre D l hl N' ⋙ DerivedCategory.coefficientFdCohomology N' 0).mapIso
         ((sfRationalScalarComp l E' L' i (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) N' j).app K) ≪≫
          zlPointHeartScalar D l hl E' N' (j.comp i) K =
        zlPointHeartScalar D l hl L' N' j ((zlPointScalar D l E' L' i).obj K) ≪≫
          (ModuleCat.extendScalars j.toRingHom).mapIso
            (zlPointHeartScalar D l hl E' L' i K) ≪≫
          ((ModuleCat.extendScalarsComp i.toRingHom j.toRingHom).app
            ((pointRationalFibre D l hl E' ⋙
              DerivedCategory.coefficientFdCohomology E' 0).obj K)).symm) ∧
    (∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B)
        (C : (DerivedCategory.pointFiniteDimensional A.val).FullSubcategory),
      (DerivedCategory.coefficientQbarCohomology l Ω 0).mapIso
          ((DerivedCategory.pointFdQbarStageComp l Ω h).app C) =
        DerivedCategory.coefficientCohomologyChangeStage l Ω h C 0) ∧
    (∀ (F : sfCommonStageWeilSheaf D l hl (zlPointHeartBase D) Ω)
        (y : {y : (zlPointHeartBase D).left // y ∈ closedPoints (zlPointHeartBase D).left})
        (ι : (zlPointHeartBase D).left.residueField y.val →+* D.k)
        (hι : ι.comp ((zlPointHeartBase D).hom.residueFieldAlgebraMap y.val) =
          algebraMap D.k₀ D.k),
      Nonempty (ZlPointFiniteStageWitness D l hl Ω F
        (localClosedPoint D (zlPointHeartBase D) y ι hι))) := by
  obtain ⟨hfinite, hcommon⟩ := zl_point_heart_essential_images D l hl Ω
  obtain ⟨htrunc, hcommontrunc⟩ := zl_point_heart_truncation_squares D l hl Ω
  obtain ⟨hunit, htower⟩ := zl_point_heart_scalar_normalizations D l hl
  refine ⟨?_, ?_, htrunc, hcommontrunc, hunit, htower, ?_, ?_⟩
  · intro A
    obtain ⟨hfull, hfaithful, hadd, himage⟩ := hfinite A
    apply zlPointHeartExact_of_essentialImage A.val _ hfull hfaithful hadd _ himage
    intro X
    unfold zlPointHeartOmega
    exact DerivedCategory.coefficientFdCohomology_finite A.val 0
      ((pointRationalFibre D l hl A.val).obj X.obj)
  · obtain ⟨hfull, hfaithful, hadd, himage⟩ := hcommon
    apply zlPointHeartExact_of_essentialImage Ω _ hfull hfaithful hadd _ himage
    intro X
    unfold zlPointCommonHeartOmega
    exact DerivedCategory.coefficientQbarCohomology_finite l Ω 0
      ((pointQbarFibre D l hl Ω).obj X.obj)
  · intro A B h C
    exact DerivedCategory.coefficientQbarCohomology_changeStage l Ω h C 0
  · intro F y ι hι
    obtain ⟨S⟩ := zl_point_weil_simultaneous_descent D l hl Ω F
    exact ⟨{
      A := S.A
      target_le := S.target_le
      M := S.M
      targetTheta := S.targetTheta
      u := S.u
      intertwining := S.intertwining
      target_structure := S.target_structure
      e := S.e
      e_hom := S.e_hom
      e_inv := S.e_inv
      fibre := (zlPointWeilFibreAt D l hl Ω
        (localClosedPoint D (zlPointHeartBase D) y ι hι)).mapIso S.e.symm ≪≫
          zlPointWeilStageOmega D l hl Ω S.A S.M.obj
            (localClosedPoint D (zlPointHeartBase D) y ι hι)
      fibre_normalization := rfl }⟩

end WeilConjectures
