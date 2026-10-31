/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalEvaluationData
import WeilConjectures.AlgebraicGeometry.IntegralCompletedEvaluation
import WeilConjectures.AlgebraicGeometry.CompletedEvaluationRationalDescent
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory

/-! # Thickness of rational completed evaluation

Source: blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality, first proof paragraph
(blueprint: lem-sf-rational-thick-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t}) (U : Option X.ProEt)

set_option linter.unusedVariables false in
/-- Completed evaluation is natural and exact; its rational isomorphism locus is thick.

Source: blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality, first proof paragraph;
Stacks 08JD, 08JE, 099A, 0A0E, 014A
(blueprint: lem-sf-rational-thick-evaluation).

Proof plan (the twelve DAG steps):
1. The valuation ring is a Noetherian DVR. Constant-completion equivalence and the
   Koszul-completion reflector apply on the global site and its slices. They identify
   the quotient completion and its actual unit with the local-completeness reflector.
2. On K-flat models the balanced finite tensor identity sends
   (p tensor a) tensor (q tensor b) to (p tensor q) tensor ab, compatibly with
   transitions. Thus completed tensor is completion of ordinary tensor.
3. Tensor carries mapping cones to mapping cones by K-flat closure and the tensor-cone
   isomorphism. Strict quotient towers and total derived inverse limit are exact;
   hence completion and completed tensor are exact, with their canonical shifts.
4. Internal Hom sends triangles to reversed triangles with H(L[1],N)=H(L,N)[-1].
   Scalar actions are componentwise, hence both functors are linear. Stacks 099A
   makes every H(L,M) complete when M is complete, also on a slice.
5. Extend the ordinary evaluation uniquely across the quotient-completion unit.
   The reflector bijection and ordinary naturality prove completed naturality.
6. On representatives Hom shift contributes (-1)^a and tensor shift (-1)^b;
   evaluation after shift contributes exactly (-1)^(a+b). This checks the actual
   shift square, not just agreement on perfect generators.
7. Apply completion to that square. Its normalized unit commutes with shifts;
   uniqueness of extension into the complete shifted target proves the completed square.
8. Extend linear functors on fractions by F(Q(f)/t^n)=Q(F(f))/t^n.
   Every localized triangle is isomorphic to an integral image, so exactness descends.
   Naturality and the shift square descend by the same fraction identities.
9. Evaluation on the coefficient sheaf is evaluation at one. The comparison becomes
   the inverse completion unit of M, which is invertible by its completeness. Zero
   is sent to zero, with its unique morphism invertible.
10. Naturality conjugates components under rational isomorphisms. Additivity identifies
    the component on a finite biproduct with the biproduct of components. Shift
    compatibility identifies it with the shifted component.
11. For a rational retract i:A->B, p:B->A with i followed by p equal to one, the
    inverse component on A is Psi(p) followed by alpha_B inverse followed by Phi(i).
    Naturality gives both inverse equations, without integral retracts or splitting.
12. The reversed image triangles and the shift square give a morphism of distinguished
    triangles. If two components are invertible, the third is by the triangle-morphism
    isomorphism lemma. This proves every two-out-of-three extension case. -/
theorem rationalThickEvaluation
    [HasZeroObject (Rational l E X U)] [HasShift (Rational l E X U) ℤ]
    [∀ n : ℤ, (shiftFunctor (Rational l E X U) n).Additive]
    [Pretriangulated (Rational l E X U)] [IsTriangulated (Rational l E X U)]
    [(q l E X U).CommShift ℤ] [(q l E X U).IsTriangulated]
    (_hshift : shiftFunctor (Rational l E X U) (1 : ℤ) =
      ScalarLocalization.map (Padic.coefficientExtensionIntegers l E) (D l E X U)
        (Padic.coefficientExtensionUniformizer l E) (shiftFunctor (D l E X U) (1 : ℤ)))
    (_hQshift : ∀ L : D l E X U,
      HEq (((q l E X U).commShiftIso (1 : ℤ)).hom.app L)
        (𝟙 ((q l E X U).obj ((shiftFunctor (D l E X U) (1 : ℤ)).obj L))))
    (_htriangles : ∀ T : Triangle (Rational l E X U),
      T ∈ distTriang (Rational l E X U) ↔
        ∃ T' : Triangle (D l E X U), T' ∈ distTriang (D l E X U) ∧
          Nonempty (T ≅ (q l E X U).mapTriangle.obj T'))
    (_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (M : D l E X U) (hM : IsComplete l E X U M) :
    (phi l E X U M).Additive ∧ (phi l E X U M).Linear
      (Padic.coefficientExtensionIntegers l E) ∧
    (psi l E X U M).Additive ∧ (psi l E X U M).Linear
      (Padic.coefficientExtensionIntegers l E) ∧
    (∀ L : D l E X U, IsComplete l E X U ((psi l E X U M).obj (op L))) ∧
    ∃ (sPhi : (phi l E X U M).CommShift ℤ) (sPsi : (psi l E X U M).CommShift ℤ),
      (fun [phiShift : (phi l E X U M).CommShift ℤ]
        [psiShift : (psi l E X U M).CommShift ℤ] ↦
        (phi l E X U M).IsTriangulated ∧ (psi l E X U M).IsTriangulated ∧
        ∃ α : phi l E X U M ⟶ psi l E X U M,
          (∀ L : D l E X U,
            (completionUnit l E X U).app ((ordinaryPhi l E X U M).obj (op L)) ≫
              α.app (op L) = ordinaryEvaluation l E X U L M) ∧
          (∀ β : phi l E X U M ⟶ psi l E X U M,
            (∀ L : D l E X U,
              (completionUnit l E X U).app ((ordinaryPhi l E X U M).obj (op L)) ≫
                β.app (op L) = ordinaryEvaluation l E X U L M) → β = α) ∧
          NatTrans.CommShift α ℤ ∧
          ∃ (F G : (Rational l E X U)ᵒᵖ ⥤ Rational l E X U)
            (eF : (q l E X U).op ⋙ F ≅ phi l E X U M ⋙ q l E X U)
            (eG : (q l E X U).op ⋙ G ≅ psi l E X U M ⋙ q l E X U)
            (sF : F.CommShift ℤ) (sG : G.CommShift ℤ),
            (fun [fShift : F.CommShift ℤ] [gShift : G.CommShift ℤ] ↦
              F.IsTriangulated ∧ G.IsTriangulated ∧
              ∃ αQ : F ⟶ G,
                NatTrans.CommShift αQ ℤ ∧
                Functor.whiskerLeft (q l E X U).op αQ ≫ eG.hom =
                  eF.hom ≫ Functor.whiskerRight α (q l E X U) ∧
                (evaluationLocus l E X U M α) ((q l E X U).obj (coefficient l E X U)) ∧
                (evaluationLocus l E X U M α).IsTriangulated ∧
                (evaluationLocus l E X U M α).IsClosedUnderIsomorphisms ∧
                (evaluationLocus l E X U M α).IsStableUnderRetracts ∧
                (evaluationLocus l E X U M α).IsClosedUnderFiniteCoproducts)
              (fShift := sF) (gShift := sG)) (phiShift := sPhi) (psiShift := sPsi) := by
  obtain ⟨hPhiAdd, hPhiLin, hPsiAdd, hPsiLin, hComplete, sPhi, sPsi, hi⟩ :=
    integralCompletedEvaluation l E X U _hInv M hM
  let := hPhiAdd
  let := hPhiLin
  let := hPsiAdd
  let := hPsiLin
  let := sPhi
  let := sPsi
  obtain ⟨hPhiTri, hPsiTri, α, hα, hUnique, hShift, hUnit⟩ := hi
  let := hPhiTri
  let := hPsiTri
  let := hShift
  let := hUnit
  obtain ⟨F, G, eF, eG, sF, sG, hd⟩ :=
    completedEvaluation_rationalDescent l E X U _hshift _hQshift _htriangles M α
  let := sF
  let := sG
  obtain ⟨hFTri, hGTri, αQ, hQShift, hSquare⟩ := hd
  let := hFTri
  let := hGTri
  let := hQShift
  have hLocus : evaluationLocus l E X U M α = αQ.isoLocus.unop := by
    funext L
    apply propext
    have h := NatTrans.congr_app hSquare (op L.obj)
    change αQ.app (op L) ≫ eG.hom.app (op L.obj) =
      eF.hom.app (op L.obj) ≫ (q l E X U).map (α.app (op L.obj)) at h
    change IsIso ((q l E X U).map (α.app (op L.obj))) ↔ IsIso (αQ.app (op L))
    constructor
    · intro hIso
      let := hIso
      have : IsIso (αQ.app (op L) ≫ eG.hom.app (op L.obj)) := by rw [h]; infer_instance
      exact IsIso.of_isIso_comp_right _ (eG.hom.app (op L.obj))
    · intro hIso
      let := hIso
      have : IsIso (eF.hom.app (op L.obj) ≫
          (q l E X U).map (α.app (op L.obj))) := by rw [← h]; infer_instance
      exact IsIso.of_isIso_comp_left (eF.hom.app (op L.obj)) _
  have hTri : (evaluationLocus l E X U M α).IsTriangulated := by
    rw [hLocus]
    infer_instance
  have hRetract : (evaluationLocus l E X U M α).IsStableUnderRetracts := by
    rw [hLocus]
    exact ⟨fun r h ↦ αQ.isoLocus.prop_of_retract r.op h⟩
  let := hTri
  let := hRetract
  refine ⟨hPhiAdd, hPhiLin, hPsiAdd, hPsiLin, hComplete, sPhi, sPsi,
    hPhiTri, hPsiTri, α, hα, hUnique, hShift, F, G, eF, eG, sF, sG,
    hFTri, hGTri, αQ, hQShift, hSquare, ?_, hTri, inferInstance, hRetract, ?_⟩
  · change IsIso ((q l E X U).map (α.app (op (coefficient l E X U))))
    infer_instance
  · refine ⟨fun J _ ↦ ⟨?_⟩⟩
    rintro Z ⟨p⟩
    exact (evaluationLocus l E X U M α).prop_of_iso
      (((HasBiproductsOfShape.colimIsoLim (J := J)
        (C := Rational l E X U)).app p.diag).symm ≪≫
          IsColimit.coconePointUniqueUpToIso (colimit.isColimit p.diag) p.isColimit)
      ((evaluationLocus l E X U M α).prop_limit p.diag p.prop_diag_obj)

end WeilConjectures.IntegralOnSlice
