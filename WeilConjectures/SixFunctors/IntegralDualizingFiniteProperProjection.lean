/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
import WeilConjectures.SixFunctors.CoefPairingLeftMateEquivalence
import WeilConjectures.CategoryTheory.UnshiftedNaturalTransformationGeneration
import WeilConjectures.SixFunctors.FiniteScalarShiftTensorEquivalences
import WeilConjectures.SixFunctors.FiniteScalarProjectionFunctorBounds

/-! # Finite proper projection with an arbitrary scalar complex

Source: prop-asd-internal-adjunction, projection-formula step;
prop-coef-integral-dualizing, second proof paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- At the single quotient `A_(q+1)`, proper projection is invertible on the
finite reduction of an integral finite-Tor constructible input, tensored with
an arbitrary scalar complex pulled back by the finite sections adjunction.
There is no coefficient sequence or left adjoint to sequence evaluation in
this assertion. The finite frame uses the actual intrinsic open extension and
proper direct image; `S` and `G` specify its finite tensor presentations.

Source: prop-asd-internal-adjunction, projection step; Stacks 0B56, 07A6, 0941.
(blueprint: lem-coef-finite-scalar-test-proper-projection).

Proof: form the natural transformation between the scalar tensor functor and
the proper-image scalar tensor functor by the recorded projection mate. Both
functors are exact and preserve coproducts: exactness comes from the actual
internal-Hom and sections/direct-image adjunctions, and preservation of target
coproducts uses finite Tor constructibility, etale origin and proper finite
cohomological dimension. The supplied scalar and proper left adjoints send
shifts of the free scalar module to tensor-invertible objects. At each such
shift, the supplied tensor comparison gives an invertible square between
tensor equivalences, whose mate is invertible. Module generation now applies.
For triangle closure use the five lemma on the triangle and its first two
rotations, so no shift coherence of the supplied tensor comparison is assumed.
Coproduct and retract closure follow from their universal properties and
naturality. The zero shift gives the asserted component at T. This includes
zero scalar complexes, zero K, empty schemes, and every positive quotient. -/
theorem integralDualizing_finite_scalar_test_proper_projection_isIso
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (q : ℕ) (F : CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G q)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    IsIso (CategoryTheory.CoefPairingFrame.leftMate
      (G.baseTensors.finiteClosed q).tensor (G.compactTensors.finiteClosed q).tensor
      F.pstar
      (proEtaleConstantDerivedDirectImage (finiteDualizingCompactification D X).g
        (Padic.coefficientExtensionRing l E (q + 1)))
      F.properAdjunction F.properTensor (F.sstar.obj T)
      ((sfIntrinsicExtensionByZero (finiteDualizingCompactification D X).i
        (Padic.coefficientExtensionRing l E (q + 1))).mapDerivedCategory.obj
          ((coefficientFiniteDerivedExtension l E X q).obj K))) := by
  let c := finiteDualizingCompactification D X
  let P := proEtaleConstantDerivedDirectImage c.g
    (Padic.coefficientExtensionRing l E (q + 1))
  let M := (sfIntrinsicExtensionByZero c.i
    (Padic.coefficientExtensionRing l E (q + 1))).mapDerivedCategory.obj
      ((coefficientFiniteDerivedExtension l E X q).obj K)
  let TC := (G.baseTensors.finiteClosed q).tensor
  let TB := (G.compactTensors.finiteClosed q).tensor
  let A := F.sstar ⋙ Prod.sectL _ (P.obj M) ⋙ TC
  let B := F.sstar ⋙ F.pstar ⋙ Prod.sectL _ M ⋙ TB ⋙ P
  let flip := (Functor.flipping
    (C := normalizedDVRDerived.{u, u} l E (Spec (.of D.k)) q)
    (D := normalizedDVRDerived.{u, u} l E (Spec (.of D.k)) q)
    (E := normalizedDVRDerived.{u, u} l E c.Z q)).functor
  let α : A ⟶ B := Functor.whiskerLeft F.sstar
    ((F.properAdjunction.rightAdjointProjectionMap
      (T_C := (Functor.curryObj TB).flip) (T_D := (Functor.curryObj TC).flip)
      (flip.map (Functor.curry.map F.properTensor.hom) ≫
        (flip.mapIso (Functor.curryObjProdComp F.pstar F.pstar TB)).hom)).app M)
  obtain ⟨sA, sB, hA, hB, hcopA, hcopB⟩ :=
    finiteScalarProjection_functor_bounds l E X D hl S G q F K hK
  let := sA
  let := sB
  have : A.IsTriangulated := hA
  have : B.IsTriangulated := hB
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) A := hcopA I
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) B := hcopB I
  apply derivedModule_isIso_of_shifted_regular (coefTraceRing l E) A B α _ T
  intro n
  obtain ⟨hC, hZ⟩ := finiteScalarShift_tensor_equivalences l E X S G q F n
  let := hC
  let := hZ
  exact CategoryTheory.CoefPairingFrame.leftMate_isIso_of_tensor_equivalences
    TC TB F.pstar P F.properAdjunction F.properTensor _ M

end WeilConjectures
