/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.DirectImagesConstructible

import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.WeilCompletedTensorReflector

/-! # Completed and rational tensor-Hom transposition

Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance, proof paragraph 2; Stacks 08J9, 08JA, 099B, 099M
(blueprint: lem-coef-completed-tensor-hom-transpose).

The completed evaluation is the normalized Hom-first counit preceded by the
canonical signed braiding. Rational scalar multiplication is written through
sfRationalCoefficientEquiv, the canonical identification of the localized ring with E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u a b
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The three equations meant by evaluation transposition, naturality in all three
variables, and signed symmetry compatibility. Here S is the already normalized
Hom-first closed data and beta is the recorded signed tensor symmetry.
Source: blueprint equivariance proof paragraph 2; Stacks 08J9
(blueprint: lem-coef-completed-tensor-hom-transpose). -/
structure CoefficientTransposeLaws {A : Type a} [Category.{b} A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (tau : ∀ (L : A) (P : J.FullSubcategory),
      (L ⟶ H.obj P) → (T.obj (P.obj.1.unop, L) ⟶ P.obj.2)) : Prop where
  /-- Evaluation with the argument first, as in the node's displayed formula. -/
  evaluation : ∀ L P phi,
    tau L P phi = T.map (Prod.mkHom (𝟙 P.obj.1.unop) phi) ≫
      (beta P.obj.1.unop (H.obj P)).hom ≫ S.evaluation P
  /-- One equation includes contravariance in P,L and covariance in Q. -/
  naturality : ∀ (L L' : A) (P P' : J.FullSubcategory) (f : L' ⟶ L)
    (g : P ⟶ P') (phi : L ⟶ H.obj P),
    tau L' P' (f ≫ phi ≫ H.map g) =
      T.map (Prod.mkHom g.hom.1.unop f) ≫ tau L P phi ≫ g.hom.2
  /-- It is the Hom-first transpose precomposed with the canonical Koszul symmetry. -/
  symmetry : ∀ L P phi,
    tau L P phi = (beta P.obj.1.unop L).hom ≫ (S.transpose L P).symm phi

/-- Residue-field inverses transported from the fixed base field. Naming this
canonical expression avoids repeating its elaboration in the transpose statement.
Source: blueprint coefficient convention, equivariance proof paragraph 2
(blueprint: lem-coef-completed-tensor-hom-transpose). -/
@[instance_reducible] def coefficientTransposeUnits
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))] :
    ∀ x : X, Invertible (C.l : X.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
      ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
        IsUnit (C.l : X.residueField x)).invertible

/-- Completed and raw rational transposition, with the precise evaluation formula,
all three naturalities and the signed tensor convention. The permitted pair P
bundles the node's objects P,Q and exactly its internal-Hom constructibility hypothesis.
Source: blueprint cor-coef-verdier-weil-equivariance, proof paragraph 2
(blueprint: lem-coef-completed-tensor-hom-transpose).

Proof (the four steps of the DAG):
1. On the completed-coefficient ringed site, identify global degree-zero derived
Hom with morphisms by lem-pur-rhom-global-sections. Internal-Hom currying gives
Hom(L,Hom(P,Q)) = Hom(L tensor P,Q). The model of def-coef-ringed-tensor-hom-model
identifies this with the evaluation counit, including its signed symmetry.
2. On simultaneous flat-term K-flat representatives, the balanced tensor comparison
sends (a tensor b) tensor r to (a tensor r) tensor (b tensor 1) at every quotient.
It commutes with quotient transitions. Thus the recorded completed tensor is the
quotient-tower completion of the ambient tensor, with its actual unit.
lem-weil-pbc-constant-completion-equivalence identifies that unit with Koszul
completion; lem-weil-pbc-ringed-koszul-completion-reflector gives the Hom bijection
into complete Q. Extend ambient evaluation uniquely along this unit.
lem-coef-derived-system-evaluation-calculus preserves this evaluation comparison.
Naturality of the unit proves that the extension of the ambient transpose is
exactly evaluation composed with 1 tensor phi.
3. Currying, global Hom and completion are natural and R-linear, so uniqueness
proves the stated three-variable equation. On degrees a,b the symmetry and
evaluation both introduce (-1)^(a*b). The normalized representative evaluation
and uniqueness through completion give the signed-symmetry equation.
4. Raw rationalization tensors the integral Hom groups and this R-linear
bijection with E. Its inverse tensors too. The operation formulas extend
bilinearly; hence evaluation, naturality and symmetry persist for every rational
arrow, including sums of pure tensors, with the displayed E scalar action.
No idempotent completion or lattice-preserving restriction is used. -/
theorem completedTensorHomTranspose
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    (∃ tau : ∀ (L : sfIntegralConstructibleCategory C.l E X)
        (P : (constructibleIntegralHomPairs C.l E X).FullSubcategory),
        (L ⟶ (constructibleIntegralHom C.l E X).obj P) ≃ₗ[
          Padic.coefficientExtensionIntegers C.l E]
          ((@constructibleIntegralTensor C.l _ E _ _ _ X
            (coefficientTransposeUnits D C X)).obj (P.obj.1.unop, L) ⟶ P.obj.2),
      CoefficientTransposeLaws
        (@podIntegralClosed C.l _ E _ _ _ X (coefficientTransposeUnits D C X))
        (@pullbackTensorIntegralBraiding C.l _ E _ _ _ X
          (coefficientTransposeUnits D C X))
        (fun L P phi ↦ tau L P phi)) ∧
    (∃ tau : ∀ (L : sfRationalConstructibleCategory C.l E X)
        (P : (constructibleRationalHomPairs C.l E X).FullSubcategory),
        (L ⟶ (rationalDerivedInternalHom C.l E X).obj P) ≃+
          ((@rationalDerivedTensor C.l _ E _ _ _ X
            (coefficientTransposeUnits D C X)).obj (P.obj.1.unop, L) ⟶ P.obj.2),
      CoefficientTransposeLaws
        (@podRationalClosed C.l _ E _ _ _ X (coefficientTransposeUnits D C X))
        (@pullbackTensorRationalBraiding C.l _ E _ _ _ X
          (coefficientTransposeUnits D C X))
        (fun L P phi ↦ tau L P phi) ∧
      ∀ L P (phi : L ⟶ (rationalDerivedInternalHom C.l E X).obj P) (c : E),
        tau L P ((sfRationalCoefficientEquiv C.l E).symm c • phi) =
          (sfRationalCoefficientEquiv C.l E).symm c • tau L P phi) := by
  sorry

end WeilConjectures
