/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Sheaf.Paper.IntegralConstructibleLinear
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Algebra.Module.TransferInstance

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.DerivedCompleteUnrestricted
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.IntegralDerivedOperations
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

public import Sheaf.CategoryTheory.RingedSiteModules

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# The rational completed-evaluation locus is thick

Source: Weil blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
first proof paragraph, exact functors and preservation of direct summands
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

/-- Restrict the published constant scalar section to the actual over-site.
Source: blueprint, sk-def-sf-operations (blueprint: lem-sf-rational-thick-evaluation). -/
def scalarConstant (V : (Site X U)ᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (ring l E X U).obj.obj V :=
  match U, V with
  | none, V => integralScalarConstant l E X V a
  | some _W, V => integralScalarConstant l E X (op V.unop.left) a

/-- Scalars act on complexes by multiplication by the specified constant section.
Source: blueprint, sk-def-sf-operations (blueprint: lem-sf-rational-thick-evaluation).
Proof: the scalar sections commute with restriction, since they do at every finite
projection. Commutativity makes multiplication linear. It commutes with differentials
and all module maps. These equations give the chain maps and their naturality;
equality on each degree and section proves uniqueness. -/
theorem scalarChain_existsUnique (a : Padic.coefficientExtensionIntegers l E) :
    ∃! σ : 𝟭 (Cx l E X U) ⟶ 𝟭 (Cx l E X U),
      ∀ (P : Cx l E X U) (n : ℤ) (V : (Site X U)ᵒᵖ) (x : (P.X n).val.obj V),
        ((σ.app P).f n).val.app V x = scalarConstant l E X U V a • x := by
  sorry

/-- The uniquely determined scalar action on complexes. Source: blueprint, sk-def-sf-operations
(blueprint: lem-sf-rational-thick-evaluation). -/
def scalarChain (a : Padic.coefficientExtensionIntegers l E) :=
  (scalarChain_existsUnique l E X U a).exists.choose

/-- The same scalar action after the actual quasi-isomorphism localization.
Source: Stacks 05RR (blueprint: lem-sf-rational-thick-evaluation). -/
def scalarDerived (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (D l E X U) ⟶ 𝟭 (D l E X U) :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : Cx l E X U ⥤ D l E X U)
    (HomologicalComplex.quasiIso (Mod l E X U) (ComplexShape.up ℤ)) (D l E X U)).preimage
      (Functor.whiskerRight (scalarChain l E X U a) DerivedCategory.Q)

/-- The canonical scalar action determines the linear structure, including localized maps.
Source: Stacks 05RR (blueprint: lem-sf-rational-thick-evaluation).
Proof: the ring and module identities hold on sections, hence on complexes. Whiskering
by the quasi-isomorphism localization is fully faithful, so they descend to the displayed
central derived endomorphisms. Define a f by precomposition with that endomorphism.
Centrality gives bilinear composition, and the formula determines every Hom action. -/
theorem linear_existsUnique :
    ∃! s : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U),
      (fun [linearInst : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U)] ↦
        ∀ (a : Padic.coefficientExtensionIntegers l E) (A B : D l E X U) (f : A ⟶ B),
          a • f = (scalarDerived l E X U a).app A ≫ f) (linearInst := s) := by
  sorry

/-- Use the canonical constant-section linear structure, not an arbitrary scalar action.
Source: Stacks 05RR (blueprint: lem-sf-rational-thick-evaluation). -/
instance linear : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U) :=
  (linear_existsUnique l E X U).exists.choose

/-- The opposite uses the same scalar action on reversed Hom modules.
Source: Stacks 08JC (blueprint: lem-sf-rational-thick-evaluation). -/
instance linearOpposite : Linear (Padic.coefficientExtensionIntegers l E) (D l E X U)ᵒᵖ where
  homModule A B := (opEquiv A B).module (Padic.coefficientExtensionIntegers l E)
  smul_comp A B C a f g := Quiver.Hom.unop_inj
    (Linear.comp_smul C.unop B.unop A.unop g.unop a f.unop)
  comp_smul A B C f a g := Quiver.Hom.unop_inj
    (Linear.smul_comp C.unop B.unop A.unop a g.unop f.unop)

/-- The canonical integer shifts preserve this coefficient action. Source: Stacks 05RR
(blueprint: lem-sf-rational-thick-evaluation).
Proof: translation and its signed differential commute with scalar multiplication
in each degree; fully faithful localization of natural transformations gives the
same assertion on all derived maps. -/
theorem shift_linear (n : ℤ) :
    (shiftFunctor (D l E X U) n).Linear (Padic.coefficientExtensionIntegers l E) := by
  sorry

/-- The shifts use the preceding canonical linearity proof. Source: Stacks 05RR
(blueprint: lem-sf-rational-thick-evaluation). -/
instance shiftLinear (n : ℤ) :
    (shiftFunctor (D l E X U) n).Linear (Padic.coefficientExtensionIntegers l E) :=
  shift_linear l E X U n

/-- The coefficient sheaf in degree zero. Source: Stacks 08JD
(blueprint: lem-sf-rational-thick-evaluation). -/
def coefficient : D l E X U := ringedSiteDualityUnit (topology X U) (ring l E X U)

/-- Psi is actual derived internal Hom with fixed second argument. Source: Stacks 08J7
(blueprint: lem-sf-rational-thick-evaluation). -/
def psi (M : D l E X U) : (D l E X U)ᵒᵖ ⥤ D l E X U :=
  (Functor.curry.obj (hom l E X U)).flip.obj M

/-- Ordinary dual tensor M before completing. Source: Stacks 08JE
(blueprint: lem-sf-rational-thick-evaluation). -/
def ordinaryPhi (M : D l E X U) : (D l E X U)ᵒᵖ ⥤ D l E X U :=
  psi l E X U (coefficient l E X U) ⋙
    Prod.sectL (D l E X U) M ⋙ (duality l E X U).closed.tensor

/-- Phi is completed dual tensor M. Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-rational-thick-evaluation). -/
def phi (M : D l E X U) : (D l E X U)ᵒᵖ ⥤ D l E X U :=
  psi l E X U (coefficient l E X U) ⋙
    Prod.sectL (D l E X U) M ⋙ completedTensor l E X U

/-- The actual ordinary adjunct of evaluation, with the Koszul symmetry in the node's order.
Source: Stacks 08JD, 08JE (blueprint: lem-sf-rational-thick-evaluation). -/
def ordinaryEvaluation (L M : D l E X U) :
    (ordinaryPhi l E X U M).obj (op L) ⟶ (psi l E X U M).obj (op L) :=
  ringedSiteDualEvaluationLeft (duality l E X U).closed (duality l E X U).symmetric
    (coefficient l E X U) (duality l E X U).unitIso L M

/-- The scalar localization uses the specified coefficient ring and uniformizer.
Source: blueprint, sk-def-sf-operations (blueprint: lem-sf-rational-thick-evaluation). -/
abbrev Rational := ScalarLocalization (Padic.coefficientExtensionIntegers l E)
  (D l E X U) (Padic.coefficientExtensionUniformizer l E)

/-- The actual tensor-with-one localization functor. Source: blueprint, sk-def-sf-operations
(blueprint: lem-sf-rational-thick-evaluation). -/
abbrev q : D l E X U ⥤ Rational l E X U :=
  ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
    (D l E X U) (Padic.coefficientExtensionUniformizer l E)

/-- Membership tests the actual localized evaluation component on the unchanged object.
Source: blueprint, sk-prop-sf-dualizable-biduality
(blueprint: lem-sf-rational-thick-evaluation). -/
def evaluationLocus (M : D l E X U) (α : phi l E X U M ⟶ psi l E X U M) :
    ObjectProperty (Rational l E X U) :=
  fun L ↦ IsIso ((q l E X U).map (α.app (op L.obj)))

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
  sorry

end WeilConjectures.IntegralOnSlice
