/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.EtaleDerivedScalarTensor
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Algebra.Homology.AcyclicKFlatTensor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
/-!
# Ordinary and completed tensor with an integral coefficient line

Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4), Proposition 3.5.1 and
Definition 3.5.2 (blueprint: lem-sf-integral-line-tensor-comparison).
The comparison is the recorded completion unit, whose representative is the map
(c,0) into Cone(1-s)[-1]. Finite comparisons are normalized on sheafified pure
tensors; the projection equation uses the actual cone projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- The line is placed in degree zero, using the existing single-complex functor.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineSingle : Mod l E X none ⥤ Cx l E X none :=
  HomologicalComplex.single _ (ComplexShape.up ℤ) 0

/-- Ordinary derived tensor with a sheaf in degree zero. The tensor model is the
recorded total tensor on K-flat representatives. Source: Stacks 06YN, 06YY
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineOrdinary : (D l E X none) × (Mod l E X none) ⥤ D l E X none :=
  ((𝟭 (D l E X none)).prod (integralLineSingle l E X ⋙ DerivedCategory.Q)) ⋙
    (duality l E X none).closed.tensor

/-- The recorded completed tensor with the same degree-zero line.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineCompleted : (D l E X none) × (Mod l E X none) ⥤ D l E X none :=
  ((𝟭 (D l E X none)).prod (integralLineSingle l E X ⋙ DerivedCategory.Q)) ⋙
    completedTensor l E X none

/-- The canonical comparison, with its existing (c,0) cone normalization.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineComparison : integralLineOrdinary l E X ⟶ integralLineCompleted l E X :=
  Functor.whiskerLeft (integralLineOrdinary l E X) (completionUnit l E X none)

/-- The ordinary total complex P tensor T[0], with the signed direct-sum differential.
Source: Stacks 06YN (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineComplex (P : Cx l E X none) (T : Mod l E X none) : Cx l E X none :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (ring l E X none)).obj
    (P, (integralLineSingle l E X).obj T)

/-- Canonical K-flat representative comparison, transported along QP isomorphic to C.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineRepresentativeIso (P : (Good l E X none).FullSubcategory)
    (T : Mod l E X none)
    (hT : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X none) (R := ring l E X none) ((integralLineSingle l E X).obj T))
    (C : D l E X none) (e : DerivedCategory.Q.obj P.obj ≅ C) :
    DerivedCategory.Q.obj (integralLineComplex l E X P.obj T) ≅
      (integralLineOrdinary l E X).obj (C, T) :=
  ((duality l E X none).models.iso (topology X none) (ring l E X none)
      (duality l E X none).closed P.obj ((integralLineSingle l E X).obj T) P.property.1 hT) ≪≫
    (duality l E X none).closed.tensor.mapIso (Iso.prod e (Iso.refl _))

/-- The finite scalar-extension complex, before restoring the completed-ring action.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteComplex (n : ℕ) :=
  (reduction l E X none n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Total tensor of the two ordinary finite reductions, over the finite ring.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteTensor (P : Cx l E X none) (T : Mod l E X none) (n : ℕ) :=
  (coefficientTotalTensor.{u, t + 1, t} (topology X none) (finite l E X none n)).obj
    ((integralLineFiniteComplex l E X n).obj P,
      (integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))

/-- Restriction along the actual finite quotient projection, applied to complexes.
Source: Stacks 06YY (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineFiniteRestrict (n : ℕ) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (projection l E X none n))).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual projection from the strict Roos complex to its nth quotient.
Source: Stacks 08TC (blueprint: lem-sf-integral-line-tensor-comparison). -/
def integralLineRoosProjection (S : Cx l E X none) (n : ℕ) :
    integralOperationsRoos ((tower l E X none).obj S) ⟶
      ((level l E X none n).obj S) :=
  CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun m : ℕ ↦ ((tower l E X none).obj S).obj (op m))
        (integralOperationsTowerStep ((tower l E X none).obj S))) ≫
    Pi.π (fun m : ℕ ↦ ((tower l E X none).obj S).obj (op m)) n

/-- Tensor by a locally free integral line commutes with the specified completion.
Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4), Proposition 3.5.1 and
Definition 3.5.2 (blueprint: lem-sf-integral-line-tensor-comparison).

Proof: (1) ExtensionIntegersDvr and CompletedConstantSheafReduction identify the
actual completed-ring quotients with the finite constant coefficients, including
quotient projections. (2) On a cover trivializing T, tensor by T is the identity;
LocalizedModuleExactIndependent detects exactness there. Sectionwise products
(ProEtaleCountableProductsExact) show that the canonical product/tensor map is
invertible by the same calculation. Thus T[0] and its finite reductions are K-flat.
(3) Choose flat-term K-flat P by KFlatResolutionIndependentCoefficients; reduction
is K-flat by ChangeOfRingsKFlat and computes derived reduction by derived change
of rings. The finite balancing isomorphism sends a tensor (x tensor y) to
(a tensor x) tensor (1 tensor y); its inverse multiplies finite coefficients.
(4) FiniteFreeCompletedScalarComparison for the identity coefficient extension
makes the canonical (c,0) completion augmentation of P invertible.
(5) Tensor that augmentation with T. Exactness and product preservation identify
its target with the Roos complex of the tensor reductions. It is precisely the
recorded completionUnit, with zero second cochain. IntegralOperationsWellDefined
identifies this with completedTensor, independently of resolutions.
(6) Every construction commutes with chain maps and line isomorphisms. The acyclic
K-flat tensor lemma descends this naturality to D(R). The displayed projection
square and pure-tensor formula identify the reduction with the ordinary balancing
isomorphism: under SheafRingDerivedCoefficientAdjunction the augmentation's adjunct
sends a tensor x to a times its reduction. Consequently the adjunct of the target
projection is invertible, and the reduced comparison is the displayed finite iso.
No boundedness, constructibility or quasi-compactness is used. -/
theorem integralLineTensorComparison
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : D l E X none) (hC : IsComplete l E X none C)
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1] :
    IsIso ((integralLineComparison l E X).app (C, T)) ∧
    (∀ (C' : D l E X none) (_hC' : IsComplete l E X none C') (f : C ⟶ C')
        (T' : Mod l E X none) [T'.IsFiniteLocallyFreeOfRank 1] (eT : T ≅ T'),
      (integralLineOrdinary l E X).map (f, eT.hom) ≫
          (integralLineComparison l E X).app (C', T') =
        (integralLineComparison l E X).app (C, T) ≫
          (integralLineCompleted l E X).map (f, eT.hom)) ∧
    ∀ (P : (Good l E X none).FullSubcategory) (e : DerivedCategory.Q.obj P.obj ≅ C),
      ∃ (hT : CochainComplex.IsKFlatIndependentCoefficients
          (J := topology X none) (R := ring l E X none)
          ((integralLineSingle l E X).obj T))
        (hS : Good l E X none (integralLineComplex l E X P.obj T)),
        (integralLineRepresentativeIso l E X P T hT C e).hom ≫
            (integralLineComparison l E X).app (C, T) ≫
            (completion l E X none).map
              (integralLineRepresentativeIso l E X P T hT C e).inv ≫
            (completionComparison l E X none).hom.app
              ⟨integralLineComplex l E X P.obj T, hS⟩ =
          DerivedCategory.Q.map (roosUnit l E X none (integralLineComplex l E X P.obj T)) ∧
        ∀ n : ℕ, ∃ β :
            (integralLineFiniteComplex l E X n).obj (integralLineComplex l E X P.obj T) ≅
              integralLineFiniteTensor l E X P.obj T n,
          (∀ (p q k : ℤ) (hpq : p + q = k) (V : X.ProEtᵒᵖ)
              (a : (finite l E X none n).obj.obj V)
              (x : (P.obj.X p).val.obj V)
              (y : (((integralLineSingle l E X).obj T).X q).val.obj V),
            (β.hom.f k).val.app V
                (generator l E X none n ((integralLineComplex l E X P.obj T).X k) V a
                  (coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                    (ring l E X none) P.obj ((integralLineSingle l E X).obj T)
                    p q k hpq V x y)) =
              coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                (finite l E X none n) ((integralLineFiniteComplex l E X n).obj P.obj)
                ((integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))
                p q k hpq V (generator l E X none n (P.obj.X p) V a x)
                (generator l E X none n (((integralLineSingle l E X).obj T).X q) V 1 y)) ∧
          (integralLineComparison l E X).app (C, T) ≫
              (completion l E X none).map
                (integralLineRepresentativeIso l E X P T hT C e).inv ≫
              (completionComparison l E X none).hom.app
                ⟨integralLineComplex l E X P.obj T, hS⟩ ≫
              DerivedCategory.Q.map
                (integralLineRoosProjection l E X (integralLineComplex l E X P.obj T) n ≫
                  (integralLineFiniteRestrict l E X n).map β.hom) =
            (integralLineRepresentativeIso l E X P T hT C e).inv ≫
              DerivedCategory.Q.map
                (((augmentation l E X none).app (integralLineComplex l E X P.obj T)).app
                    (op n) ≫ (integralLineFiniteRestrict l E X n).map β.hom) := by
  sorry

end WeilConjectures
