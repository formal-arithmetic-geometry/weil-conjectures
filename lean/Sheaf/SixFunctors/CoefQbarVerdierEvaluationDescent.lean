/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierFunctor

/-! # The constructed common-stage dualizing object and evaluation

Source: thm-coef-qbar-verdier, proof steps 4--5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

attribute [local irreducible] WeilConjectures.CoefQbarTensor

/-- Omega is the included dualizing object at the base coefficient field. -/
def descendedOmega (F : Finite D l hl Ω X) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  (inclusion (Padic.finiteCoefficientBase l Ω)).obj
    ((sfRationalConstructibleLocalization l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω)) X).obj
        (F.omega (Padic.finiteCoefficientBase l Ω)).omega)

/-- The normalized finite u maps identify every finite omega with the base object. -/
def descendedOmegaComparison (F : Finite D l hl Ω X) (E : Index l Ω) :
    (inclusion E).obj ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (F.omega E).omega) ≅ descendedOmega D l hl Ω X F := by
  let O := Padic.finiteCoefficientBase l Ω
  have h : O ≤ E := show (⊥ : IntermediateField (Padic l) Ω) ≤ E.val from bot_le
  exact (inclusion E).mapIso (F.scalar O E h).omega.symm ≪≫
    (inclusionTransition l Ω X O E h).app _

/-- Compare the finite tensor with the actual tensor of the included object and dual. -/
def descendedTensorComparison (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) (E : Index l Ω) (K : Stage l Ω X E) :
    (inclusion E).obj ((RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E)).obj
      (K, (F.datum E).dual.obj (op K))) ≅
    (CoefQbarTensor D l hl Ω X).obj
      ((inclusion E).obj K, (descendedDual D l hl Ω X F hF).obj (op ((inclusion E).obj K))) :=
  tensorInclusion D l hl Ω X E K ((F.datum E).dual.obj (op K)) ≪≫
    (CoefQbarTensor D l hl Ω X).mapIso
      (Iso.prod (Iso.refl _) ((descendedComparison D l hl Ω X F hF E).app (op K)))

/-- Evaluation is the included finite evaluation at the object's own stage,
transported by the specified tensor and omega comparisons. -/
def descendedEvaluation (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (CoefQbarTensor D l hl Ω X).obj
      (K, (descendedDual D l hl Ω X F hF).obj (op K)) ⟶ descendedOmega D l hl Ω X F :=
  (descendedTensorComparison D l hl Ω X F hF K.stage K.obj).inv ≫
    (inclusion K.stage).map ((F.datum K.stage).evaluation K.obj) ≫
      (descendedOmegaComparison D l hl Ω X F K.stage).hom

/-- The normalization of evaluation at an included finite object is definitional
up to cancellation of the specified tensor comparison. -/
theorem descendedEvaluation_finite (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) (E : Index l Ω) (K : Stage l Ω X E) :
    (tensorInclusion D l hl Ω X E K ((F.datum E).dual.obj (op K))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 ((inclusion E).obj K))
          ((descendedComparison D l hl Ω X F hF E).hom.app (op K))) ≫
      descendedEvaluation D l hl Ω X F hF ((inclusion E).obj K) =
    (inclusion E).map ((F.datum E).evaluation K) ≫
      (descendedOmegaComparison D l hl Ω X F E).hom := by
  rw [← Category.assoc]
  change (descendedTensorComparison D l hl Ω X F hF E K).hom ≫
    ((descendedTensorComparison D l hl Ω X F hF E K).inv ≫ _) = _
  erw [Iso.hom_inv_id_assoc]
  rfl

/-- The constructed omega comparisons are coherent and evaluation is natural.
Source: thm-coef-qbar-verdier, proof steps 4--5, common-stage evaluation descent
(blueprint: lem-coef-qbar-verdier-evaluation-equations).

Proof: for base <= E <= L, the three finite scalar u maps compose through the
prescribed tensor associator. This follows by localizing the canonical integral
u tower equation: the normalized reduction maps agree at every finite quotient,
so derived completeness identifies the two maps. Naturality and the cocycle of
the inclusion-transition isomorphisms then give the displayed omega equation.
For an arrow K -> M, choose a common stage representing it. Expand the two
constructed evaluations there using the finite scalar evaluation square and the
omega equation just proved. The representative formula for descendedDual
conjugates the finite dual arrow by beta and inverse beta. The two tensor
comparison factors therefore cancel against the finite scalar evaluation
square. What remains is precisely (F.datum L).evaluation_natural at that common
stage L. Include this equality; compatibility with further extension proves it
for the quotient class. Equal fields, zero objects, and zero arrows use the
same equations, so no nonzero or positive-dimensional hypothesis is needed. -/
theorem descendedEvaluation_equations (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    (∀ (E L : Index l Ω) (h : E ≤ L),
      (inclusion (Y := X) L).map (F.scalar E L h).omega.hom ≫
        (descendedOmegaComparison D l hl Ω X F L).hom =
      (inclusionTransition l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (F.omega E).omega) ≫ (descendedOmegaComparison D l hl Ω X F E).hom) ∧
    (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X) (f : K ⟶ M),
      (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom f (𝟙 ((descendedDual D l hl Ω X F hF).obj (op M)))) ≫
        descendedEvaluation D l hl Ω X F hF M =
      (CoefQbarTensor D l hl Ω X).map
          (Prod.mkHom (𝟙 K) ((descendedDual D l hl Ω X F hF).map f.op)) ≫
        descendedEvaluation D l hl Ω X F hF K) := by sorry

end WeilConjectures.CoefQbarVerdier
