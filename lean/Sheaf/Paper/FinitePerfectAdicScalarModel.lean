/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.FinitePerfectAdicScalarCoherence
public import Sheaf.Paper.FinitePerfectAdicConstantCohomology

/-! # The constant-model comparison for explicit scalar realization

Source: Stacks Project, Tags 093J, 093M, 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Constant algebraic quotient complexes have the canonical realized model diagram,
including its specified consecutive arrows.

Source: Stacks Project, Tags 093J, 093M, 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-scalar-model).

Proof: represent each perfect level by a bounded complex of finite projective modules.
Universe lift and exact constant realization preserve these representatives and their
finite-projective splittings. Inverse image to U, restriction along W and transport to
the slice commute with constants, by their constant-section units. The locally bijective
finite coefficient unit identifies the resulting fixed-ring module sheaf with the
actual quotient-ring module sheaf. After forgetting quotient scalars, flatness of the
completed constant ring over the constant A-ring and its canonical finite reduction
identify this with completed scalar extension of the A-restriction of the algebraic
level. These natural identifications give model. On an algebraic quotient arrow all
comparisons send a constant pure tensor to that same constant section. Associativity
of scalar restriction and the equation between the two consecutive completed
projections show that the two displayed composites agree on these generators.
Sheafification, termwise total complexes and localization preserve this equality,
giving the specified model_normalized equation. This does not select a marking or
use an actual quotient of M. Zero rings, zero complexes and empty charts use the same
canonical tensor and sheafification maps. -/
theorem finitePerfectAdicScalar_model
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n)) :
    ∃ model : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≅
      (finitePerfectAdicModelDiagram X d W T).obj (op n),
      ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        (finitePerfectAdicEtaleConstantTransition V.left T n)) ≫
      (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≫
      (model U W f n).hom =
    (model U W f (n + 1)).hom ≫
      (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op := by sorry

end AlgebraicGeometry.Scheme
