/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.FieldExtensionComposition
public import Sheaf.Paper.FieldExtensionReductionLimits
public import Sheaf.Paper.FieldExtensionLimitEquations
public import Sheaf.Paper.FieldExceptionalSystemLaws

/-! # Descent of whole-system comparisons through integral reconstruction

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- Reconstruct the prescribed whole-system comparisons in the integral categories.
The reduction family is supplied separately; the conclusion contains neither the
arbitrary strict-limit assertion nor any rational localization.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
apply Rlim to the tower comparisons and identify the integral adjunctions
(blueprint: lem-sp-field-extension-integral-descent).

Proof: for each coefficient field choose the reduction tower and normalized
reconstruction equivalence. Transfer the supplied tower right adjoint and its
finite adjunction evaluations through the section equivalences. The integral
adjunction realization theorem supplies the reconstructed functors, adjunction,
finite units and counits, and actual gamma. Exact Tate tensor and its K-flat
multiplication map supply SourceNormalization. This constructs the integral models.
Restrict the supplied proper/open comparison and its counit mate to normalized
constructible systems and conjugate by the same equivalences. Use the supplied
reduction family for the scalarReduction maps. Full faithfulness of reconstruction
lifts the resulting tower comparison uniquely to the integral comparison; its
unit and counit equations follow by injectivity on Hom groups. The orientation,
projection and tensor-transpose identities give the tower purity square. Applying
the total limit and inserting the reconstruction unit gives integral purity and
LimitEquations, with the indicated normalized scalar reductions. The canonical
source word is fixed on K-flat tensors independently of gamma. Finally multiplication
of three tensor factors gives the system coefficient cocycle, and full faithfulness
transports it to the three integral composition equations. This argument uses
faithfulness of normalized reconstruction, never of finite derived evaluation. -/
theorem field_extension_integral_descent
    [SmoothOfRelativeDimension d (j ≫ p)] [IsSeparated (j ≫ p)]
    (b : FieldShriekSystem.Laws P D (SpTowerGamma.factorization j p))
    (a : FieldExceptionalSystem.Domains P D (SpTowerGamma.factorization j p))
    (A : FieldExceptionalSystem.Adjoints P D (SpTowerGamma.factorization j p) b a)
    (laws : FieldExceptionalSystem.Laws P D (SpTowerGamma.factorization j p) b a A)
    (red : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F) (T : Scheme.{u})
      (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
      (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T)),
      Reduction P D E F h T RA RB) :
    ∃ (m : ∀ E : FieldShriekSystem.Index P, IntegralModel P D E j p d)
      (i : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
        IntegralComparison P D j p d E F h (m E) (m F)),
      (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F) (M : Integral P E X),
        HEq ((i E F h).scalarReductionX.hom.app M).hom
          ((red E F h X (m E).reductionX (m F).reductionX).reduction.hom.app M)) ∧
      (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F) (K : Integral P E Y),
        HEq ((i E F h).scalarReductionY.hom.app K).hom
          ((red E F h Y (m E).reductionY (m F).reductionY).reduction.hom.app K)) ∧
      (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
        LimitEquations P D j p d E F h (m E) (m F) (i E F h)) ∧
      ∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
        IntegralComposition P D j p d E F L h k (m E) (m F) (m L)
          (i E F h) (i F L k) (i E L (h.trans k)) := by sorry

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
