/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierSignedShift
public import WeilConjectures.SixFunctors.RationalVerdier.RationalTensorOppositeShift
public import WeilConjectures.CategoryTheory.SixFunctors.EvaluationShiftTransport

/-! # The signed Hom shift transposes completed tensor cancellation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (w : IntegralFiniteExtension.DualizingDatum l X D hl E)
  (A : Datum D l hl X E w)

/-- The fixed signed dual shift is the transpose of signed tensor cancellation.
Source: blueprint thm-coef-qbar-verdier steps 3--4, the tensor--Hom evaluation
argument; Stacks Tags 0A8X, 08JC and 0941.
(blueprint: lem-coef-rational-verdier-signed-evaluation-shift-X3).

Proof: resolve the integral source by a flat-term K-flat complex P and the
integral dualizing target by a K-injective complex I. Use the fixed Hom-product
projections to compute the inverse signed shift on Hom(P,I). Its degree-j
coefficient is (-1)^(-nj+n(n+1)/2). Ordinary evaluation on degrees i,j has
coefficient (-1)^(ij). Right-slot then left-slot tensor cancellation contributes
(-1)^(ni), while evaluation after shifting contributes (-1)^((i-n)(j+n)).
The difference is n(n-1)/2 modulo two, giving exactly signedOppositeShift.
Generation by local homogeneous tensors and joint monicity of Hom projections
prove the chain equation. The fixed completion map carries the same quotient
coordinates and zero second cone coordinate, so this equation survives the
Roos mapping-fiber comparison. Apply derived localization and use the
representative equations of A.ordinary and A.completion. The integral full
inclusion is faithful, and its shift comparison transports the equation to the
constructible integral category. Finally scalar-localize the equation. The
localizationDualComparison shift equation and A.evaluation_integral identify
its sides with the displayed rational maps. Every rational object is represented
by an integral one, so this proves the formula for all K and all integer n. -/
theorem signedShift_evaluation (n : ℤ) (K : sfRationalConstructibleCategory l E X) :
    letI := signedShift D l hl X E w A
    (tensor D l hl X E).map (Prod.mkHom (𝟙 (K⟦-n⟧))
        (reindexedDualShift A.dual n K).inv) ≫ A.evaluation (K⟦-n⟧) =
      signedOppositeShift D l hl X E K (A.dual.obj (op K)) n ≫ A.evaluation K := by sorry

end WeilConjectures.RationalVerdier
