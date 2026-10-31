/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicProjectionShiftData

/-! # AdicCompletedProjectionShift

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, adic Step 2
(blueprint: lem-pur-adic-completed-projection-shift). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open IntegralSystemRealization

section Exceptional
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (F : Type u) [Field F] [Algebra ℚ_[C.l] F] [FiniteDimensional ℚ_[C.l] F]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The completed projection is invertible and respects the second-input shift,
and its completed tensor-pullback output lies in the finite-Tor domain.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-completed-projection-shift).

Proof: choose the simultaneous strict-system realization. Apply the strict
compactification projection shift theorem to the reductions of T and K.
Its proper factor is the counit mate, its open factor is the unit-normalized
open tensor map, and its last factor is the pullback compositor. Realization
coherence identifies this composite with the ringed projection conjugated by
chi and the pullback completion unit, which is precisely adicProjection.
The normalized realization shift squares, with sign (-1)^a on first degree a,
transport the strict-system equality to the completed category. Naturality at
the inclusion comparison identifies the full-subcategory shift with the ambient
shift. The integral tensor/pullback closure and compact-support projection formula
give the output domain, invertibility of chi on these inputs, and invertibility
of this same projection. All equalities are established before finite evaluation;
no faithfulness of evaluations is used. The argument is uniform in the chosen
compactification, so also covers the proper-only and open-only choices. -/
theorem adicCompletedProjectionShift
    (d : RingedModels C.l F) (b : RingedOpenComparisons C.l F d)
    (T : finiteTorConstructibleIntegralCategory C.l F X) :
    ∃ (hχ : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        IsIso (((d.tensor Y).chi C.l F).app
          ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj, K.obj)))
      (hA : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        finiteTorConstructibleIntegral C.l F X
          ((integralCompletedTensor C.l F X).obj
            (T.obj, (integralDerivedPullback C.l F f).obj K.obj)))
      (hPF : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        IsIso (adicProjection C.l F d b c T.obj K.obj (hχ K))),
      ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        adicProjection C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj (hχ (K⟦(1 : ℤ)⟧)) ≫
            (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).map
              (adicTensorInputShift C.l F f T.obj K).hom ≫
            ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).commShiftIso
              (1 : ℤ)).hom.app _ =
          (integralCompletedTensor C.l F Y).map
              (Prod.mkHom (𝟙 _) (adicInputShift C.l F Y K).hom) ≫
            ((tensorShifts C.l F).integralRight Y 1).hom.app
              ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj,
                K.obj) ≫
            (adicProjection C.l F d b c T.obj K.obj (hχ K))⟦(1 : ℤ)⟧' := by sorry

end Exceptional
end WeilConjectures
