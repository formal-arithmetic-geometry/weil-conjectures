/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import Sheaf.Paper.SfPackageLocalizationBoundaryData

/-! # Descent of tower-pinned localization boundaries -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {Z U X Y : SixFunctorSpace D}
  [IsSeparated Z.obj.hom] [IsSeparated U.obj.hom]
  [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
  (i : Z ⟶ X) (j : U ⟶ X) (f : X ⟶ Y)
  [IsClosedImmersion i.hom.left] (hj : IsOpenImmersion j.hom.left)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (c : Compactification f.hom.left)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)

/-- A family of tower-pinned rational boundaries descends to the actual common-stage
operations, and the same family satisfies every finite scalar-transition square.
Source: current blueprint prop-functor-package.proof.md, clause (3), finite-field
extension and common-stage passage; prop-weil-pbc-descent-functors.
(blueprint: lem-sf-package-localization-boundary-descent).

Proof: realize each rational boundary as the exact compact-support image of the
unique source recollement boundary. Finite scalar extension is exact. Its normalized
operation comparisons preserve the counit and unit; recollement orthogonality makes
the source boundary unique, hence also preserves its third square. Compatibility of
the normalized support construction with scalar extension transports that square to
the actual compact-support values, giving the transition equations for the supplied
family. Descend this compatible natural transformation using common-stage descent:
on an object represented at E0 use the E0 boundary, conjugated by the specified
inclusion comparisons and canonical shift. The transition equations and comparison
cocycle make the arrow independent of enlargement, and naturality is checked after
moving any input morphism to a common finite field. The descended first two maps
are the actual localization arrows, by the unit/counit and composition equations.
Every triangle is represented at a finite field; the exact inclusion preserves its
distinguishedness. The construction gives the asserted inclusion squares for all
E0 simultaneously. Identity transitions, zero objects and empty strata are included. -/
theorem sfPackageLocalizationBoundaryDescent
    {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)
    (hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ)
    (hl : IsUnit (C.l : D.k))
    (δE : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SfPackageLocalizationBoundary
        (sixFunctorCoefficientRational D C S.closure.coefficientStages E₀) i j f cj ci
        (𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀)))
    (hE : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SfPackageLocalizationRationalBoundary i j f hj c cj ci
        (S.closure.coefficientStages E₀) hl (δE E₀)) :
    ∃ δbar : SfPackageLocalizationBoundary S.closure.commonStage i j f cj ci
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left)),
      (∀ K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
        sfPackageLocalizationTriangle S.closure.commonStage i j f hj c cj ci
          (𝟭 (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left)) δbar K ∈
            distTriang _) ∧
      (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
        SfPackageLocalizationCoefficientBoundary (S.closure.commonStageComparison E₀)
          f i j cj ci (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀) (δE E₀) δbar) ∧
      ∀ (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L),
        SfPackageLocalizationCoefficientBoundary (S.closure.coefficientTransition h)
          f i j cj ci (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift
            C.l C.Qbar Y.obj.left E₀ L h) (δE E₀) (δE L) := by sorry

end WeilConjectures
