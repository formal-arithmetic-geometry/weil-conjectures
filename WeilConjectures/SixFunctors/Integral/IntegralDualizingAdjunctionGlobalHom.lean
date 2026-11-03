/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingAdjunctionData.IntegralDualizingAdjunctionData

/-! # Global derived Hom from the constructible exceptional adjunction

Source: current blueprint prop-coef-integral-dualizing.proof.md, direct adjunction argument.
(blueprint: lem-coef-integral-dualizing-adjunction-global-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The direct counit comparison for the exceptional value of the coefficient unit.
There is no finite tower, reduction comparison, completeness presentation or Tor bound in
this assertion. It is the enriched consequence of the specified compact-support adjunction.

Source: current blueprint prop-coef-integral-dualizing.proof.md, second paragraph
(blueprint: lem-coef-integral-dualizing-adjunction-global-hom).

Proof: use the derived-functor action on global mapping complexes for compact support,
written as the separately derived open-extension and proper-image factors of the published
compactification. Conjugate by A.supportIso, and postcompose with the ambient image of the
counit at A.unit and A.unitIso. Exact coefficient-point sections and the point-fibre
equivalence identify the resulting target with coefficientDerivedDual applied to the
published integralDualizingCompactSections. This constructs a natural transformation from
the global derived Hom into (A.right.obj A.unit).obj to that target, retaining the coefficient
module action. The section-action encoding and the ordinary global-Hom model comparison
identify the source with integralDualizingGlobalHom, not just its underlying abelian object.

In degree i the transformation sends h:K to (A.right.obj A.unit)[i] to compact support of h
followed by the shifted counit, followed by unitIso. The shift comparison for the right
adjoint is the canonical mate of the shift comparison for the exact compact-support
functor. Thus this is exactly the adjunction bijection in degree i, followed by the exact
point-sections equivalence. Each cohomology map is bijective as an R-linear map. Cohomology
in every degree detects isomorphisms in D(R), so every component is invertible. The original
transformation is natural in K because derived functor action, the counit, supportIso and
unitIso are natural; invert it componentwise to obtain the natural isomorphism. The proof
includes all shifts, torsion inputs, the zero object and the empty scheme, and uses no
inverse-limit calculation of mapping towers.
-/
theorem integralDualizing_adjunction_global_hom
    (A : IntegralDualizingAdjunctionData D l hl E X) :
    Nonempty (integralDualizingGlobalHom l E X (A.right.obj A.unit).obj ≅
      (integralDualizingCompactSections l E D hl X).op ⋙
        coefficientDerivedDual (integralDualizingCoefficients l E)) := by sorry

end WeilConjectures
