/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceRestriction

/-! # Compositor form of the finite étale trace restriction square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefDualFormulaScalarTranspose

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- The compact-support coefficient map respects composition with the structure map,
evaluated at the upper dualizing object.
Source: Step 3 of lem-coef-etale-relative-trace-restriction, using
lem-sf-etale-restriction-compositor and lem-amb-unbounded-compact-support-comparisons
(blueprint: lem-coef-etale-relative-trace-restriction-compositor).
Proof: expand finiteSupportComposition into its three supplied-compactification
comparisons and the canonical unbounded compositor. For proper constituents compare
counit transposes of scalarMate; associativity of derived direct-image composition
identifies them. For open constituents the balancing maps commute with composition,
as is checked on the termwise extension by zero. The mixed square follows by taking
the proper/open exchange transpose and applying the same unit and counit equations.
Paste these equations with naturality of the coefficient maps. The unbounded
compact-support comparisons identify this paste with the displayed compositors.
On bounded-below inputs this is the scalar mate of the restriction-compositor
identity; the preceding unbounded construction retains that normalization without
assuming that arbitrary scalar extension preserves D+. No trace or dualizing
transition equation is assumed. -/
theorem finiteEtaleTrace_restriction_compositor (n : ℕ) :
    letI := c.hasCompactification
    letI := (finiteDualizingCompactification D X).hasCompactification
    letI := (finiteDualizingCompactification D Y).hasCompactification
    let q := finiteDualizingQuotient l E n.le_succ
    let K := finiteDualizingEtaleTerm l E D X (n + 1)
    let FA := Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c
    let GB := finiteDualizingEtaleSupport l E D Y n
    let aA := finiteSupportComposition (finiteDualizingCoeff l E (n + 1)) f
      (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
      (CategoryTheory.comp_over f (Spec (.of D.k))) c
      (finiteDualizingCompactification D Y) (finiteDualizingCompactification D X)
    let aB := finiteSupportComposition (finiteDualizingCoeff l E n) f
      (Y ↘ Spec (.of D.k)) (X ↘ Spec (.of D.k))
      (CategoryTheory.comp_over f (Spec (.of D.k))) c
      (finiteDualizingCompactification D Y) (finiteDualizingCompactification D X)
    Etale.ExceptionalCoefficients.compactSupportMap q
        (finiteDualizingCompactification D Y) (FA.obj K) ≫
      GB.map (Etale.ExceptionalCoefficients.compactSupportMap q c K) ≫
      aB.hom.app ((Etale.scalarExtension q X).obj K) =
    (Etale.scalarExtension q (Spec (.of D.k))).map (aA.hom.app K) ≫
      Etale.ExceptionalCoefficients.compactSupportMap q
        (finiteDualizingCompactification D X) K := by
  sorry

end WeilConjectures.CoefDualFormulaScalarTranspose
