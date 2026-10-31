/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceRestriction

/-! # Mate form of the finite étale trace restriction square -/

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

/-- The scalar adjunct of the restriction path is the compact-support coefficient map
followed by compact support of the dualizing comparison and the lower trace.
Source: Step 2 of lem-coef-etale-relative-trace-restriction, and the mate equation of
lem-sf-etale-compact-scalar-restriction
(blueprint: lem-coef-etale-relative-trace-restriction-mate).
Proof: identify the bounded-below restriction map with the proper/open restriction
isomorphism in the scalar mate theorem. Write the transition as the scalar unit
followed by restriction of the dualizing comparison. Naturality of the restriction
map moves the latter comparison to its target. The scalar compact-support mate
equation identifies the adjunct of the first two factors with compactSupportMap.
Naturality of the Hom bijection for the final trace gives the displayed composite.
The assertion contains only the restriction path, and applies also at n = 0. -/
theorem finiteEtaleTrace_restriction_mate (n : ℕ) :
    let q := finiteDualizingQuotient l E n.le_succ
    let FA := Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E (n + 1))) c
    let FB := Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c
    let UY := Sheaf.derivedRestrictScalars Y.smallEtaleTopology q
    let adj := Adjunction.ofIsRightAdjoint UY
    (adj.homEquiv (FA.obj (finiteDualizingEtaleTerm l E D X (n + 1)))
      (finiteDualizingEtaleTerm l E D Y n)).symm
      (FA.map (finiteDualizingEtaleTransition l E D X n.le_succ) ≫
        finiteEtaleSupportRestriction q c
          ⟨finiteDualizingEtaleTerm l E D X n, finiteEtaleDualizing_plus D l E X n⟩ ≫
        UY.map (finiteEtaleTrace D l E f c n)) =
      Etale.ExceptionalCoefficients.compactSupportMap q c
          (finiteDualizingEtaleTerm l E D X (n + 1)) ≫
        FB.map (finiteDualizingEtaleComparison l E D X n.le_succ) ≫
        finiteEtaleTrace D l E f c n := by
  sorry

end WeilConjectures.CoefDualFormulaScalarTranspose
