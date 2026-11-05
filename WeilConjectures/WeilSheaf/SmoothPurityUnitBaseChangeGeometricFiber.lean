/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeChart
public import WeilConjectures.WeilSheaf.CondensedModelDescent
public import WeilConjectures.WeilSheaf.LowerStar

/-!
# The exceptional base change map at the unit along `k₀ ⟶ k̄`: gluing the charts (A1')

Let `k₀` be a finite field with algebraic closure `k̄`. For `X` over `k₀` we write `X̄` for its
geometric fibre, viewed over `k̄` (`geometricFiberOver`), and `h̄ : X̄ ⟶ Ȳ` for the base change
of `h : X ⟶ Y` (`geometricFiberOverMap`); the squares `πX ≫ h = h̄ ≫ πY` are cartesian
(`isPullback_geometricFiberOverMap`) and `πY = Y.hom.geometricFiberProj` is weakly étale.

Given a **global compact-support exchange** `Ex`, attached to every cartesian square over
`k₀ ⟶ k̄`, compatible with composition (`hEx`), agreeing with proper base change for the proper
pieces (`hExProper`), and with invertible mates for the étale and open-immersion pieces (step 2,
`hj`, `hg`, `hjA`, `hjV`), the exceptional base change map at the unit of a smooth `f : X ⟶ Y`
is invertible as soon as `X` is covered by charts `U --g--> A --jA--> ℙⁿ_V --p--> V --jV--> Y`
with `j ≫ f = g ≫ jA ≫ p ≫ jV` (`Chart`, the étale normal form of `f`):
`isIso_smoothUnitBaseChange_geometricFiber_of_charts`. The proof is: locality on `X̄`
(`isIso_smoothUnitBaseChange_of_openCover`), transport along `j ≫ f = g ≫ jA ≫ p ≫ jV`,
composition compatibility of `Ex`, and the chart theorem
`isIso_smoothUnitBaseChange_chart_of_projectiveSpace`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section GeometricFiber

variable {k : Type u} [Field k] [Finite k]

end GeometricFiber

section Charts

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

attribute [instance] Chart.hU₁ Chart.hU₂ Chart.hU₃ Chart.hA₁ Chart.hA₂ Chart.hA₃ Chart.hP₁
  Chart.hP₂ Chart.hP₃ Chart.hV₁ Chart.hV₂ Chart.hV₃ Chart.hj Chart.hjV Chart.hp

variable (f : X ⟶ Y)

end Charts

end AlgebraicGeometry.ProEtale.CondensedRing
