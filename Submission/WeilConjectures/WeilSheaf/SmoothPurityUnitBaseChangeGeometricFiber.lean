/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.WeilSheaf.SmoothPurityDescendedTraceUniversal
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection
public import Submission.WeilConjectures.WeilSheaf.CondensedModelDescent
public import Submission.WeilConjectures.WeilSheaf.LowerStar

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- The geometric fibre `X̄ = X ×_{k} k̄` of `X` over `k`, as an object over `k̄`. -/
abbrev geometricFiberOver (X : Over (Spec (.of k))) : Over (Spec (.of (AlgebraicClosure k))) :=
  Over.mk X.hom.geometricFiberToAlgebraicClosure

instance (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (geometricFiberOver X).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))

instance (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (geometricFiberOver X).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd _ _))

instance (X : Over (Spec (.of k))) [IsSeparated X.hom] :
    IsSeparated (geometricFiberOver X).hom :=
  inferInstanceAs (IsSeparated (pullback.snd _ _))

/-- The base change `h̄ : X̄ ⟶ Ȳ` of a morphism `h : X ⟶ Y` over `k`. -/
abbrev geometricFiberOverMap {X Y : Over (Spec (.of k))} (h : X ⟶ Y) :
    geometricFiberOver X ⟶ geometricFiberOver Y :=
  Over.homMk (Scheme.Hom.geometricFiberMap h.left (Over.w h)) (by simp)

instance {X Y : Over (Spec (.of k))} (h : X ⟶ Y) [IsOpenImmersion h.left] :
    IsOpenImmersion (geometricFiberOverMap h).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.Hom.geometricFiberMap h.left (Over.w h)))

instance {X Y : Over (Spec (.of k))} (h : X ⟶ Y) [IsProper h.left] :
    IsProper (geometricFiberOverMap h).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) h.left (Over.w h)
    inferInstance

end GeometricFiber

section Charts

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

instance factPrime_ringChar_algebraicClosure : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩

instance factNe_ringChar_algebraicClosure : Fact (ringChar (AlgebraicClosure k) ≠ l) :=
  ⟨ringChar_algebraicClosure_ne (k₀ := k) (l := l)⟩

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- A chart of the étale normal form of `f : X ⟶ Y`: an open `j : U ⟶ X` on which
`j ≫ f = g ≫ jA ≫ p ≫ jV` with `g` étale (not recorded), `jA` an open immersion into
`P ≅ ℙⁿ_V`, `p` its projection and `jV : V ⟶ Y` an open immersion. -/
structure Chart (f : X ⟶ Y) where
  /-- The source of the chart. -/
  U : Over (Spec (.of k))
  /-- The étale target `𝔸ⁿ_V` of the chart. -/
  A : Over (Spec (.of k))
  /-- The projective space `ℙⁿ_V`. -/
  P : Over (Spec (.of k))
  /-- The open `V ⊂ Y`. -/
  V : Over (Spec (.of k))
  [hU₁ : LocallyOfFiniteType U.hom] [hU₂ : QuasiCompact U.hom] [hU₃ : IsSeparated U.hom]
  [hA₁ : LocallyOfFiniteType A.hom] [hA₂ : QuasiCompact A.hom] [hA₃ : IsSeparated A.hom]
  [hP₁ : LocallyOfFiniteType P.hom] [hP₂ : QuasiCompact P.hom] [hP₃ : IsSeparated P.hom]
  [hV₁ : LocallyOfFiniteType V.hom] [hV₂ : QuasiCompact V.hom] [hV₃ : IsSeparated V.hom]
  /-- The étale map `U ⟶ 𝔸ⁿ_V`. -/
  g : U ⟶ A
  /-- The open immersion `𝔸ⁿ_V ⟶ ℙⁿ_V`. -/
  jA : A ⟶ P
  /-- The projection `ℙⁿ_V ⟶ V`. -/
  p : P ⟶ V
  /-- The open immersion `V ⟶ Y`. -/
  jV : V ⟶ Y
  /-- The open immersion `U ⟶ X`. -/
  j : U ⟶ X
  [hj : IsOpenImmersion j.left]
  [hjV : IsOpenImmersion jV.left]
  [hp : IsProper p.left]
  /-- The relative dimension. -/
  n : ℕ
  /-- `P ≅ ℙⁿ_V`. -/
  eP : P.left ≅ ℙ(ULift.{u} (Fin (n + 1)); V.left)
  he : eP.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); V.left) ↘ V.left = p.left
  comm : j ≫ f = g ≫ jA ≫ p ≫ jV

attribute [instance] Chart.hU₁ Chart.hU₂ Chart.hU₃ Chart.hA₁ Chart.hA₂ Chart.hA₃ Chart.hP₁
  Chart.hP₂ Chart.hP₃ Chart.hV₁ Chart.hV₂ Chart.hV₃ Chart.hj Chart.hjV Chart.hp

variable (f : X ⟶ Y)

end Charts

end AlgebraicGeometry.ProEtale.CondensedRing
