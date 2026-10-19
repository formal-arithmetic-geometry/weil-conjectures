/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.LogDifferentialStalk
import Sheaf.AlgebraicGeometry.LogCotangentComparison
import Sheaf.AlgebraicGeometry.LogFanChartBlowup
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.RingTheory.FiniteFreeMapResidueLocalizationStrong
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.EtaleLocalInfinitesimalLiftsSmooth

/-!
# The strict logarithmic Jacobian criterion

Source: ILO, Exposé X, proof of Proposition 1.2, printed p.138, referring to
Kato (1988), §3.12 (blueprint: lem-per-strict-log-jacobian-criterion).

The fs log schemes include local Noetherianness. Strictness is the existing
canonical characteristic-stalk isomorphism criterion from `LogFanChartBlowup`.
The cotangent injectivity hypothesis uses the canonical graph on the existing
logarithmic differential stalk modules.
-/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A strict morphism between log-smooth fs log schemes over the same base is smooth
near a geometric point if its logarithmic cotangent comparison is injective there.
Source: ILO, Exposé X, proof of Proposition 1.2, printed p.138; Kato (1988), §3.12
(blueprint: lem-per-strict-log-jacobian-criterion).

Proof:
1. Put `E = h*ω_Y/S` and `F = ω_X/S`, with comparison sending ordinary and logarithmic
   differentials to the differentials of their pullbacks. The finite-local-freeness
   clause of `lem-per-log-smooth-infinitesimal-calculus` gives finite bases after a
   strict étale localization. Injectivity over the geometric residue field implies
   injectivity over the ordinary residue field by faithful scalar extension.
   `lem-pc-finite-free-map-residue-localization-strong` supplies a left inverse after
   shrinking. Finitely many entries and their inverse identities spread from the
   geometric stalk to an étale neighbourhood `U → X`.
2. The calculus gives local finite presentation of `U → S` and `Y → S`. Over affine
   opens `Spec R`, `Spec B`, `Spec C`, the affine-open finite-presentation lemma
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` makes `B,C` finitely presented
   over `R`. Then `lem-weil-pbc-finite-presentation-over-finite-type-algebra` makes
   `C` finitely presented over `B`. Thus `U → Y` is locally of finite presentation.
3. In an arbitrary affine square-zero lifting problem `T₀ → U`, `T → Y`, give `T`
   the pulled-back log structure from `Y` and `T₀` its restriction. These are fine
   log structures even for non-Noetherian tests. Strictness of `h` gives the log map
   `T₀ → U`. The calculus produces lifts `a : T → U` over `S`, étale locally on `T`.
4. The torsor clause for `Y/S` identifies the difference of `ha` and the required
   map `b` with a homomorphism `δ : (ha₀)*ω_Y/S → I`, with `ha = b + δ`. If `r` is
   the left inverse from Step 1, set `ε = -δ ∘ a₀*r` and replace `a` by `a + ε`.
   The change under composition with `h` is `ε ∘ a₀*u = -δ`, so the new lift lies
   over `Y`. On log sections the changes multiply by `1 + ε(dlog m)`; products add
   because `I² = 0`. This solves every test problem étale locally.
5. Apply `lem-per-etale-local-infinitesimal-lifts-smooth` using Step 2 and the lifts
   in Steps 3--4. It makes `U → Y` smooth. Apply `lem-trf-etale-source-smoothness`
   at the chosen point of `U` to obtain smoothness of `h` on an open neighbourhood
   of the original geometric point. No descent of an arbitrary chosen lift is used.
-/
theorem EtaleLogHom.smooth_near_of_strict_logCotangent_injective
    {X Y S : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X S) (g : EtaleLogHom Y S) (h : EtaleLogHom X Y)
    (hf : f.IsLogSmooth) (hg : g.IsLogSmooth) (hover : h.CompEq g f)
    (hstrict : h.IsStrict) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme) (hinj : EtaleLogHom.IsLogCotangentInjective f g h t) :
    ∃ U : X.scheme.Opens, t default ∈ U ∧ Smooth (U.ι ≫ h.base) := by
  sorry

end AlgebraicGeometry
