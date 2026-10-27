/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.LogDifferentialStalk
public import Sheaf.AlgebraicGeometry.FSStrictLogMorphism
public import Sheaf.AlgebraicGeometry.LogCotangentComparison
import WeilConjectures.RingTheory.FiniteFreeMapResidueLocalizationStrong
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource

/-!
# The strict logarithmic Jacobian criterion

Source: ILO, Exposé X, proof of Proposition 1.2, printed p.138, applying
Kato (1988), §3.12 (blueprint: lem-per-strict-log-jacobian-criterion).

Injectivity of the canonical comparison on logarithmic cotangent spaces implies
smoothness near the chosen geometric point for a strict morphism over a common
log-smooth base. The existing graph presentation specifies the canonical comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.EtaleLogHom

/-- A strict morphism between log-smooth fs log schemes over a common base is smooth
near a geometric point where its logarithmic cotangent comparison is injective.
Source: ILO, Exposé X, proof of Proposition 1.2, printed p.138; Kato (1988), §3.12
(blueprint: lem-per-strict-log-jacobian-criterion).

Proof:
1. By `lem-per-log-smooth-infinitesimal-calculus`, the relative logarithmic
   differentials are finite locally free. Choose strict étale neighborhoods with
   bases. Injectivity over the geometric residue field descends to the ordinary
   residue field by faithful field extension. Apply
   `lem-pc-finite-free-map-residue-localization-strong` to obtain, after shrinking,
   a retraction `r` of the differential comparison `u`. Spread its finitely many
   entries and identities to an étale neighborhood `U` of the chosen point.
2. The calculus makes `U → S` and `Y → S` locally of finite presentation.
   By `lem-weil-pbc-lfp-affine-opens-finite-presentation`, their affine coordinate
   rings are finitely presented over the base. Apply
   `lem-weil-pbc-finite-presentation-over-finite-type-algebra` to conclude that
   `U → Y` is locally of finite presentation.
3. For an arbitrary affine square-zero thickening `T₀ → T` and a lifting square
   into `U → Y`, pull the log structure of `Y` back to `T` and then to `T₀`.
   Strictness of `h` gives the canonical log map `T₀ → U`. The calculus supplies
   a log lift `a : T → U` over `S`, étale locally on `T`.
4. The torsor clause of the calculus gives the difference `δ` between `h a` and
   the prescribed map to `Y`. Correct `a` by `ε = -δ ∘ a₀* r`.
   On functions and log sections the resulting difference is
   `ε ∘ a₀* u = -δ`, since `r u = 1`. Square-zero multiplication gives
   `(1+s)(1+t) = 1+s+t`, so the corrected lift lies over `Y`.
5. Apply `lem-per-etale-local-infinitesimal-lifts-smooth` to `U → Y`.
   Finally `lem-trf-etale-source-smoothness` descends smoothness at the point
   from `U` to `X`, giving an open neighborhood on which `h` is smooth. -/
theorem smooth_near_of_strict_logCotangent_injective
    {S X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X S) (g : EtaleLogHom Y S) (h : EtaleLogHom X Y)
    (hover : h.CompEq g f) (hf : f.IsLogSmooth) (hg : g.IsLogSmooth)
    (hstrict : h.IsStrict) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme) (hinj : IsLogCotangentInjective f g h t) :
    ∃ U : X.scheme.Opens,
      (Scheme.SpecToEquivOfField Ω X.scheme t).1 ∈ U ∧ Smooth (U.ι ≫ h.base) := by
  sorry

end AlgebraicGeometry.EtaleLogHom
