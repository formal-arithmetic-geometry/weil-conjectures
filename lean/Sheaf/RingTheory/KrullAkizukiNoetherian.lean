/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Finite.Basic

/-!
# Krull–Akizuki Noetherianity for intermediate rings

Source: Stacks Project, Algebra, Lemma 10.119.12 (Tag 00PG)
(blueprint: lem-sc-krull-akizuki-noetherian).
-/

universe uR uD uK uL

/-- An intermediate ring between a one-dimensional Noetherian domain and a finite
field extension is Noetherian.
Source: Stacks Project, Algebra, Lemma 10.119.12 (Tag 00PG).

Proof (the node's two steps):
1. Given a nonzero ideal `I` of `D`, choose nonzero `a ∈ I`. Its minimal
   polynomial over `K` has nonzero constant coefficient. Clearing denominators
   gives a polynomial relation over `R` with nonzero constant coefficient;
   the remaining terms belong to `I`, so this coefficient lies in `I ∩ R`.
   The zero ideal is already finitely generated.
2. For nonzero `x ∈ I ∩ R`, choose a finite `K`-basis of `L` and view `D` as
   an `R`-submodule of a finite direct sum of copies of `K`. By
   `lem-sc-finite-length-global-submodule`, `D/xD` has finite length over `R`.
   Its submodule `I/xD` therefore has finite length and finitely many
   `R`-generators. Lift these generators to `I` and adjoin `x`; since `R` is
   contained in `D`, these generate `I` as a `D`-ideal. Thus `D` is Noetherian.
(blueprint: lem-sc-krull-akizuki-noetherian). -/
theorem krullAkizukiNoetherian
    {R : Type uR} {D : Type uD} {K : Type uK} {L : Type uL}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing D] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra R D] [Algebra D L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R D L]
    (hRD : Function.Injective (algebraMap R D))
    (hDL : Function.Injective (algebraMap D L))
    (hdim : ringKrullDim R = 1) :
    IsNoetherianRing D := by
  sorry
