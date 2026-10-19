/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import Mathlib.RingTheory.Length
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.RingTheory.LengthOfSupportAtMaximalIdeal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.FlatBaseChange
import WeilConjectures.Blowup.BlowupUniversal

/-!
# Principalization by blowups at regular surface points

Source: Stacks Project, Tag 0AHH, `resolve-lemma-make-ideal-principal`
(blueprint: lem-per-surface-point-ideal-principalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-coherent ideal supported at finitely many regular closed points of dimension two
becomes an effective Cartier ideal, hence an invertible module, after finitely many point
blowups. The maps `a` are the composites to `X`, starting at the isomorphism `e0`; each `b i`
is identified over its target with the canonical blowup of the reduced closed point `p`.
The case `n = 0` is allowed. The support of `I` here is the support of the quotient by `I`.

Source: Stacks Project, Tag 0AHH, `resolve-lemma-make-ideal-principal`
(blueprint: lem-per-surface-point-ideal-principalization).

Proof plan, following the nine steps of the node:
1. The quotient stalks at `T` have finite length: their support lies at the maximal ideal
   because points of `T` are closed. Apply `lem-sc-generic-stalk-finite-length`, handling the
   zero quotient separately, and strongly induct on the sum of these lengths.
2. If the sum is zero, every quotient stalk vanishes, so `I` is the unit ideal. Use the empty
   tower; its generator is the nonzerodivisor 1 and its module is locally free of rank one.
3. Otherwise blow up a point with positive colength. The blowup is Noetherian by
   `lemma-nagata-blowup-proper` and `lem-weil-pbc-finite-type-over-noetherian`. The centre
   extends to an effective Cartier ideal by `thm-nagata-blowup-principalizes-center`; the
   complement is unchanged by `thm-nagata-global-blowup-complement`.
4. Apply `lem-sbc-canonical-stalk-spectrum-flat` and `thm-nagata-blowup-flat-base-change`
   to identify the stalk base change with the maximal-ideal blowup. Then
   `lem-per-local-surface-maximal-blowup-geometry` gives the exceptional projective line
   and regular local rings of dimension two at its closed points.
5. Apply `lem-per-local-surface-weak-transform-colength-drop` to obtain an exceptional
   multiplicity and a residual ideal with smaller total colength on that line.
6. Globalize the ideal inclusion using B_Q = (W⁻¹B)_(W⁻¹Q), where W is the complement
   of the prime of the chosen point. Off the exceptional divisor the inclusion is automatic.
   Divide locally by a power of a nonzerodivisor generator of the exceptional ideal. Changes
   of generator by a unit preserve the residual ideal, so these ideals glue.
7. The same stalk identifications preserve quotient lengths. The residual support consists
   of finitely many closed regular points of dimension two, on the exceptional fibre and at
   the unique lifts of the other points of `T`. Its total colength is strictly smaller.
8. Apply the strong induction hypothesis to the residual ideal and prepend the first blowup.
   Every new centre still maps into the original `T`.
9. Use `lemma-nagata-cartier-total-transform-blowup` at each step to preserve the exceptional
   Cartier ideal. The final extended ideal is its power times the principalized residual
   ideal; a product of nonzerodivisors is a nonzerodivisor. Its local generators identify its
   module with the structure sheaf, proving both asserted conclusions. -/
theorem exists_surface_point_ideal_principalization
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : T.Finite)
    (hclosed : ∀ p ∈ T, IsClosed ({p} : Set X))
    (hregular : ∀ p ∈ T, IsRegularLocalRing (X.presheaf.stalk p))
    (hdim : ∀ p ∈ T, ringKrullDim (X.presheaf.stalk p) = 2)
    (I : X.IdealSheafData) (hsupport : (I.support : Set X) ⊆ T) :
    ∃ (n : ℕ) (Y : Fin (n + 1) → Scheme.{u}) (e0 : Y 0 ≅ X)
      (b : ∀ i : Fin n, Y i.succ ⟶ Y i.castSucc) (a : ∀ i, Y i ⟶ X),
      a 0 = e0.hom ∧
      (∀ i : Fin n, b i ≫ a i.castSucc = a i.succ) ∧
      (∀ i : Fin n, ∃ (p : Y i.castSucc) (hp : IsClosed ({p} : Set (Y i.castSucc))),
        a i.castSucc p ∈ T ∧
        ∃ e : Y i.succ ≅ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowup,
          e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).blowupMap = b i) ∧
      (I.comap (a (Fin.last n))).IsInvertible ∧
      Scheme.Modules.IsInvertible (I.comap (a (Fin.last n))).toModules := by
  sorry

end AlgebraicGeometry
