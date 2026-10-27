/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum

/-!
# Coherent ideals with fine charts

Source: ILO, Exposé VIII 3.3.7 (blueprint: def-trf-fs-log-blowup).

The existing fs constructions are retained by public import. Coherence of an ideal
on a fine log structure needs finitely generated integral charts, without saturation.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A chart's finite elements generate the log ideal on every geometric stalk.
Source: ILO VIII 3.3.7 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.ChartGeneratesIdeal {X : Scheme.{u}} (M : EtaleLogStructure X)
    (I : M.IdealFamily) (W : X.Etale) {P : Type u} [CommMonoid P]
    (β : P →* M.monoidSheaf.obj.obj (op W)) (E : Finset P) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (w : (Scheme.pointSmallEtale t).fiber.obj W),
    M.idealStalk I t = {m | ∃ p ∈ E, ∃ n : M.toEtalePrelogStructure.stalk t,
      M.toEtalePrelogStructure.germ t W w (β p) * n = m}

/-- Nonempty coherent log ideals on fine log schemes. This is the chart-local
coherence condition, with finitely generated integral monoids and no saturation.
The recorded fs-only predicate remains available for existing consumers.
Source: ILO VIII 3.3.7 (blueprint: def-trf-fs-log-blowup). -/
def EtaleLogStructure.IsNonemptyFineCoherentIdeal {X : Scheme.{u}}
    (M : EtaleLogStructure X) (I : M.IdealFamily) : Prop :=
  M.IsIdeal I ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    ∃ (W : X.Etale) (_w : (Scheme.pointSmallEtale t).fiber.obj W)
      (P : Type u) (_ : CommMonoid P) (β : P →* M.monoidSheaf.obj.obj (op W))
      (E : Finset P), Monoid.FG P ∧
        Function.Injective (Algebra.GrothendieckGroup.of (M := P)) ∧
        M.IsChart W β ∧ E.Nonempty ∧ M.ChartGeneratesIdeal I W β E

end AlgebraicGeometry
