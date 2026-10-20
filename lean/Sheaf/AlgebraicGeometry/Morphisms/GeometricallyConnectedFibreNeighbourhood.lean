/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus
import Sheaf.AlgebraicGeometry.Morphisms.CohenMacaulayClosedPointSlice
import Sheaf.TraceFormula.FiniteLocallyFreeMultisectionConnectedOpen
import Sheaf.TraceFormula.FlatLFPCMLocusFibreDense
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import WeilConjectures.AlgebraicGeometry.FinitePiecePersistence
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-! # Spreading a geometrically connected fibre open

Source: Stacks Project, more-morphisms.tex, Tag 055W, label
`lemma-fibre-geometrically-connected-reduced` (blueprint:
`lem-trf-geometrically-connected-fibre-open-spreading`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometrically connected open in a geometrically reduced flat finitely presented family
spreads to a quasi-compact open with geometrically connected fibres over an affine elementary
étale neighbourhood.

Source: Stacks Project, more-morphisms.tex, Tag 055W,
`lemma-fibre-geometrically-connected-reduced`.
Proof: first shrink the base to an affine neighbourhood and lift the prescribed fibre open to a
quasi-compact open.  Choose a Cohen--Macaulay point in that fibre and use the flat
quasifinite slice and the elementary étale finite-piece lemma to obtain a finite locally free
multisection.  The finite-locally-free multisection connected-open lemma then gives an open
with geometrically connected fibres and the prescribed special fibre.  Finally shrink to the
open image so that all fibres are nonempty, and then to an affine neighbourhood; flatness,
finite presentation, geometric reducedness, quasi-compactness, and the embedded fibre equality
are preserved by these restrictions and base changes.  The cited DAG nodes provide each step.
(blueprint: lem-trf-geometrically-connected-fibre-open-spreading) -/
theorem exists_geometricallyConnected_fibre_neighbourhood
    {Y S : Scheme.{u}} (h : Y ⟶ S) [Flat h]
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]
    [GeometricallyReduced h] (s : S) (T : (h.fiber s).Opens)
    [GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ (S₁ : Scheme.{u}) (a : S₁ ⟶ S) (s₁ : S₁) (hs : a s₁ = s),
      IsAffine S₁ ∧ Etale a ∧ IsIso (a.residueFieldMap s₁) ∧
      ∃ V : (pullback h a).Opens,
        IsCompact (V : Set ↥(pullback h a)) ∧
        GeometricallyConnected (V.ι ≫ pullback.snd h a) ∧
        (pullback.snd h a).fiberι s₁ ⁻¹ᵁ V =
          (pullback.map (pullback.snd h a) (S₁.fromSpecResidueField s₁)
              h (S.fromSpecResidueField (a s₁))
              (pullback.fst h a) (Spec.map (a.residueFieldMap s₁)) a
              (pullback.condition (f := h) (g := a)).symm
              (a.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm ≫
            eqToHom (congrArg h.fiber hs)) ⁻¹ᵁ T := by
  sorry

end AlgebraicGeometry
