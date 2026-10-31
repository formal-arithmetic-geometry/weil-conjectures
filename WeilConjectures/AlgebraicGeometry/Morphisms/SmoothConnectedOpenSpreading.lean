/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.Morphisms.GeometricallyConnectedFibreNeighbourhood

/-! # Spreading a geometrically connected open in a smooth fibre

Source: Stacks Project, more-morphisms.tex, Tag 055W (smooth specialization), and the
first two proof sentences of Tag 057J; morphisms.tex, Tags 01VB, 01VC and 01VA
(blueprint: lem-trf-smooth-connected-open-spreading).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometrically connected open in a smooth finitely presented family spreads to a
quasi-compact smooth open family with geometrically connected fibres over an affine elementary
étale neighbourhood, with the prescribed special fibre as an embedded open subscheme.

Source: Stacks Project, more-morphisms.tex, Tag 055W,
`lemma-fibre-geometrically-connected-reduced`, smooth specialization; Tag 057J,
`lemma-normal-morphism-irreducible`, first two proof sentences; morphisms.tex,
Tags 01VB, 01VC and 01VA.

Proof: (1) Use `sbc-lem-smooth-criterion` to obtain flatness of `h` and
`sbc-lem-smooth-geometrically-reduced` to obtain geometrically reduced fibres.
The finite-presentation hypotheses are already given.
(2) Apply `lem-trf-geometrically-connected-fibre-open-spreading` to `h`, `s` and `T`.
This gives the affine elementary étale neighbourhood and a quasi-compact open `V`,
geometrically connected over the neighbourhood, with the stated embedded fibre equality.
(3) By the smooth clause of `lem-pc-proper-base-change`, the second projection of
`pullback h a` is smooth (Tag 01VB); no properness is required by that clause.
(4) Its composite with the open immersion `V.ι` is smooth by
`lem-pc-open-immersion-smooth-composition` (Tags 01VC and 01VA). This supplies the
remaining conclusion while preserving the fibre equality from step (2).
(blueprint: lem-trf-smooth-connected-open-spreading) -/
theorem exists_smooth_geometricallyConnected_fibre_neighbourhood
    {Y S : Scheme.{u}} (h : Y ⟶ S) [Smooth h]
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]
    (s : S) (T : (h.fiber s).Opens)
    [GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ (S₁ : Scheme.{u}) (a : S₁ ⟶ S) (s₁ : S₁) (hs : a s₁ = s),
      IsAffine S₁ ∧ Etale a ∧ IsIso (a.residueFieldMap s₁) ∧
      ∃ V : (pullback h a).Opens,
        IsCompact (V : Set ↥(pullback h a)) ∧
        Smooth (V.ι ≫ pullback.snd h a) ∧
        GeometricallyConnected (V.ι ≫ pullback.snd h a) ∧
        (pullback.snd h a).fiberι s₁ ⁻¹ᵁ V =
          (pullback.map (pullback.snd h a) (S₁.fromSpecResidueField s₁)
              h (S.fromSpecResidueField (a s₁))
              (pullback.fst h a) (Spec.map (a.residueFieldMap s₁)) a
              (pullback.condition (f := h) (g := a)).symm
              (a.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm ≫
            eqToHom (congrArg h.fiber hs)) ⁻¹ᵁ T := by
  obtain ⟨S₁, a, s₁, hs, hS₁, ha, hκ, V, hV, hconn, hfiber⟩ :=
    exists_geometricallyConnected_fibre_neighbourhood h s T
  exact ⟨S₁, a, s₁, hs, hS₁, ha, hκ, V, hV, inferInstance, hconn, hfiber⟩

end AlgebraicGeometry
