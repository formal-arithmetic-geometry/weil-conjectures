/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Sheaf.AlgebraicGeometry.Morphisms.GeometricallyConnectedFibreNeighbourhood

/-!
# Spreading a geometrically irreducible smooth-fibre open

Source: Stacks Project, Tag 057J (`lemma-normal-morphism-irreducible`), specialized to
smooth morphisms using Tag 056W, as applied in Tag 057K
(blueprint: lem-trf-geometrically-integral-fibre-neighbourhood).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometrically irreducible open in a fibre of a smooth finitely presented morphism
spreads to a quasi-compact open with geometrically integral fibres over an affine elementary
étale neighbourhood. The last equality is in the lattice of opens of the new ambient fibre:
the comparison is the canonical pullback map induced by `a` and its residue-field map,
followed by transport along `hs`. Thus it specifies equality as open subschemes, including
their embeddings, rather than an abstract isomorphism of schemes.

Source: Stacks Project, Tag 057J, smooth specialization via Tag 056W used in Tag 057K
(blueprint: lem-trf-geometrically-integral-fibre-neighbourhood).

Proof:
1. By `lem-pc-smooth-flat` and `sbc-lem-smooth-geometrically-reduced`, smoothness gives
   flatness and geometrically reduced fibres. A geometrically irreducible scheme is nonempty
   and geometrically connected: a partition into two nonempty clopen parts contradicts
   irreducibility after each field extension (`def-pc-geometrically-irreducible`,
   `def-weil-irreducible-components`, `def-weil-connected-scheme`).
2. Apply `lem-trf-geometrically-connected-fibre-open-spreading` (Stacks 055W). It gives the
   affine elementary étale neighbourhood and quasi-compact open with geometrically connected
   fibres and exactly the prescribed open fibre. Retain this neighbourhood and entire open.
3. Smoothness is stable under base change (`lem-pc-proper-base-change`, clause 2) and under
   precomposition with an open immersion (`lem-pc-open-immersion-smooth-composition`), so the
   open's structure map is smooth. No separatedness or Noetherian hypothesis is needed.
4. For any point of the new base and any extension K of its residue field, the corresponding
   base-changed fibre C is smooth over Spec K. Iterated base change (`def-pc-base-change`)
   and step 2 make C geometrically connected and nonempty. Spec K is integral and has local
   ring and function field K (`lem-weil-pbc-spec-domain-stalks-function-field`,
   `def-weil-affine-spectrum`); K is integrally closed in itself.
5. Apply `lem-sbc-smooth-connected-generic-geometry-core` over Spec K, with the identity
   cartesian generic fibre, to conclude C is integral. Since the point and field extension
   were arbitrary, every fibre is geometrically integral. All other clauses and the equality
   of embedded open fibres are those of step 2.
-/
theorem exists_geometricallyIntegral_fibre_neighbourhood {Y S : Scheme.{u}}
    (h : Y ⟶ S) [Smooth h] [LocallyOfFinitePresentation h] [QuasiCompact h]
    [QuasiSeparated h] (s : S) (T : (h.fiber s).Opens)
    [GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ (S₁ : Scheme.{u}) (a : S₁ ⟶ S) (s₁ : S₁) (hs : a s₁ = s),
      IsAffine S₁ ∧ Etale a ∧ IsIso (a.residueFieldMap s₁) ∧
      ∃ V : (pullback h a).Opens,
        IsCompact (V : Set ↥(pullback h a)) ∧
        GeometricallyIntegral (V.ι ≫ pullback.snd h a) ∧
        (pullback.snd h a).fiberι s₁ ⁻¹ᵁ V =
          (pullback.map (pullback.snd h a) (S₁.fromSpecResidueField s₁)
              h (S.fromSpecResidueField (a s₁))
              (pullback.fst h a) (Spec.map (a.residueFieldMap s₁)) a
              (pullback.condition (f := h) (g := a)).symm
              (a.SpecMap_residueFieldMap_fromSpecResidueField s₁).symm ≫
            eqToHom (congrArg h.fiber hs)) ⁻¹ᵁ T := by
  sorry

end AlgebraicGeometry
