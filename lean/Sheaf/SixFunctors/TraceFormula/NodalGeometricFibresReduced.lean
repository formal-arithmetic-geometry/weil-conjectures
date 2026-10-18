/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.RingTheory.GeometricReducednessFiniteInseparableTest
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Nodal geometric curve fibres are geometrically reduced

Source: Stacks Project, `curves.tex`, Tag 0E37 (lemma-facts-about-nodal-curves),
with the completed local model from Tag 0C47
(blueprint: lem-trf-nodal-geometric-fibres-reduced).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The scalar map from the ground field to the completed local ring, obtained from the
structure morphism on stalks and the canonical completion map.
Source: Stacks Project, `curves.tex`, Tag 0C47, the completed geometric local ring as an
algebra over the ground field (blueprint: lem-trf-nodal-geometric-fibres-reduced). -/
noncomputable def Scheme.Hom.nodalCompletedLocalScalar
    {Ω : Type u} [Field Ω] {X : Scheme.{u}} (q : X ⟶ Spec (.of Ω)) (x : X) :
    Ω →+* AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) :=
  (algebraMap (X.presheaf.stalk x) _).comp
    ((q.stalkMap x).hom.comp (StructureSheaf.toStalk Ω (q x)).hom)

/-- A finite-type curve whose algebraically closed base changes have one-dimensional
components and only smooth closed points or ordinary nodal completed local rings is
geometrically reduced. The scalar equation says the nodal ring isomorphism is an
isomorphism of algebras over the geometric ground field.

Source: Stacks Project, `curves.tex`, Tag 0E37, geometric reducedness assertion and proof,
and Tag 0C47 for the completed nodal local model
(blueprint: lem-trf-nodal-geometric-fibres-reduced).

Proof plan, following the five steps of the node:
1. Base change preserves finite type (`lem-weil-pbc-lft-base-change` and the affine charts
   of `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`). The
   result is Noetherian (`lem-weil-pbc-finite-type-over-noetherian`) and Jacobson
   (`lem-sc-lft-over-field-jacobson-space`), so every point specializes to a closed point.
2. Smooth closed points have reduced local rings (`sbc-lem-smooth-geometrically-reduced`).
   The nodal completion embeds in the product of its two power-series axes, which are
   domains (`lem-weil-pbc-power-series-domain`). Completion is faithfully flat
   (`lem-weil-pbc-local-completion-faithfully-flat`) and injective
   (`lem-weil-pbc-faithfully-flat-ideal-contraction`), so the local ring is reduced.
3. Localization from a closed specialization gives reducedness of every stalk, hence of
   the scheme (`def-pc-reduced-scheme`). Empty base changes are reduced as well.
4. On each affine chart, embed a finite purely inseparable extension in an algebraically
   closed field. Flatness over the field (`lem-weil-pbc-module-over-field-flat`) and tensor
   exactness (`lem-weil-pbc-flat-tensor-exact`) give an injection into a reduced ring.
   Apply `lem-trf-geometric-reducedness-finite-inseparable-test` to get every field extension.
5. The open affine fibre-product charts of step 1 are reduced after each field extension;
   `def-pc-reduced-scheme` gives reducedness of the entire base change.
-/
theorem nodal_geometric_fibres_reduced
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of k)),
      IsEmpty ↥(pullback (C := Scheme.{u}) f g) ∨
        ((∀ Z ∈ irreducibleComponents ↥(pullback (C := Scheme.{u}) f g),
            topologicalKrullDim Z = 1) ∧
          ∀ x : ↥(pullback (C := Scheme.{u}) f g),
            x ∈ closedPoints ↥(pullback (C := Scheme.{u}) f g) →
            x ∈ (pullback.snd f g).smoothLocus ∨
              ∃ e : AdicCompletion
                  (IsLocalRing.maximalIdeal ((pullback (C := Scheme.{u}) f g).presheaf.stalk x))
                  ((pullback (C := Scheme.{u}) f g).presheaf.stalk x) ≃+*
                (MvPowerSeries (Fin 2) Ω ⧸
                  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}),
                ∀ a : Ω, e ((pullback.snd f g).nodalCompletedLocalScalar x a) =
                  Ideal.Quotient.mk _ (MvPowerSeries.C a))) :
    GeometricallyReduced f := by
  sorry

end AlgebraicGeometry
