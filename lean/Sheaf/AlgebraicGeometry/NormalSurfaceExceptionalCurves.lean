/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.ReducedNormalization
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ComponentwiseNormalizationAffineCharts
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import Sheaf.AlgebraicGeometry.NormalModificationCodimensionOne
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.RingTheory.FibrePrimesResidueFields
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Exceptional curves of a normal excellent surface modification

Source: Stacks Project, Resolution of Surfaces, Tag 0BBT, first, second and fourth
proof paragraphs; supporting Tags 0BFP, 0A21(6), and 00PD
(blueprint: lem-per-normal-surface-exceptional-curves).

## Main definitions and statements

* `Scheme.Hom.exceptionalCurves` is the set of contracted integral closed curves.
* `normal_surface_exceptional_curves` gives normalization, finiteness, the isomorphism
  criterion, and the local-ring and residue-field properties of these curves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The exceptional curves of `h` are irreducible closed supports of dimension one with
singleton image. Each support carries its unique reduced induced closed scheme structure,
so it specifies an integral closed subscheme without counting isomorphic presentations
more than once. Source: Stacks Project, Tag 0BBT, second proof paragraph
(blueprint: lem-per-normal-surface-exceptional-curves). -/
def Scheme.Hom.exceptionalCurves {Z X : Scheme.{u}} (h : Z ⟶ X) :
    Set (IrreducibleCloseds Z) :=
  {C | topologicalKrullDim (C : Set Z) = 1 ∧ ∃ x : X, h '' (C : Set Z) = {x}}

/-- Finite exceptional-curve data for a proper birational modification of a normal
excellent Noetherian integral surface. Function-field maps are the actual generic stalk
maps transported along the displayed equality of generic points. The common fraction
field in the local assertion is `k(Z)`, with the target stalk acting through the actual
stalk map and the canonical inclusion of the source stalk into `k(Z)`.

Source: Stacks Project, Tag 0BBT, first two and fourth proof paragraphs; supporting
Tags 0BFP, 0A21(6), and 00PD
(blueprint: lem-per-normal-surface-exceptional-curves).

Proof:
1. Properness makes `Y` finite type over Noetherian `X`, hence Noetherian. Excellence
   of every affine coordinate ring of `Y` follows from finite-type stability and the
   affine-cover criterion (`lem-exc-finite-type-localization-excellent`,
   `lem-trf-excellent-scheme-affine-cover`, `lem-weil-pbc-finite-type-over-noetherian`).
2. Integrality identifies componentwise normalization with function-field normalization.
   Excellent normalization preparation makes the normalization finite, normal,
   Noetherian and excellent (`lem-per-excellent-normalization-preparation`).
3. Its affine integral-closure charts are domains between a domain and its fraction
   field, hence have the same fraction field. Their generic points glue, giving
   integrality and birationality (`lem-per-componentwise-normalization-affine-charts`,
   `lem-sc-integral-function-field-affine-fraction`).
4. Finite morphisms are proper and proper morphisms compose. The closed dominant
   dimension formula gives dimension two. Over normal `Y` the finite birational
   normalization is an isomorphism (`lem-weil-pbc-finite-proper`,
   `lem-weil-pbc-proper-composition`, `lem-trf-closed-dominant-dimension`,
   `lem-trf-finite-birational-normal-iso`).
5. Affine stalk localization identifies local dimension with lengths of chains of
   generizations. All such chains on either surface have length at most two
   (`lem-weil-pbc-affine-open-stalk-localization`,
   `lem-weil-pbc-localization-prime-residue-field-iso`, `lem-sc-scheme-sober`).
6. Stalks are Noetherian normal local domains; a one-dimensional such stalk is a DVR
   (`lem-weil-pbc-localization-noetherian`, `lem-sc-normal-dim1-dvr`).
7. The normal modification theorem gives an isomorphism open containing all points
   of local dimension zero or one, and all points with finite fibre
   (`lem-per-normal-modification-codimension-one`).
8. Every point of its closed complement is closed, since a further specialization
   would give a chain of length three. Its finitely many irreducible components are
   therefore singletons (`lem-sc-noetherian-closed-subset-finite-components`).
9. Properness makes every contracted curve's image point closed. Such a point lies
   outside the isomorphism open, since an isomorphism cannot contract a curve.
10. Each exceptional fibre is a proper closed subset of the integral surface, hence
    has dimension at most one. Its one-dimensional irreducible closed subsets are
    components, so there are finitely many; the exceptional set is finite by step 8.
11. If there are no exceptional curves, all exceptional fibres have dimension zero
    and finitely many points. The normal modification theorem then makes the
    complement empty. Conversely an isomorphism contracts no curve.
12. A curve's generic stalk has dimension one: a longer generization chain followed
    by a proper specialization in the curve would have length three. Step 6 gives
    the DVR assertion (`lem-sc-normal-dim1-dvr`).
13. Scheme stalk maps are local. Stalks inject into their generic stalks with the
    same fraction field, by affine localization. Naturality and the generic stalk
    isomorphism make the actual target-to-source stalk map injective and give the
    common fraction field (`lem-sc-integral-function-field-affine-fraction`).
14. In the finite type fibre over the contraction point the curve has dimension one.
    The dimension/transcendence-degree theorem gives residue transcendence degree one;
    the fibre residue-field identification preserves this extension
    (`lem-sc-closed-irreducible-dimension-trdeg`,
    `lem-sfb-finite-type-composition-base-change`,
    `lem-weil-pbc-fibre-ring-primes-residue-fields`). -/
theorem normal_surface_exceptional_curves
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X]
    (hnormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hexcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hdim : topologicalKrullDim X = 2)
    (f : Y ⟶ X) [IsProper f]
    (hgeneric : f (genericPoint Y) = genericPoint X)
    (hbirational : Function.Bijective
      ((X.presheaf.stalkCongr (Inseparable.of_eq hgeneric)).inv ≫
        f.stalkMap (genericPoint Y) : X.functionField ⟶ Y.functionField)) :
    IsFinite Y.fromNormalization ∧ IsProper Y.fromNormalization ∧
    IsIntegral Y.normalization ∧ IsNoetherian Y.normalization ∧
    (∀ z : Y.normalization,
      IsIntegrallyClosed (Y.normalization.presheaf.stalk z)) ∧
    (∀ U : Y.normalization.affineOpens, IsExcellent Γ(Y.normalization, U)) ∧
    topologicalKrullDim Y.normalization = 2 ∧
    IsProper (Y.fromNormalization ≫ f) ∧
    (∃ hg : (Y.fromNormalization ≫ f) (genericPoint Y.normalization) = genericPoint X,
      Function.Bijective
        ((X.presheaf.stalkCongr (Inseparable.of_eq hg)).inv ≫
          (Y.fromNormalization ≫ f).stalkMap (genericPoint Y.normalization) :
            X.functionField ⟶ Y.normalization.functionField)) ∧
    ((∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsIso Y.fromNormalization) ∧
    (Y.fromNormalization ≫ f).exceptionalCurves.Finite ∧
    (∀ C ∈ (Y.fromNormalization ≫ f).exceptionalCurves, ∀ x : X,
      (Y.fromNormalization ≫ f) '' (C : Set Y.normalization) = {x} →
        IsClosed ({x} : Set X)) ∧
    (IsIso (Y.fromNormalization ≫ f) ↔
      (Y.fromNormalization ≫ f).exceptionalCurves = ∅) ∧
    (∀ C ∈ (Y.fromNormalization ≫ f).exceptionalCurves,
      ∀ η : Y.normalization, IsGenericPoint η (C : Set Y.normalization) →
        IsDiscreteValuationRing (Y.normalization.presheaf.stalk η) ∧
        IsLocalHom ((Y.fromNormalization ≫ f).stalkMap η).hom ∧
        Function.Injective ((Y.fromNormalization ≫ f).stalkMap η) ∧
        IsFractionRing (Y.normalization.presheaf.stalk η) Y.normalization.functionField ∧
        @IsFractionRing (X.presheaf.stalk ((Y.fromNormalization ≫ f) η)) _
          Y.normalization.functionField _
          (((algebraMap (Y.normalization.presheaf.stalk η) Y.normalization.functionField).comp
            ((Y.fromNormalization ≫ f).stalkMap η).hom).toAlgebra) ∧
        @Algebra.trdeg (X.residueField ((Y.fromNormalization ≫ f) η))
          (Y.normalization.residueField η) _ _
          (((Y.fromNormalization ≫ f).residueFieldMap η).hom.toAlgebra) = 1) := by
  sorry

end AlgebraicGeometry
