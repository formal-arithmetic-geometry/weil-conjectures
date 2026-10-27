/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric fibre dimension bounds under base change and covering detection

Source: Stacks Project, Morphisms of Spaces, Tags 04NS(1) and 06LR;
Quotients of Groupoids, Tag 0D52; Decent Algebraic Spaces, Tag 0A4J
(blueprint: lem-sfb-space-relative-dimension-base-change).

The base scheme of the big site is arbitrary. A morphism from an algebraic space to
an `S`-scheme is its natural transformation to that scheme's Yoneda presheaf.
All geometric fibres and base changes below are actual presheaf fibre products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The condition `P_d`: every geometric fibre has topological Krull dimension at most `d`.
The fields range over the universe of the big site, and the topology on the point
classes is the existing atlas topology. Empty fibres have dimension bottom.
Source: Stacks Project, Tags 06LR and 0D52, with Tag 0A4J for the topological reading
on quasi-separated geometric fibres (blueprint: lem-sfb-space-relative-dimension-base-change).
-/
def GeometricFibreDimensionLE {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (T : Over S) (f : F ⟶ yoneda.obj T) (d : ℕ) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T.left),
    topologicalKrullDim (Point (Limits.pullback f (yoneda.map (Over.homMk
      (U := Over.mk (a ≫ T.hom)) (V := T) a rfl)))) ≤ (d : WithBot ℕ∞)

/-- Geometric fibre dimension bounds are preserved by arbitrary scheme base change
and detected by every jointly surjective family of scheme maps.
Source: Stacks Project, Tags 04NS(1), 06LR and 0D52, with Tag 0A4J
(blueprint: lem-sfb-space-relative-dimension-base-change).

Proof:
1. The diagonal after any scheme base change is a pullback of the original diagonal.
   Quasi-compactness is preserved by `lem-pc-quasi-compact-base-change`. Pulling back
   an atlas uses `lem-trf-space-fibre-products-etale-covers`; its chart composites
   remain locally finite type by `lem-weil-pbc-lft-base-change`. Thus all geometric
   fibres are quasi-separated and locally of finite type over their fields.
2. Pullback associativity identifies each geometric fibre of the base change with
   the fibre of the original map at the composite geometric point. The isomorphism
   identifies atlas topologies and chains of irreducible closed subsets, proving
   the forward implication using `def-kun-topological-krull-dimension`.
3. For a quasi-separated space locally of finite type over a field, an étale atlas
   and its pullback compute topological dimension by
   `lem-sfb-quasiseparated-space-atlas-dimension`. Apply
   `lem-sc-fibre-dimension-after-base-change` to the atlas over the one-point field
   spectra. Its local topological dimensions agree before and after field extension.
   The projection is surjective by `lem-pc-field-extension-surjective` and
   `lem-weil-pbc-surjective-base-change`. The supremum formula
   `lem-weil-pbc-dimension-supremum-local-dimensions`, with the local dimension
   conventions `def-kun-dimension` and `def-kun-topological-dimension-at-point`,
   gives equality of global dimensions, also for the empty atlas.
4. To detect the bound at Spec Ω → T, choose a covering point over its image.
   The residue-field maps of `def-weil-residue-field` and
   `lem-weil-common-extension-fields` embed Ω and the covering residue field into
   a common field over the base residue field. Enlarge it to an algebraically
   closed field by `def-weil-algebraic-closure`. Pullback associativity identifies
   the extended original fibre with a geometric fibre of the chosen covering
   base change, which has the bound. Step 3 descends that bound back to Ω.
   An empty jointly surjective family forces the target empty, so the geometric
   point assertion is vacuous. No nonemptiness or equidimensionality is needed.
-/
theorem geometricFibreDimensionLE_baseChange_and_descent
    {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hft : MapToSchemeIsLocally (@LocallyOfFiniteType) X T f)
    (hqs : MapIsQuasiCompact (Limits.pullback.diagonal f)) (d : ℕ) :
    (GeometricFibreDimensionLE T f d →
      ∀ (T' : Over S) (g : T' ⟶ T),
        GeometricFibreDimensionLE T' (Limits.pullback.snd f (yoneda.map g)) d) ∧
    (∀ (I : Type w) (Tᵢ : I → Over S) (g : ∀ i : I, Tᵢ i ⟶ T),
      (∀ t : T.left, ∃ (i : I) (tᵢ : (Tᵢ i).left), (g i).left tᵢ = t) →
      (∀ i : I, GeometricFibreDimensionLE (Tᵢ i) (Limits.pullback.snd f (yoneda.map (g i))) d) →
      GeometricFibreDimensionLE T f d) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
