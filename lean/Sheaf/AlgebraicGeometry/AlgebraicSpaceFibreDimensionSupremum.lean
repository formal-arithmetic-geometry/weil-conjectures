/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalFibreDimensionOpen
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Fibre dimension as a supremum of local relative dimensions

Source: Stacks Project, More on Morphisms of Spaces, Tag 0D4M,
lemma-dimension-fibre, scheme-target case; Properties of Spaces, Tags 04N5 and 04N6
(blueprint: lem-sfb-space-fibre-dimension-supremum).

The structural morphism of `X : AlgebraicSpace T` is the given morphism to `T`.
Over `T`, the fibre product with the residue-field spectrum is the product of presheaves:
`h_T` is terminal. Dimensions are computed on scheme charts, never on the point space.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The residue-field fibre, as a presheaf on schemes over the original base.
The product is over the terminal presheaf `h_T`, hence is `X ×_T Spec κ(t)`.
Source: Stacks, Tag 0D4M, scheme-target reduction
(blueprint: lem-sfb-space-fibre-dimension-supremum). -/
noncomputable def residueFibrePresheaf {T : Scheme.{u}} (X : AlgebraicSpace T) (t : T) :
    (Over T)ᵒᵖ ⥤ Type u :=
  Limits.prod X.obj.obj (yoneda.obj (Over.mk (T.fromSpecResidueField t)))

/-- A point lies over `t` if a field-valued representative has image `t` in the base.
This is the condition `f(x) = t`, expressed without choosing a representative.
Source: Stacks, Properties of Spaces, Tag 03BU; More on Morphisms of Spaces, Tag 0D4M
(blueprint: lem-sfb-space-fibre-dimension-supremum). -/
def pointLiesOver {T : Scheme.{u}} (X : AlgebraicSpace T) (t : T)
    (x : Point X.obj.obj) : Prop :=
  ∃ r : PointRepresentative X.obj.obj,
    Quot.mk _ r = x ∧ r.base (IsLocalRing.closedPoint r.K) = t

/-- The fibre chart dimension is the supremum of local relative dimensions over its
points, is finite or bottom, and is attained at a point precisely in the nonempty case.
The affine-chart suprema below are the node's `n_f(t)`; `localFibreDimension` is its
already constructed `δ_f(x)`.
Source: Stacks, More on Morphisms of Spaces, Tag 0D4M, lemma-dimension-fibre;
Properties of Spaces, Tags 04N5 and 04N6
(blueprint: lem-sfb-space-fibre-dimension-supremum).

Proof:
1. Around `t` choose an affine open `V` of `T`. Quasi-compactness gives a quasi-compact
   scheme atlas of `X ×_T V`; lem-trf-space-qc-finite-affine-atlas-refinement refines it
   to a surjective affine étale atlas `U`. The composite `U → X` is étale by
   lem-weil-pbc-etale-composition-cancellation. Local finite type on charts gives that
   `U → V` is locally of finite type. Its residue-field fibre `P` is affine by
   lem-weil-pbc-fibre-product-affine-spectra and locally of finite type by
   lem-weil-pbc-lft-base-change. It is quasi-compact by lem-weil-pbc-affine-scheme-qcqs,
   hence finite type over the residue field. Base change gives a surjective étale
   atlas `P → X_t` by lem-trf-space-fibre-products-etale-covers.
2. Every point `x` over `t` lifts to `u` in the atlas by lem-a1-space-point-open-calculus.
   The scheme fibre homeomorphism gives the unique `p` of `P` above `u`. For another
   chart `W,w` above `x`, the scheme `U ×_X W` has a point above `u,w` by that same point
   calculus. On residue-field fibres both projections are étale. Applying
   lem-sfb-etale-topological-dimension-at-point twice identifies their local dimensions.
   Thus every chart value at `x` equals `dim_p P`, so their supremum `δ_f(x)` does too.
3. For any affine étale chart `B → X_t`, lift each `b` to `B ×_{X_t} P`. Étale invariance
   gives `dim_b B = dim_p P ≤ dim P`. By
   lem-weil-pbc-dimension-supremum-local-dimensions, `dim B ≤ dim P`. Since `P` itself
   is a chart, the supremum of all affine chart dimensions equals `dim P`.
4. The local dimensions of points of `P` and the values `δ_f(x)` over `t` have the same
   range by step 2. Their suprema agree, and the same dimension-supremum lemma identifies
   both with `dim P`, giving the displayed equality.
5. By lem-kun-dimension-finite-type, `P` has finite dimension. When nonempty, its local
   dimensions form a nonempty bounded set of natural numbers and have a largest value.
   Steps 2 and 4 give a point `x` attaining that finite dimension. The surjective atlas
   and point lifting say that `X_t` is empty exactly when no `x` lies over `t`. In this
   case every chart is empty, its dimension is bottom, and both suprema are bottom.
No separation, properness, flatness, finite presentation, or Noetherian assumption is used. -/
theorem fibre_dimension_eq_supremum {T : Scheme.{u}} (X : AlgebraicSpace T)
    (hft : ∀ (U : Over T) (a : yoneda.obj U ⟶ X.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom)
    (hqc : ∀ (V : Over T), CompactSpace V.left →
      ∃ (U : Over T) (a : yoneda.obj U ⟶ Limits.prod X.obj.obj (yoneda.obj V)),
        CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (t : T) :
    ((⨆ (U : Over T) (_ : IsAffine U.left)
        (a : yoneda.obj U ⟶ residueFibrePresheaf X t) (_ : IsEtale a),
          topologicalKrullDim U.left) =
      ⨆ (x : Point X.obj.obj) (_ : pointLiesOver X t x), localFibreDimension X x) ∧
    (IsEmpty (Point (residueFibrePresheaf X t)) ↔
      ¬ ∃ x : Point X.obj.obj, pointLiesOver X t x) ∧
    (IsEmpty (Point (residueFibrePresheaf X t)) →
      (⨆ (U : Over T) (_ : IsAffine U.left)
        (a : yoneda.obj U ⟶ residueFibrePresheaf X t) (_ : IsEtale a),
          topologicalKrullDim U.left) = ⊥ ∧
      (⨆ (x : Point X.obj.obj) (_ : pointLiesOver X t x), localFibreDimension X x) = ⊥) ∧
    (Nonempty (Point (residueFibrePresheaf X t)) →
      ∃ (d : ℕ) (x : Point X.obj.obj), pointLiesOver X t x ∧
        localFibreDimension X x = (d : WithBot ℕ∞) ∧
        (⨆ (U : Over T) (_ : IsAffine U.left)
          (a : yoneda.obj U ⟶ residueFibrePresheaf X t) (_ : IsEtale a),
            topologicalKrullDim U.left) = (d : WithBot ℕ∞)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
