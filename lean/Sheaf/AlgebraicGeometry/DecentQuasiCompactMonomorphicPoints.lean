module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Quasi-compact monomorphic field representatives

Source: Stacks Project, Decent Spaces, Tag 03JV (lemma-UR-finite-above-x),
implication (6) to (4), pointwise; Tag 03I8 (definition-very-reasonable)
(blueprint: lem-sfb-decent-quasicompact-monomorphic-points).

Quasi-compactness is expanded using the node's affine scheme tests. The pullback is
represented by an actual scheme, whose underlying space is quasi-compact. Monomorphism
is tested on morphisms from every algebraic space over the original base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- If every field-valued morphism to an algebraic space is quasi-compact, then every
point admits a quasi-compact monomorphic field representative. The point set and its
representatives are the existing `Point` and `schemePointMap`; no atlas is chosen.
Source: Stacks Project, Decent Spaces, Tag 03JV (6) to (4), and Tag 03I8
(blueprint: lem-sfb-decent-quasicompact-monomorphic-points).

Proof:
1. By [lem-sfb-space-change-base-to-integers], view `X` over `Spec ℤ`. The sigma
   formula preserves field representatives, point classes and scheme fibre products.
   Every affine test acquires its map to `S`, so the hypothesis transfers unchanged.
2. Choose a point-surjective scheme atlas `V → X` by
   [lem-a1-space-affine-etale-cover], and a point `v` above `x`. Let `L = κ(v)` and
   `T = Spec L`. Its map `i : T → V` is the residue-field map of
   [lem-weil-pbc-morphism-from-spec-field], monomorphic by
   [lem-sfb-residue-field-point-monomorphism]. The composite `b : T → X` represents
   `x` by [def-a1-algebraic-space-point-classes]. The representable diagonal gives
   schemes `P = T ×_X V` and `H = T ×_X T`; `P → T` is étale and `H` is
   quasi-compact by the hypothesis, tested against the affine `T → X` itself.
3. The map `H → P`, sending `(t₁,t₂)` to `(t₁,i(t₂))`, is monomorphic because `i`
   is. By [lem-weil-pbc-etale-fibre-discrete-separable-points], `P` is a disjoint
   union of spectra of finite separable extensions of `L`. Apply
   [lem-sfb-monomorphism-into-field-coproduct]: `H` is a union of its components.
   The squares and their universal properties are those of
   [lem-trf-space-fibre-products-etale-covers].
4. Quasi-compactness makes this union finite. Its inclusion into `P` is open;
   [lem-weil-pbc-etale-composition-cancellation] gives étaleness of `H → T`.
   It is quasi-compact since `T` has only two opens. Swapping the factors gives the
   same properties for the other projection.
5. Apply [lem-sfb-finite-point-self-relation-field-monomorphism] to obtain a field
   monomorphism representing `x` over `Spec ℤ`, initially on scheme tests.
   Evaluating two maps from an arbitrary algebraic space on each scheme and each
   section extends cancellation to all algebraic spaces: morphisms are natural
   transformations by [def-trf-algebraic-space].
6. Restore the base `S` using [lem-sfb-space-change-base-to-integers]. The
   equivalence preserves the representative's point and its cancellation property.
   The original hypothesis makes this field map quasi-compact on every affine
   scheme test. If `Point X.obj.obj` is empty, there is no `x` to consider. -/
theorem exists_quasiCompact_monomorphic_field_representative
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : ∀ (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
      (c : yoneda.obj (Over.mk b) ⟶ X.obj.obj) (U : Over S), IsAffine U.left →
      ∀ t : yoneda.obj U ⟶ X.obj.obj,
        ∃ (V : Over S) (p : V ⟶ U) (q : yoneda.obj V ⟶ yoneda.obj (Over.mk b)),
          IsPullback q (yoneda.map p) c t ∧ CompactSpace V.left)
    (x : Point X.obj.obj) :
    ∃ (F : Type u) (_ : Field F) (b : Spec (CommRingCat.of F) ⟶ S)
      (j : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      schemePointMap j (IsLocalRing.closedPoint F) = x ∧
      (∀ (Y : AlgebraicSpace S) (a c : Y.obj.obj ⟶ yoneda.obj (Over.mk b)),
        a ≫ j = c ≫ j → a = c) ∧
      ∀ (U : Over S), IsAffine U.left → ∀ t : yoneda.obj U ⟶ X.obj.obj,
        ∃ (V : Over S) (p : V ⟶ U) (q : yoneda.obj V ⟶ yoneda.obj (Over.mk b)),
          IsPullback q (yoneda.map p) j t ∧ CompactSpace V.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
