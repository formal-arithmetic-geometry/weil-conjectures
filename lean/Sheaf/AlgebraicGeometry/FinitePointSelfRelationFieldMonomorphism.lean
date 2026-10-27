/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# A finite self-relation gives a field monomorphism

Source: Stacks Project, Decent Spaces, Tag 03JU (lemma-R-finite-above-x),
implication (3) to (4)
(blueprint: lem-sfb-finite-point-self-relation-field-monomorphism).

The scheme `R` and its two projections represent the self-fibre product by their
Yoneda pullback square. Point equality uses the existing field-valued point classes.
The lifted integer spectrum is the terminal scheme in the chosen universe.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A field-valued point with étale quasi-compact self-relation projections admits a
monomorphic field-valued representative of the same point class. Monomorphy is the
injectivity on sections over every test scheme. No quasi-compactness of `j` is asserted.
Source: Stacks Project, Decent Spaces, Tag 03JU (lemma-R-finite-above-x), (3) to (4)
(blueprint: lem-sfb-finite-point-self-relation-field-monomorphism).

Proof:
1. By the representing pullback square [lem-trf-space-fibre-products-etale-covers],
`R(T)` is the set of pairs of maps to `Spec L` with equal image in `X(T)`. This is an
étale equivalence relation, by the two étaleness hypotheses [def-trf-algebraic-space].
2. Apply [lem-trf-etale-relation-quotient]. Its quotient `Y` is an algebraic space with
surjective étale atlas `q : Spec L → Y` and relation `R`. The equality `b s = b t`
gives a factorization `b = q ≫ i` with `i : Y → X` by its quotient universal property.
3. To prove `i` monic, lift two sections of `Y` with equal image in `X` on a common
étale covering using the quotient's local lifting clause. Their lifts are related by
`R`, hence have equal image in `Y`; sheaf separation gives equality of the sections.
4. The scheme `Spec L` is affine, hence quasi-separated
[lem-weil-pbc-affine-scheme-qcqs]. The relation projections are quasi-compact, so
[lem-sfb-space-qs-atlas-criterion] makes `Y` quasi-separated in the absolute sense.
5. Apply [lem-sfb-pointlike-quasiseparated-space-field] to `q`. It identifies `Y` with
`Spec k` for a subfield of `L`. Composing with `i` gives the asserted monomorphism.
The factorization of `b` through the inclusion of fields proves equality of the point
classes [def-a1-space-point-topology], without asserting quasi-compactness of `j`. -/
theorem finite_point_self_relation_field_monomorphism
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (L : Type u) [Field L]
    (b : yoneda.obj (Over.mk (specULiftZIsTerminal.from (Spec (CommRingCat.of L)))) ⟶
      X.obj.obj)
    (R : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (s t : R ⟶ Over.mk (specULiftZIsTerminal.from (Spec (CommRingCat.of L))))
    (hR : IsPullback (yoneda.map s) (yoneda.map t) b b)
    (hs : Etale s.left) (ht : Etale t.left)
    (hsc : QuasiCompact s.left) (htc : QuasiCompact t.left) :
    ∃ (k : Type u) (_ : Field k)
      (j : yoneda.obj (Over.mk (specULiftZIsTerminal.from (Spec (CommRingCat.of k)))) ⟶
        X.obj.obj),
      (∀ T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))),
        Function.Injective (j.app (op T))) ∧
      (Quot.mk _ (⟨k, specULiftZIsTerminal.from (Spec (CommRingCat.of k)),
        yonedaEquiv j⟩ : PointRepresentative X.obj.obj) : Point X.obj.obj) =
      Quot.mk _ (⟨L, specULiftZIsTerminal.from (Spec (CommRingCat.of L)),
        yonedaEquiv b⟩ : PointRepresentative X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
