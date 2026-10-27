/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion

/-!
# Closed field subspaces at closed points of decent algebraic spaces

Source: Stacks Project, Decent Spaces, Tag 0AHB (lemma-decent-space-closed-point);
decency is Tag 03I8, equivalently Tag 03JV(6)
(blueprint: lem-sfb-decent-closed-point-field-immersion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A closed point of a decent algebraic space is the image of a representable closed
immersion from a field spectrum. Decency is expanded as the affine scheme-test
quasi-compactness of every field-valued morphism. The conclusion tests all schemes.
Source: Stacks Project, Decent Spaces, Tag 0AHB; Tags 03I8 and 03JV(6)
(blueprint: lem-sfb-decent-closed-point-field-immersion).
Proof:
1. By [lem-sfb-decent-quasicompact-monomorphic-points], choose a quasi-compact
monomorphic field representative i of x. Applying that result to all points supplies
[lem-sfb-decent-etale-fibres-no-specializations]. An atlas and
[lem-weil-pbc-affine-opens-basis] give a jointly surjective affine etale chart family.
2. In an affine chart U, the fibre over the closed point x is closed by
[def-a1-space-point-topology]. Its points are closed in U: any specialization stays
in that fibre, and [lem-sfb-decent-etale-fibres-no-specializations] makes it trivial.
By [lem-trf-space-fibre-products-etale-covers], W = U times_X Spec K is a scheme etale
over K. It is quasi-compact by the choice of i. By
[lem-weil-pbc-etale-fibre-discrete-separable-points], W is discrete and is a disjoint
union of field spectra. Its singleton opens have a finite subcover, so this union is finite.
3. The projection W to U is monomorphic by base change of i. For each component image u,
[lem-trf-closed-point-residue-immersion] makes Spec kappa(u) to U a closed immersion.
By [lem-weil-pbc-morphism-from-spec-field], the component factors through that map.
By [lem-weil-pbc-field-point-factors-through-immersion], its pullback is the same component;
components over other points have empty pullback. The resulting nonempty monomorphism
into Spec kappa(u) is an isomorphism by [lem-sfb-monomorphism-into-field-coproduct].
Thus exactly one component lies over each u and its residue-field map is an isomorphism.
4. The finitely many component maps to U are closed immersions with distinct closed
images. Their union has discrete induced topology, so W to U is a closed embedding.
Near one image point remove all other component images; the sheaf map there is the
surjective sheaf map of that component's closed immersion. Away from the union its
target is zero. Surjectivity is local, so W to U is a closed immersion by
[def-weil-closed-immersion]. This also covers empty W.
5. Apply [lem-sfb-space-closed-immersion-atlas-locality] to the affine etale chart family.
It gives scheme representability and closed-immersion projections after every scheme
test. The chosen representative has point image exactly the singleton x. -/
theorem exists_closedImmersion_field_of_decent {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hdecent : ∀ (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
      (c : yoneda.obj (Over.mk b) ⟶ X.obj.obj) (U : Over S), IsAffine U.left →
      ∀ t : yoneda.obj U ⟶ X.obj.obj,
        ∃ (V : Over S) (p : V ⟶ U) (q : yoneda.obj V ⟶ yoneda.obj (Over.mk b)),
          IsPullback q (yoneda.map p) c t ∧ CompactSpace V.left)
    (x : Point X.obj.obj) (hx : IsClosed ({x} : Set (Point X.obj.obj))) :
    ∃ (K : Type u) (_ : Field K) (b : Spec (CommRingCat.of K) ⟶ S)
      (i : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      pointImage i = {x} ∧ IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
