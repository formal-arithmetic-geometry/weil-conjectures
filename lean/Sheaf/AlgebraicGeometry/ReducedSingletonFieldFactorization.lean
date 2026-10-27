/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Reduced singleton-image maps factor through a field monomorphism

Source: Stacks Project, Decent Spaces, Tags 0H1T
(lemma-factor-through-residual-space-decent) and 0H1R
(lemma-residual-space-monomorphism)
(blueprint: lem-sfb-reduced-singleton-field-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A reduced algebraic space mapping into the point represented by a quasi-compact
field monomorphism factors uniquely through that monomorphism. The point is the image
of the unique point of `Spec F`. Maps to the representable presheaf of `Spec F` are
precisely morphisms to that scheme over `S`; all transformations are on `Over S`.
No Noetherian or quasi-separatedness hypothesis is imposed.

Source: Stacks Project, Decent Spaces, Tags 0H1T
(lemma-factor-through-residual-space-decent) and 0H1R
(lemma-residual-space-monomorphism)
(blueprint: lem-sfb-reduced-singleton-field-factorization).

Proof:
1. Choose an affine etale chart containing a point over the image of `j`. Its image
is a quasi-compact open subspace `E` by lem-a1-space-affine-etale-cover and
lem-a1-space-etale-open-image. Both maps factor through `E` by
lem-a1-space-open-factor-scheme-tests. The map `j` remains quasi-compact by the
scheme-test pullback comparison there, and remains monomorphic by cancellation.
2. Apply lem-sfb-qc-space-schematic-strata to obtain a schematic closed subspace
`T` of an open neighbourhood `U` containing the point. The maps factor through `U`.
On a reduced etale scheme atlas `W` of `Y`, the closed immersion
`W ×_U T → W` has image all of `W` by lem-a1-space-point-open-calculus.
Thus lem-weil-pbc-reduced-source-factors-through-closed-subscheme gives `W → T`.
The same argument applies to the reduced scheme `Spec F`, giving `j_T : Spec F → T`.
3. The point map of `T → X` is injective (closed then open immersion), so `W → T`
has singleton image. Cancellation with `j` makes `j_T` a scheme monomorphism;
the structure map to `S` ensures cancellation also for arbitrary scheme tests.
4. By lem-weil-pbc-morphism-from-spec-field, `j_T` factors through the residue field
at its image point. The resulting map from `Spec F` to that residue-field spectrum
is monomorphic; lem-sfb-monomorphism-into-field-coproduct for a one-element family
makes it an isomorphism. Apply lem-sfb-reduced-scheme-single-point-residue-factorization
to `W → T` and compose with that isomorphism's inverse to obtain `W → Spec F`.
5. By lem-trf-space-fibre-products-etale-covers, the atlas remains surjective etale
on every scheme test. The two pullbacks of the map to `Spec F` agree by cancellation
with `j`. The fppf sheaf condition glues them, with naturality and uniqueness again
from the monomorphism. The empty source is included by the empty covering. -/
theorem existsUnique_factor_through_field_of_reduced_singleton_image
    {S : Scheme.{u}} (X Y : AlgebraicSpace S) (F : Type u) [Field F]
    (s : Spec (CommRingCat.of F) ⟶ S)
    (j : yoneda.obj (Over.mk s) ⟶ X.obj.obj) [Mono j]
    (hqc : MapIsQuasiCompact j) (hred : IsReduced Y)
    (f : Y ⟶ X)
    (himage : pointImage f.hom.hom ⊆ {schemePointMap j (IsLocalRing.closedPoint F)}) :
    ∃! g : Y.obj.obj ⟶ yoneda.obj (Over.mk s), g ≫ j = f.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
