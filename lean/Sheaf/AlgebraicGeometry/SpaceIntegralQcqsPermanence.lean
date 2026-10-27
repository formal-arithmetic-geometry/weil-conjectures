/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Integral algebraic-space morphisms and quasi-compactness permanence

Source: Stacks Project, Morphisms of Spaces, Tags 03WE, 073B, 03KL and 03KQ;
Morphisms of Schemes, Tag 01S7
(blueprint: lem-sfb-space-integral-qcqs-permanence).

Quasi-compactness uses the existing point topology and affine-test predicate.
Quasi-separatedness is absolute, via the existing affine-pair criterion of Tag 0AHR.
Scheme representability is an isomorphism with the Yoneda presheaf of an actual scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Integral maps are affine, quasi-compact and separated, preserve qcqs sources over qcqs
targets, and preserve absolute separatedness when the target is a scheme. Maps from
quasi-compact spaces to quasi-separated spaces are quasi-compact; quasi-compact open
subspaces of quasi-separated spaces are quasi-separated.
Source: Stacks Project, Morphisms of Spaces, Tags 03WE, 03WG, 073B(1), 03KL and 03KQ;
Morphisms of Schemes, Tag 01S7
(blueprint: lem-sfb-space-integral-qcqs-permanence).

Proof: (1) Reconcile point-space and atlas quasi-compactness using
[lem-sfb-qc-space-affine-etale-atlas], [lem-weil-pbc-affine-scheme-qcqs] and
[lem-a1-space-finite-affine-subatlas]. A compact point space has an affine surjective
etale atlas, and a quasi-compact atlas has compact target point space.
(2) On every affine scheme test, integrality gives an affine scheme source by
[def-weil-finite-integral-morphism]. Apply [lem-sfb-space-affine-locality] to obtain
affineness, quasi-compactness, separatedness, and the qcqs permanence assertion.
(3) If the target is a scheme, the same affine locality makes the source a scheme.
Compose its separated map to the target with the target's separated map to Spec Z,
using [lem-sfb-space-separated-fp-composition]. If the target is also quasi-compact,
apply [lem-sfb-space-quasicompact-affine-tests] to its identity scheme test. The
source is quasi-compact, and step (1) identifies this with point-space compactness.
(4) Apply [lem-sfb-space-qcqs-permanence], first implication, to an arbitrary map
from a quasi-compact space into a quasi-separated space.
(5) For an open immersion, injectivity on sections identifies the absolute diagonal
of the open subspace with the pullback of the target's absolute diagonal: equal
images of two sections in the target mean equal sections in the subspace. This is
the sheaf pullback of [lem-trf-space-fibre-products-etale-covers]. Base-change
stability in [lem-sfb-space-quasicompact-affine-tests] gives quasi-separatedness.
The stated case also assumes the open source is quasi-compact.
(6) Empty spaces require no nonemptiness hypothesis: empty covers have finite empty
subcovers, the empty scheme is affine, and its diagonal is a quasi-compact closed
immersion. All preceding arguments therefore include empty sources and fibres. -/
theorem integral_qcqs_permanence {S : Scheme.{u}} :
    (∀ (B X : AlgebraicSpace S) (g : B ⟶ X),
      IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) g.hom.hom →
        MapIsAffine g ∧ MapIsQuasiCompact g.hom.hom ∧ MapIsSeparated g ∧
          (CompactSpace (Point X.obj.obj) → IsAbsolutelyQuasiSeparated X →
            CompactSpace (Point B.obj.obj) ∧ IsAbsolutelyQuasiSeparated B) ∧
          (∀ (T : Over S), Nonempty (X.obj.obj ≅ yoneda.obj T) →
            T.left.IsSeparated → ∃ U : Over S,
              Nonempty (B.obj.obj ≅ yoneda.obj U) ∧ U.left.IsSeparated ∧
                (CompactSpace T.left → CompactSpace U.left))) ∧
      (∀ (A X : AlgebraicSpace S) (f : A ⟶ X),
        CompactSpace (Point A.obj.obj) → IsAbsolutelyQuasiSeparated X →
          MapIsQuasiCompact f.hom.hom) ∧
      (∀ (U X : AlgebraicSpace S) (j : U ⟶ X),
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom →
          CompactSpace (Point U.obj.obj) → IsAbsolutelyQuasiSeparated X →
            IsAbsolutelyQuasiSeparated U) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
