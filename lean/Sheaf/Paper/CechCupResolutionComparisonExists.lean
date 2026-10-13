/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData

/-! # Existence of Cech comparisons for a computing resolution pairing

Source: Stacks Project, Tags 01EQ and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A computing sectionwise resolution pairing admits canonical Cech comparison
maps. This supplies only alpha, beta and their identifications, not a cup comparison.
Source: Stacks Project, Tag 0FKV, proof of Lemma 20.31.4, flasque-resolution paragraph;
Tag 01EQ, proof of the canonical Cech comparison.
(blueprint: lem-sc-cech-cup-resolution-comparison-exists)

Proof: take nonnegative Godement/flasque resolutions of F, G and F tensor G with
their augmentation-preserving section pairing. Compare them to injective resolutions
over the coefficient augmentations; flasque acyclicity makes the comparisons compute
global cohomology and thus supplies CupResolutionPairing D. For each of its three
resolutions use restriction to Cech degree zero for alpha, and augmentation into
resolution degree zero for beta. Naturality of restriction and the zero differential
of the augmentation verify their cochain identities. Flasque Cech acyclicity and the
first-quadrant column comparison show alpha is a quasi-isomorphism. Define iso by the
inverse of the resolution's computing global comparison, the injective-resolution
cohomology identification, and H(alpha). This gives alpha_class. Map the entire Cech
double complex to the one for the injective resolution. Its alpha and beta squares
commute by naturality and the over-augmentation equality. The injective alpha map is
a quasi-isomorphism; cancellation in these squares and IsModuleCechComparison give
beta_class for every specified canonical comparison. Degree zero and an empty cover
of the empty scheme use the same cochain identities and require no exception. -/
theorem exists_cupCechResolutionComparison (X : Scheme.{v}) {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (F G : X.Modules) :
    ∃ D : CupResolutionPairing F G,
      Nonempty (CupCechResolutionComparison U D.left) ∧
      Nonempty (CupCechResolutionComparison U D.right) ∧
      Nonempty (CupCechResolutionComparison U D.target) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
