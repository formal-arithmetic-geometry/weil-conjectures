/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleMapIsoLocus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Arbitrary base change detects the isomorphism locus

Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), matrix proof; Tag 0BDP,
final determinant sentence; Tag 0095, tensor formula for pullback.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- If a pulled-back vector bundle map is invertible, its topological image lies in
the explicitly constructed locally invertible open.
Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), and Tag 0095.
(blueprint: lem-sc-finite-locally-free-map-iso-locus-pullback)

Proof: Work on simultaneous finite free frames of M and N. At any t of T, an
inverse after tensor pullback gives an inverse matrix over the residue field k(t).
The extension from k(h(t)) to k(t) reflects matrix invertibility. In particular the
ranks at h(t) must agree. On an equal-rank frame with matrix A, det A is therefore
nonzero in k(h(t)). The principal determinant open contains h(t), and the adjugate
divided by det A supplies an inverse there. This open is among those in the supremum
defining moduleMapIsoLocus, proving that h(t) belongs to it. Apply this to every t.
For zero ranks the determinant is 1, and for empty T image containment is vacuous.
No reducedness is required: in each local ring, an element whose residue is nonzero
is a unit. The scalar-extension matrix is identified using the tensor formula of
Tag 0095; thus the statement concerns tensorPullback rather than another pullback. -/
theorem range_subset_moduleMapIsoLocus_of_isIso_tensorPullback {W : Scheme.{u}}
    (M N : W.Modules) [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    {T : Scheme.{u}} (h : T ⟶ W) (hφ : IsIso ((tensorPullback h).map φ)) :
    Set.range h ⊆ (moduleMapIsoLocus φ : Set W) := by sorry

end AlgebraicGeometry.Scheme.Modules
