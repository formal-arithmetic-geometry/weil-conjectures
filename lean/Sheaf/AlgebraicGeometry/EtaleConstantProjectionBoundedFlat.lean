/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Flat.Basic

/-! # Constant projection with bounded flat coefficients
Source: Stacks Project, Etale Cohomology, Tag 0F0E, lemma-pull-out-constant.
(blueprint: lem-kun-constant-projection-bounded-flat)
-/
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- The constant projection comparison is invertible for a bounded complex of flat
integer modules and an arbitrary bounded-below complex of etale sheaves.
Source: Stacks Project, Tag 0F0E, the bounded-complex and single-flat-module reductions.
(blueprint: lem-kun-constant-projection-bounded-flat).
Proof: on K-flat models the derived comparison is induced by the ordinary constant
sheaf tensor comparison. A cone is the direct sum of a complex and a shifted complex;
tensor distributes over that sum. The cone differential has entries d, u, zero, -d.
Naturality supplies the u-square, and the shifted differential has the same minus sign
on both sides. The counit is a transformation of exact functors, so taking its mate
preserves these squares. Applying triangulated derived sections gives a morphism of
triangles, in either variable. For the tensor unit, the constant functor's normalized
unit constraint and the adjunction triangle identity identify the mate with identity.
Thus finite free modules give finite sums of identity comparisons.

For a flat integer module M and a sheaf F in degree zero, choose a small directed
Lazard presentation M = colim M_i by finite free modules. Constants and ordinary tensor
preserve this colimit. The quasi-compact quasi-separated cohomology theorem gives
H^q(X,F tensor constant(M)) = colim H^q(X,F tensor constant(M_i)) for q nonnegative.
On the source, exact tensor with a flat module gives
H^q(RΓ(F) tensor^L M) = H^q(RΓ(F)) tensor M; ordinary module tensor commutes with the
same colimit. Naturality identifies the finite free comparison systems. Every finite
free map is invertible, hence so is the colimit map. Negative cohomology vanishes.

For bounded-below E and fixed flat M, fix n and replace E by its good truncation
above n. Flat tensor preserves the kernel-image sequences computing homology and
therefore preserves the cohomology comparison through n. Derived sections preserves
lower bounds, so the derived truncation comparison identifies degree n before and
after truncation on both sides. The truncated object has finite cohomological support.
Its canonical Postnikov triangles have shifted cohomology sheaves as successive
quotients. The sheaf case, the shift squares above, and the long exact sequences
prove the comparison for this truncation, hence for E in degree n. All n gives an
isomorphism. Finally induct over the finite interval supporting P: the stupid
truncation triangle removes its lowest term, leaving a shorter bounded flat complex
and a shifted flat module. The natural morphism of triangles and the five lemma
prove the middle comparison. If N is below b, P is zero; zero inputs and the empty
scheme are included by these same constructions. -/
theorem isIso_constantDerivedProjectionMap_of_bounded_flat
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ℤ)
    (b N : ℤ) [P.IsStrictlyGE b] [P.IsStrictlyLE N]
    (hP : ∀ i : ℤ, Module.Flat (ULift.{u + 1} ℤ) (P.X i)) :
    IsIso (constantDerivedProjectionMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) X
      (DerivedCategory.Plus.ι.obj E) (DerivedCategory.Q.obj P)) := by sorry
end AlgebraicGeometry.Etale
