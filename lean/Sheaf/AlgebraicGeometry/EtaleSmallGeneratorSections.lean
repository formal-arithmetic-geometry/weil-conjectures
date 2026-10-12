/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSmallGenerator

/-!
# Section-size bound for the affine etale generator

Source: Stacks Project, Tags 01DO and 03EW; Mathlib free-Yoneda sheaves and
affine etale site comparison.
(blueprint: lem-sc-etale-small-generator-sections)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every section group of the concrete etale generator is small in the scheme universe.
Source: Stacks Project, Tag 01DO, its sheafified free representables, and the small
model of the affine etale site in Mathlib.AlgebraicGeometry.Sites.AffineEtale.
(blueprint: lem-sc-etale-small-generator-sections)

Proof: On the u-small affine model C, the free presheaf for each representable is a
coproduct of copies of ULift Z indexed by a u-small hom set. It is the coefficient
lift of the same free presheaf valued in AddCommGrpCat.{u}. Sheafification commutes
with this coefficient lift: compute it by the twice-iterated plus construction.
Each plus step uses matching-family limits indexed by u-small covering sieves and
filtered colimits over the u-small partially ordered set of covering sieves. Lifting
abelian groups preserves these limits and colimits, so the two sheafifications are
canonically isomorphic. The u-small coproduct over C has the same compatibility,
since coefficient lifting preserves coproducts and sheafification is a left adjoint.
Consequently the coproduct used in etaleSmallGenerator has u-small section groups
on C. The small-model equivalence transports that bound to every affine etale object.
For an arbitrary etale object U, use a covering by its affine open subschemes indexed
by a u-small type (the affine opens form a subset of the u-small set of all opens).
The transported sheaf's separatedness makes its section group on U inject into the
product of its section groups on this covering. A u-small product of u-small types,
and every type injecting into it, is u-small. This is the required conclusion. For
the empty U the covering is empty, the product is a singleton and the section group
is trivial; no nonemptiness or quasi-compactness assumption is needed. -/
theorem etaleSmallGenerator_sections_small (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    Small.{u} ((etaleSmallGenerator X).obj.obj U) := by
  sorry

end AlgebraicGeometry.Scheme
