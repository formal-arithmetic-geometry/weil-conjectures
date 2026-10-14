/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! Transfer of large coproducts from a derived category to its abelian category. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- Large derived coproducts give large coproducts in the underlying category.

Source: the first step of node new-stage3-gabriel-popescu-large-hom-right-adjoint,
the agent-written derived-to-abelian extension of Stacks Project Tag 0F5S.
The extension uses injective copresentations and degree-zero cohomology.

(blueprint: new-stage3-derived-large-coproducts-transfer)

Proof in words: for a family X_i at the displayed size, take the coproduct K
of the degree-zero objects X_i[0] in D(A), and set P = H^0(K). Apply H^0 to
the injections to obtain maps X_i -> P. If I is injective, I[0] is
K-injective; exactness of Hom(-,I) identifies Hom_D(K,I[0]) naturally with
Hom_A(H^0(K),I). The derived coproduct property therefore identifies the
map Hom_A(P,I) -> product_i Hom_A(X_i,I) with a bijection.
For arbitrary Y, embed Y into an injective I^0, and embed its cokernel into
an injective I^1. This gives an exact sequence 0 -> Y -> I^0 -> I^1.
The two functors Hom_A(P,-) and product_i Hom_A(X_i,-) are left exact.
The comparison maps for I^0 and I^1 are bijections and commute with the
map I^0 -> I^1. Taking kernels gives the comparison bijection for Y.
This is precisely the universal property of the displayed cofan with vertex
P. Thus every family of the displayed size has a coproduct. The argument
also covers the empty family, for which P is a zero object.
-/
theorem derived_large_coproducts_transfer
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    HasCoproducts.{max w vA vH} A := by sorry

end CategoryTheory
