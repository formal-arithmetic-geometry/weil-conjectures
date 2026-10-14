/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.FieldScalarPresheafPullbackExists
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Exactness of extension from a constant field presheaf

Source: Stacks Project, Modules, Tag 02N4; Sheaves on Spaces, Tag 0095.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

/-- Extension from the constant field presheaf preserves monomorphisms before
sheafification.

Source: Stacks Project, Modules, Tag 02N4; Sheaves on Spaces, Tag 0095.
(blueprint: lem-sc-field-scalar-presheaf-pullback-mono).

Proof: put α_U = R(X -> U) ∘ α. The identity-site presheaf pullback is computed
at U by R(U) ⊗[k] V(U). Here R(U) is a right k-module by a · c = a α_U(c),
and left R(U) acts on the first factor by left multiplication. This bimodule
construction does not assume that R(U) is commutative or that α_U(k) is central.
Its universal property gives the natural sectionwise tensor description of the
Mathlib presheaf pullback. A monomorphism of module presheaves is injective at
every open. Every right module over a field is flat, so tensoring these injections
with R(U) remains injective. Hence the image morphism is pointwise injective and
therefore a monomorphism of R-module presheaves. If R(U) is the zero ring, the
tensor is zero and the assertion still holds; the empty space also needs no
nonempty-open assumption. -/
theorem fieldScalarPresheafPullback_preservesMonomorphisms
    {k : Type u} [Field k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    letI := fieldScalarPresheafPullback_isRightAdjoint.{u, v} X R α
    (PresheafOfModules.pullback.{max u v}
      (fieldScalarPresheafRingMap X R α)).PreservesMonomorphisms := by sorry

end SheafOfModules
