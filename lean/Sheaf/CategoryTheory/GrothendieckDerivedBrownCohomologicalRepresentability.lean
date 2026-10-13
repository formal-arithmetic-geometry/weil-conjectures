/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-! # Cohomological Brown representability for Grothendieck derived categories

Source: Stacks Project, Tag 0F5X, `injectives-lemma-brown`.
(blueprint: lem-grothendieck-derived-brown-cohomological-representability)
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- A cohomological functor on the unbounded derived category of a Grothendieck
abelian category taking set-indexed coproducts to products is representable.
Source: Stacks Project, Tag 0F5X, `injectives-lemma-brown`.
(blueprint: lem-grothendieck-derived-brown-cohomological-representability)

Proof in words: Use Gabriel-Popescu to write A as an exact localization of modules
by L, with fully faithful derived right adjoint RG and counit L RG ≅ identity.
The composite H L preserves products of opposite coproducts and is cohomological.
Brown representability for the compact generator given by the free rank-one module
represents H L by a complex E. Complete the unit E → RG(L(E)) to a triangle
M → E → RG(L(E)) → M[1]. Applying L kills M, because the counit is invertible.
Thus Hom(M,E) = H(L(M)) = 0. Exactness of Hom(-,E) on this triangle gives a
retraction RG(L(E)) → E of its second map. Evaluating on RG(X), and using the
localization adjunction and its counit, makes H a natural direct summand of the
functor Hom(-,L(E)). Yoneda identifies its projector with an idempotent on L(E).
The derived category has countable coproducts, so idempotents split by the telescope
argument. Its splitting object represents H. All sums used in the Brown construction
are indexed in max(w,vA,vH); the explicit coproduct hypothesis includes these sums.
The representing natural Hom bijections define RepresentableBy, also when the
Hom and value universes differ. No compact generation of D(A) is asserted.
-/
theorem grothendieckDerived_cohomological_isRepresentable
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w vA vH), PreservesLimitsOfShape (Discrete I) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by sorry

end CategoryTheory
