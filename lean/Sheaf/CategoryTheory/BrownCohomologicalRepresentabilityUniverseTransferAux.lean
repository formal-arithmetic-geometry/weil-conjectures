/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-! Auxiliary reduction for universe transfer. -/

@[expose] public section

universe w v vH u

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- The universe-transport construction produces a representing object and additive
natural isomorphism in the original category. The proof transports all structures
along `ULiftHom.equiv`, applies the common-universe Brown principle, and descends
along the equivalence and the universe-lift equivalences on additive groups.
Source: Stacks Project, Tag 0A8F, with explicit universe bookkeeping
(blueprint: lem-pc-brown-representability-universe-transfer-aux).

Proof: Construct the category `ULiftHom.{max w v vH} C` and transport zero objects,
shifts, preadditivity, distinguished triangles, coproducts, compact generators, and
weak generation across `ULiftHom.equiv`. Compose `H` with the inverse equivalence and
`AddCommGrpCat.uliftFunctor`; transport homologicality and preservation of all products
using the equivalence and the lift/down additive equivalences. Apply `hBrown` in the
common universe. Descend the representing object and its natural bijections along the
same equivalences to obtain a representing-by structure for `H ⋙ forget` in `C`.
-/
theorem brownCohomologicalRepresentabilityUniverseTransfer_aux
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{max w v vH} C]
    (hC : IsCompactlyGeneratedTriangulated.{max w v vH} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) H)
    (hBrown : ∀ (A : Type u) [Category.{max w v vH} A]
      [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
      [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
      [IsTriangulated A] [HasCoproducts.{max w v vH} A],
      IsCompactlyGeneratedTriangulated.{max w v vH} A →
      ∀ (K : Aᵒᵖ ⥤ AddCommGrpCat.{max w v vH}) [K.IsHomological],
      (∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) K) →
      ∃ G : A, Nonempty (K ≅ preadditiveYoneda.obj G)) :
    ∃ G : C, Nonempty ((H ⋙ forget AddCommGrpCat).RepresentableBy G) := by
  sorry



end CategoryTheory
