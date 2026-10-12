/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Changing universes in the Brown representability criterion

Source: Stacks Project, Tag 0A8F, Lemma `lemma-brown`, with its set-indexing
convention made explicit (blueprint: lem-pc-brown-representability-universe-transfer).
-/

@[expose] public section

universe w v vH u

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- Brown representability in the common enlarged universe implies representability
for a category and an abelian-group-valued functor with independent morphism and value
universes. Source: Stacks Project, Tag 0A8F, Lemma `lemma-brown`, universe bookkeeping
(blueprint: lem-pc-brown-representability-universe-transfer).

Proof: Put V = max w v vH. Replace C by ULiftHom.{V} C, which has the same
object universe and Hom groups lifted to V. Transport zero objects, preadditivity,
shifts, distinguished triangles, and the triangulated axioms along its equivalence
with C. Transport the V-indexed coproducts along the equivalence. The original
compact generators, with the same index set, remain compact: the canonical map
from the direct sum of lifted Hom groups to Hom into a coproduct is identified
with the original canonical map by the lift/down additive equivalences. The
coproduct of the transported generators remains a weak generator because the
equivalence preserves zero objects, shifts, and nonzero morphisms.

Precompose H with the opposite of the equivalence's inverse and postcompose with
AddCommGrpCat.uliftFunctor.{V}. This is a functor K to AddCommGrpCat.{V}.
It is homological: the equivalence preserves distinguished triangles and the lift
functor preserves exact sequences of groups. It preserves V-indexed products:
the equivalence preserves limits, H preserves these products by assumption, and
lifting groups preserves a product whenever that product exists (the product
universal property transfers along the lift/down bijections). Apply hBrown to K.
For a representing object G in the lifted category, transport G back to C.
Evaluate the representing natural isomorphism on the lifted objects of C and
compose its component bijections with the lift/down bijections on Hom groups and
on H's values. This gives natural bijections Hom_C(-, G) ≃ H(-), hence the asserted
representability of the underlying set-valued functor. Empty coproducts and the
zero category are preserved by the same equivalence; no nonemptiness is required.
-/
theorem brownCohomologicalRepresentabilityUniverseTransfer
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
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by sorry

end CategoryTheory
