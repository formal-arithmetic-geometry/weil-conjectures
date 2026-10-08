/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

/-!
# The underlying presheaf of the internal hom of sheaves

Let `C` be an essentially small site and `A` a symmetric monoidal closed Grothendieck abelian
category. The internal hom of the monoidal closed structure on `Sheaf J A` of
`CategoryTheory.GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall` is, by Day's
reflection theorem, the sheafification of the internal hom of the underlying presheaves, the
functor enriched hom `functorEnrichedHom A F G`. Since the latter is already a sheaf
(`CategoryTheory.Presheaf.isSheaf_functorEnrichedHom`), the underlying presheaf of `[F, G]` is
`functorEnrichedHom A F G` (`CategoryTheory.GrothendieckTopology.sheafToPresheafIhomIso`): its
sections over `U` are the morphisms between the restrictions of `F` and `G` to `C/U`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace CategoryTheory.GrothendieckTopology

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
  {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)

/-- The underlying presheaf of the internal hom `[F, G]` of sheaves is the internal hom
`functorEnrichedHom A F G` of the underlying presheaves: the latter is a sheaf, so the
sheafification in Day's construction of `[F, G]` does not change it. -/
noncomputable def sheafToPresheafIhomIso (F G : Sheaf J A) :
    ((ihom F).obj G).obj ≅ functorEnrichedHom A F.obj G.obj :=
  have : IsIso ((sheafificationAdjunction J A).unit.app (functorEnrichedHom A F.obj G.obj)) := by
    rw [sheafificationAdjunction_unit_app]
    exact CategoryTheory.isIso_toSheafify _ (Presheaf.isSheaf_functorEnrichedHom _ _ G.property)
  (asIso ((sheafificationAdjunction J A).unit.app (functorEnrichedHom A F.obj G.obj))).symm

end CategoryTheory.GrothendieckTopology
