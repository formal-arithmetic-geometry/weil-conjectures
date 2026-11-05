/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

/-!
# Composites of transported functors of algebras

For commutation isomorphisms `e₁ : L₁ ⋙ G ≅ F ⋙ L₁`, `e₂ : L₂ ⋙ H ≅ G ⋙ L₂` and
`e₃ : L₃ ⋙ H ≅ F ⋙ L₃`, an isomorphism `β : L₃ ≅ L₁ ⋙ L₂` compatible with them induces an
isomorphism `mapOfNatIso e₁ ⋙ mapOfNatIso e₂ ≅ mapOfNatIso e₃`
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompIsoOfIso`) whose components are those
of `β⁻¹` on the underlying objects.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D E : Type*} [Category C] [Category D] [Category E] {F : C ⥤ C} {G : D ⥤ D}
  {H : E ⥤ E} {L₁ : C ⥤ D} {L₂ : D ⥤ E} {L₃ : C ⥤ E} {e₁ : L₁ ⋙ G ≅ F ⋙ L₁}
  {e₂ : L₂ ⋙ H ≅ G ⋙ L₂} {e₃ : L₃ ⋙ H ≅ F ⋙ L₃}

end CategoryTheory.Endofunctor.IsoAlgebra
