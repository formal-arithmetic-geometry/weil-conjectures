/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetMonoidalAdjunction

/-!
# Free sheaves of modules on abelian sheaves, as a braided monoidal left adjoint

For a lax braided functor `G : A ⥤ B`, postcomposition `sheafCompose J G` is lax braided for the
sheafified tensor products (`CategoryTheory.sheafComposeLaxBraided`). For a commutative ring
`R`, the sheafified free `R`-module functor `M ↦ (R ⊗[ℤ] M)^#` from abelian sheaves to sheaves of
`R`-modules is strong monoidal and braided, left adjoint to the forgetful functor by a monoidal
adjunction (`CategoryTheory.Sheaf.extendScalarsAbAdjunction`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

/-- Postcomposition with a lax braided functor is lax braided for the pointwise monoidal
structures on functor categories. -/
instance Functor.LaxBraided.whiskeringRight {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [MonoidalCategory D] [BraidedCategory D] [MonoidalCategory E]
    [BraidedCategory E] (L : D ⥤ E) [L.LaxBraided] :
    ((Functor.whiskeringRight C D E).obj L).LaxBraided where
  braided F G := by
    ext X
    exact Functor.LaxBraided.braided (F := L) (F.obj X) (G.obj X)

section SheafCompose

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {A : Type*} [Category* A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type*} [Category* B] [MonoidalCategory B] [BraidedCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G] [G.LaxBraided]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The postcomposition of sheaves with a lax braided functor is lax braided, being monoidally
isomorphic to the composite of the lax braided inclusion of sheaves into presheaves, of
postcomposition with `G` on presheaves and of sheafification. -/
noncomputable instance sheafComposeLaxBraided : (sheafCompose J G).LaxBraided :=
  have := Functor.LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G)
  Functor.LaxBraided.ofNatIso (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G)

end SheafCompose

namespace Sheaf

universe v

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (R : Type v) [CommRing R]
  [HasWeakSheafify J Ab.{v}] [(J.W (A := Ab.{v})).IsMonoidal]
  [HasWeakSheafify J (ModuleCat.{v} R)] [(J.W (A := ModuleCat.{v} R)).IsMonoidal]
  [J.HasSheafCompose (forget₂ (ModuleCat.{v} R) Ab.{v})]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The sheafified free `R`-module functor `M ↦ (R ⊗[ℤ] M)^#` from abelian sheaves to sheaves of
`R`-modules. -/
noncomputable def extendScalarsAb : Sheaf J Ab.{v} ⥤ Sheaf J (ModuleCat.{v} R) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalarsAb R)

/-- The sheafified free `R`-module functor is left adjoint to the forgetful functor. -/
noncomputable abbrev extendScalarsAbAdjunction :
    extendScalarsAb J R ⊣ sheafCompose J (forget₂ (ModuleCat.{v} R) Ab.{v}) :=
  Sheaf.adjunction J (ModuleCat.extendScalarsAbAdj R)

/-- The sheafified free `R`-module functor is strong monoidal. -/
noncomputable instance : (extendScalarsAb J R).Monoidal :=
  composeAndSheafifyMonoidal J (ModuleCat.extendScalarsAbAdj R)

/-- The adjunction between the sheafified free `R`-module functor and the forgetful functor is
monoidal. -/
instance : (extendScalarsAbAdjunction J R).IsMonoidal :=
  inferInstanceAs (letI := composeAndSheafifyOplaxMonoidal J (ModuleCat.extendScalarsAbAdj R)
    (extendScalarsAbAdjunction J R).IsMonoidal)

/-- The sheafified free `R`-module functor is braided, being the strong monoidal left adjoint of
the lax braided forgetful functor. -/
noncomputable instance : (extendScalarsAb J R).Braided where
  braided := Adjunction.μ_comp_map_braiding (extendScalarsAbAdjunction J R)

end Sheaf

end CategoryTheory
