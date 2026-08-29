/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!

# The tensor product of sheaves is preadditive and linear,
  the pushforward of sheaves is lax braided

Let `A` be an abelian monoidal category whose tensor product is additive in each variable
and `J` a Grothendieck topology with `HasSheafify J A` such that the localized monoidal
structure `Sheaf.monoidalCategory` on `Sheaf J A` is available (`(J.W).IsMonoidal`).
We show that this monoidal structure is compatible with the preadditive structure on
`Sheaf J A`, i.e. `MonoidalPreadditive (Sheaf J A)`, and, when `A` is moreover `R`-linear
with `R`-linear tensor product, that it is compatible with the `R`-linear structure,
i.e. `MonoidalLinear R (Sheaf J A)`.

The sheafification functor `presheafToSheaf J A` is braided, hence its right adjoint
`sheafToPresheaf J A` is lax braided.

If `F : C ⥤ D` is a continuous functor of sites, the pushforward
`F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is obtained by sheafifying the
restriction along `F.op` of the underlying presheaf. As restriction is a braided functor
between the (pointwise monoidal) categories of presheaves, the pushforward is lax braided.
When `A` is symmetric this says that `F.sheafPushforwardContinuous A J K` is lax symmetric
monoidal.

## Main results

- `CategoryTheory.Sheaf.monoidalPreadditive`: the monoidal category structure on
  `Sheaf J A` obtained in `Sheaf.monoidalCategory` is preadditive.
- `CategoryTheory.Sheaf.monoidalLinear`: the monoidal category structure on
  `Sheaf J A` obtained in `Sheaf.monoidalCategory` is `R`-linear.
- `CategoryTheory.sheafToPresheafLaxBraided`: the underlying presheaf functor is lax braided.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxBraided`: the pushforward of sheaves
  along a continuous functor of sites is lax braided.
-/




@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Sheaf

open MonoidalCategory CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [Abelian A] [MonoidalPreadditive A]
  [HasSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] monoidalCategory

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
tensorLeft P ⋙ presheafToSheaf J A` in the second variable. -/
noncomputable def presheafToSheafCompTensorLeftIso (P : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
      tensorLeft P ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun Q ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
tensorRight Q ⋙ presheafToSheaf J A` in the first variable. -/
noncomputable def presheafToSheafCompTensorRightIso (Q : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
      tensorRight Q ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun P ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- Tensoring on the left with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorLeftIso (X : Sheaf J A) :
    tensorLeft X ≅ sheafToPresheaf J A ⋙ tensorLeft X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorLeft _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorLeftIso X.obj)

/-- Tensoring on the right with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorRightIso (X : Sheaf J A) :
    tensorRight X ≅ sheafToPresheaf J A ⋙ tensorRight X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).flip.mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorRight _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorRightIso X.obj)

noncomputable instance (X : Sheaf J A) : (tensorLeft X).Additive :=
  Functor.additive_of_iso (tensorLeftIso X).symm

noncomputable instance (X : Sheaf J A) : (tensorRight X).Additive :=
  Functor.additive_of_iso (tensorRightIso X).symm

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is preadditive when `A` is an abelian monoidal category with additive tensor product. -/
instance monoidalPreadditive : MonoidalPreadditive (Sheaf J A) where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} _ _ := (tensorLeft X).map_add
  add_whiskerRight {X _ _} _ _ := (tensorRight X).map_add

section Linear

variable (R : Type*) [Semiring R] [Linear R A] [MonoidalLinear R A]

noncomputable instance (X : Sheaf J A) : (tensorLeft X).Linear R :=
  Functor.linear_of_iso R (tensorLeftIso X).symm

noncomputable instance (X : Sheaf J A) : (tensorRight X).Linear R :=
  Functor.linear_of_iso R (tensorRightIso X).symm

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is `R`-linear when `A` is an abelian `R`-linear monoidal category with `R`-linear tensor
product. -/
instance monoidalLinear : MonoidalLinear R (Sheaf J A) where
  whiskerLeft_smul X {_ _} r f := (tensorLeft X).map_smul r f
  smul_whiskerRight r {_ _} f X := (tensorRight X).map_smul r f

end Linear

end CategoryTheory.Sheaf

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The functor sending a sheaf to its underlying presheaf is lax monoidal, being the right
adjoint of the (strong) monoidal sheafification functor. -/
noncomputable instance sheafToPresheafLaxMonoidal : (sheafToPresheaf J A).LaxMonoidal :=
  (sheafificationAdjunction J A).rightAdjointLaxMonoidal

/-- The functor sending a sheaf to its underlying presheaf is lax braided, being the right
adjoint of the braided sheafification functor. -/
noncomputable instance sheafToPresheafLaxBraided : (sheafToPresheaf J A).LaxBraided :=
  (sheafificationAdjunction J A).rightAdjointLaxBraided

namespace Functor

variable [F.IsContinuous J K] [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

/-- The pushforward of sheaves along a continuous functor `F : C ⥤ D` is the sheafification of
the restriction along `F.op` of the underlying presheaf. -/
noncomputable def sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso :
    sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op ⋙ presheafToSheaf J A ≅
      F.sheafPushforwardContinuous A J K :=
  isoWhiskerLeft (F.sheafPushforwardContinuous A J K)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (F.sheafPushforwardContinuous A J K).rightUnitor

/-- The pushforward of sheaves along a continuous functor of sites is lax monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxMonoidal :
    (F.sheafPushforwardContinuous A J K).LaxMonoidal :=
  LaxMonoidal.transport (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

/-- The pushforward of sheaves along a continuous functor of sites is lax braided. When `A` is
symmetric, this says that the pushforward is lax symmetric monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxBraided :
    (F.sheafPushforwardContinuous A J K).LaxBraided :=
  have := LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)
  LaxBraided.ofNatIso (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

end Functor

end CategoryTheory
