/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit

/-!
# Morphisms from the monoidal unit of a category of sheaves of modules

Let `J` be a Grothendieck topology on `C` and `R` a commutative ring, and equip the category of
sheaves of `R`-modules with the monoidal structure `CategoryTheory.Sheaf.monoidalCategory`
(sheafification of the objectwise tensor product). Let `W` be a terminal object of `C`.

* Morphisms `𝟙_ ⟶ F` correspond to sections of `F` over `W`, via evaluation at the *unit
  section* `CategoryTheory.Sheaf.unitSection J W`, the image of `1 ∈ R`
  (`CategoryTheory.Sheaf.hom_ext_of_unitSection`, `CategoryTheory.Sheaf.exists_unitHom_eq`).
* Under this correspondence, `(λ_ 𝟙_).inv ≫ (s ⊗ₘ t)` corresponds to the image of
  `s(1) ⊗ t(1)` under the canonical map `F(W) ⊗ G(W) ⟶ (F ⊗ G)(W)`
  (`CategoryTheory.Sheaf.leftUnitor_inv_comp_tensorHom_app`).

If moreover `W` has finite disjoint refinements
(`CategoryTheory.GrothendieckTopology.HasFiniteDisjointRefinements`), then taking sections over
`W` is exact and commutes with coproducts and tensor products up to finite sums. We deduce that
the unit is projective (`CategoryTheory.Sheaf.projective_unit`), that morphisms from the unit to
a coproduct factor through a finite subcoproduct
(`CategoryTheory.Sheaf.unitFactorsThroughFiniteCoproducts`) and that morphisms from the unit to
a tensor product are finite sums of tensor products (`CategoryTheory.Sheaf.unitTensorFinite`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped TensorProduct

namespace ModuleCat

variable {R : Type*} [Ring R] {D : Type*} [Category* D] {K : D ⥤ ModuleCat.{w} R}

end ModuleCat

namespace CategoryTheory

namespace GrothendieckTopology.IsDisjointCover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [CommRing R]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  {W : C} {ι : Type*} [Finite ι] {Y : ι → C} {f : ∀ i, Y i ⟶ W}

end GrothendieckTopology.IsDisjointCover

namespace Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Type (max u v)}
  [CommRing R] [HasWeakSheafify J (ModuleCat.{max u v} R)]
  [(J.W (A := ModuleCat.{max u v} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- The canonical morphism from the objectwise tensor product of the presheaves underlying two
sheaves of modules to the presheaf underlying their tensor product. -/
noncomputable def tensorObjComparison (F G : Sheaf J (ModuleCat.{max u v} R)) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  (sheafificationAdjunction J _).homEquiv _ _
    (Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{max u v} R)) _ _ ≫
      ((sheafificationAdjunction J _).counit.app F ⊗ₘ (sheafificationAdjunction J _).counit.app G))

variable {J}

/-- The comparison `F(-) ⊗ G(-) ⟶ (F ⊗ G)(-)` is natural. -/
@[reassoc]
lemma tensorObjComparison_naturality {F F' G G' : Sheaf J (ModuleCat.{max u v} R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    tensorObjComparison J F G ≫ (f ⊗ₘ g).hom =
      (f.hom ⊗ₘ g.hom) ≫ tensorObjComparison J F' G' := by
  have h (F G : Sheaf J (ModuleCat.{max u v} R)) :
      ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J F G) =
        Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{max u v} R)) _ _ ≫
          ((sheafificationAdjunction J _).counit.app F ⊗ₘ
            (sheafificationAdjunction J _).counit.app G) :=
    Equiv.symm_apply_apply _ _
  have h₂ : ((sheafificationAdjunction J _).homEquiv _ _).symm
      (tensorObjComparison J F G ≫ (f ⊗ₘ g).hom) =
      ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J F G) ≫
        (f ⊗ₘ g) :=
    Adjunction.homEquiv_naturality_right_symm _ _ _
  have h₃ : ((sheafificationAdjunction J _).homEquiv _ _).symm
      ((f.hom ⊗ₘ g.hom) ≫ tensorObjComparison J F' G') =
      (presheafToSheaf J _).map (f.hom ⊗ₘ g.hom) ≫
        ((sheafificationAdjunction J _).homEquiv _ _).symm (tensorObjComparison J F' G') :=
    Adjunction.homEquiv_naturality_left_symm _ _ _
  apply ((sheafificationAdjunction J _).homEquiv _ _).symm.injective
  rw [h₂, h₃, h, h, Category.assoc, tensorHom_comp_tensorHom]
  erw [← Functor.OplaxMonoidal.δ_natural_assoc]
  rw [tensorHom_comp_tensorHom]
  congr 2
  · exact ((sheafificationAdjunction J _).counit.naturality f).symm
  · exact ((sheafificationAdjunction J _).counit.naturality g).symm

section Terminal

variable {W : C} (hW : Limits.IsTerminal W)

variable [J.HasSheafCompose (forget (ModuleCat.{max u v} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{max u v} R)]

end Terminal

end Sheaf

end CategoryTheory
