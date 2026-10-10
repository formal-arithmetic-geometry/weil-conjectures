/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf

/-!

# Sheaves of commutative rings as commutative ring objects of abelian sheaves

A sheaf of commutative rings `S : Sheaf J CommRingCat` has an underlying abelian sheaf,
obtained by forgetting first to sheaves of rings and then to abelian sheaves. By
`WeilConjectures.CategoryTheory.RingObjects.RingPresheaf` it is a ring object of `Sheaf J Ab`
(`CategoryTheory.Sheaf.monObj_sheafCompose_obj`), and it is commutative since its sections
are commutative rings. A morphism of sheaves of commutative rings induces a morphism of ring
objects. This is the form in which the coefficient sheaves `ℤ_ℓ`, `ℚ_ℓ`, `E`, `𝒪_E` and `ℚ̄_ℓ` of
`WeilConjectures.CategoryTheory.RingObjects.Profinite.EllAdic` and their pullbacks to the
pro-étale site of a scheme are ring objects.

## Main definitions

* `CategoryTheory.Sheaf.toAb`: the abelian sheaf underlying a sheaf of commutative rings, a
  commutative ring object (`CategoryTheory.Sheaf.isCommMonObj_toAb`).
* `CategoryTheory.Sheaf.toAbMap`: the morphism of ring objects underlying a morphism of sheaves
  of commutative rings.

-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ RingCat.{w} Ab.{w})]

/-- The abelian sheaf underlying a sheaf of commutative rings `S`, obtained by forgetting first
to sheaves of rings and then to abelian sheaves. It is a commutative ring object of `Sheaf J Ab`
through `CategoryTheory.Sheaf.monObj_sheafCompose_obj`. -/
noncomputable abbrev toAb (S : Sheaf J CommRingCat.{w}) : Sheaf J Ab.{w} :=
  (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).obj
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)

lemma toAb_obj (S : Sheaf J CommRingCat.{w}) :
    (toAb J S).obj = S.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⋙ forget₂ RingCat.{w} Ab.{w} :=
  rfl

/-- The morphism of abelian sheaves underlying a morphism of sheaves of commutative rings. It is
a morphism of ring objects through `CategoryTheory.Sheaf.isMonHom_sheafCompose_map`. -/
noncomputable abbrev toAbMap {S T : Sheaf J CommRingCat.{w}} (f : S ⟶ T) : toAb J S ⟶ toAb J T :=
  (sheafCompose J (forget₂ RingCat.{w} Ab.{w})).map
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f)

lemma toAbMap_hom {S T : Sheaf J CommRingCat.{w}} (f : S ⟶ T) :
    (toAbMap J f).hom =
      Functor.whiskerRight f.hom
        (forget₂ CommRingCat.{w} RingCat.{w} ⋙ forget₂ RingCat.{w} Ab.{w}) :=
  rfl

variable [HasWeakSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The abelian sheaf underlying a sheaf of commutative rings is a commutative ring object. -/
instance isCommMonObj_toAb (S : Sheaf J CommRingCat.{w}) : IsCommMonObj (toAb J S) :=
  isCommMonObj_sheafCompose_obj J _ fun U (a b : S.obj.obj U) ↦ mul_comm a b

end CategoryTheory.Sheaf
