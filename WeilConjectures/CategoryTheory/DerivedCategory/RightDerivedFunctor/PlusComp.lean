/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Composition of right derived functors on bounded below derived categories

This is the bounded below counterpart of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`. Let `F : C ⥤ D` and
`G : D ⥤ E` be additive functors between abelian categories, with `C` and `D` having
enough injectives. If `F` preserves injective objects, then the canonical comparison

`R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`

is an isomorphism (`Functor.rightDerivedFunctorPlusCompIso`).

## Why this is not a corollary of the unbounded statement

`Functor.rightDerivedFunctorCompIso` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` proves the same
theorem for the unbounded derived category, but it assumes `HasKInjectiveResolutions` on
both `C` and `D`, whose only source in this repository is a `sorry`. The bounded below
statement needs only
enough injectives, so it rests on proved theorems; see
`WeilConjectures.SixFunctors.Derived` for why that distinction matters here. This file
therefore deliberately does not import anything from
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.

## The proof, and where it differs from the unbounded one

The shape is the same: the composite `R⁺F ⋙ R⁺G`, equipped with the composite unit
`Functor.rightDerivedFunctorPlusCompUnit`, is itself a right derived functor of
`(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`, and the isomorphism then follows from uniqueness
of right derived functors.

The hypothesis on `F` is where the two arguments part company. The unbounded derivability
structure is indexed by K-injective complexes, so there the requirement is that `F` send
K-injective complexes to K-injective complexes
(`Functor.PreservesKInjectiveComplexes`). The bounded below derivability structure is
indexed by bounded below complexes of *injective objects*, so here the requirement is only
that `F` preserve injective objects — Mathlib's `Functor.PreservesInjectiveObjects`, which
for a right adjoint of a monomorphism-preserving functor is
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`. That is a
weaker and much more readily available hypothesis than the K-injective one, which needs the
left adjoint to be exact.

Concretely, the check that the composite unit is invertible at a bounded below complex `K`
of injectives uses Mathlib's criterion that the unit of a bounded below right derived
functor is invertible at any complex all of whose terms are injective
(the instance in `Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean`).
Applied to `G` this is exactly where `F.PreservesInjectiveObjects` enters: the terms of
`F.mapHomotopyCategoryPlus.obj K` are the `F.obj (K.X n)`, injective because `F` preserves
injectives.

## Main definitions

- `CategoryTheory.Functor.rightDerivedFunctorPlusNatTrans` and
  `Functor.rightDerivedFunctorPlusNatIso`: functoriality of the bounded below right derived
  functor in natural transformations of the underived functors.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`: the composition isomorphism
  `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`.
- `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'`: the composition isomorphism
  `R⁺F ⋙ R⁺G ≅ R⁺H` associated with an isomorphism `F ⋙ G ≅ H`. This is the form in which
  the theorem is usually applied, e.g. for the Leray isomorphism.
- `CategoryTheory.Functor.rightDerivedFunctorPlusIdIso`: the identity isomorphism
  `R⁺(𝟭 C) ≅ 𝟭`, expressing that the identity functor is its own right derived functor.

Both composition isomorphisms are characterized by their compatibility with the units of the
right derived functors, in `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_fac` and
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'_fac`.

## Coherence

`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_id_comp`,
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_comp_id` and
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_assoc` are the unit and
associativity laws relating `rightDerivedFunctorPlusCompIso` and
`rightDerivedFunctorPlusIdIso`, i.e. the coherence of `R⁺` as a pseudofunctor. They are
proved from the characterizations by the units, using that the comparison isomorphisms
`Functor.mapHomotopyCategoryPlusIdIso` and
`Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))` of the bounded below homotopy
categories are the identity.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

namespace Functor

section NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Functoriality of the bounded below right derived functor: a natural transformation
`F ⟶ G` of additive functors induces a natural transformation
`R⁺F ⟶ R⁺G : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`. -/
noncomputable def rightDerivedFunctorPlusNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : F.rightDerivedFunctorPlus ⟶ G.rightDerivedFunctorPlus :=
  rightDerivedNatTrans F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus τ) DerivedCategory.Plus.Qh)

/-- Functoriality of the bounded below right derived functor in natural isomorphisms: an
isomorphism `F ≅ G` of additive functors induces an isomorphism `R⁺F ≅ R⁺G`. -/
noncomputable def rightDerivedFunctorPlusNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) : F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus where
  hom := rightDerivedFunctorPlusNatTrans e.hom
  inv := rightDerivedFunctorPlusNatTrans e.inv
  hom_inv_id := by
    simp [rightDerivedFunctorPlusNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategoryPlus_comp]
  inv_hom_id := by
    simp [rightDerivedFunctorPlusNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategoryPlus_comp]

/-- The natural transformation induced on bounded below right derived functors by a natural
isomorphism is an isomorphism. -/
instance isIso_rightDerivedFunctorPlusNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) [IsIso τ] : IsIso (rightDerivedFunctorPlusNatTrans τ) :=
  inferInstanceAs (IsIso (rightDerivedFunctorPlusNatIso (asIso τ)).hom)

end NatTrans

section Composition

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The composite unit exhibiting `R⁺F ⋙ R⁺G` as a candidate right derived functor of
`(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`: it is assembled from the units of `R⁺F` and `R⁺G`
and the composition isomorphism of `mapHomotopyCategoryPlus`. -/
noncomputable def rightDerivedFunctorPlusCompUnit :
    (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- If `F` preserves injective objects, then `R⁺F ⋙ R⁺G`, equipped with the composite unit,
is a right derived functor of `(F ⋙ G).mapHomotopyCategoryPlus ⋙ Qh`: by the injective
right derivability structure it suffices that the composite unit is an isomorphism on
bounded below complexes of injectives, which holds since the unit of `R⁺F` is an
isomorphism there and the unit of `R⁺G` is an isomorphism on their images under `F`, those
being complexes of injectives again. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp [F.PreservesInjectiveObjects] :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (HomotopyCategory.Plus.quasiIso C) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  set K : HomotopyCategory.Plus C := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁
    with hK
  have hKinj : ∀ n : ℤ, Injective (K.obj.as.X n) := fun n => inferInstance
  have h₁ : IsIso (F.rightDerivedFunctorPlusUnit.app K) := inferInstance
  have hFinj : ∀ n : ℤ, Injective ((F.mapHomotopyCategoryPlus.obj K).obj.as.X n) := fun n =>
    inferInstanceAs (Injective (F.obj (K.obj.as.X n)))
  have h₂ : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K)) := by
    have := hFinj
    infer_instance
  dsimp [rightDerivedFunctorPlusCompUnit]
  infer_instance

/-- **Composition of bounded below right derived functors**: for additive functors
`F : C ⥤ D` and `G : D ⥤ E` between abelian categories with enough injectives, where `F`
preserves injective objects, the canonical comparison `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G` is an
isomorphism. -/
noncomputable def rightDerivedFunctorPlusCompIso [F.PreservesInjectiveObjects] :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
    (HomotopyCategory.Plus.quasiIso C)

/-- The composition isomorphism `Functor.rightDerivedFunctorPlusCompIso` is characterized by
its compatibility with the units: composing the unit of `R⁺(F ⋙ G)` with it gives the
composite unit `Functor.rightDerivedFunctorPlusCompUnit`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompIso_fac [F.PreservesInjectiveObjects] :
    (F ⋙ G).rightDerivedFunctorPlusUnit ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (rightDerivedFunctorPlusCompIso F G).hom =
      rightDerivedFunctorPlusCompUnit F G := by
  simp [rightDerivedFunctorPlusCompIso]

/-- The pointwise form of `Functor.rightDerivedFunctorPlusCompIso_fac`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompIso_fac_app [F.PreservesInjectiveObjects]
    (K : HomotopyCategory.Plus C) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) =
      (rightDerivedFunctorPlusCompUnit F G).app K :=
  NatTrans.congr_app (rightDerivedFunctorPlusCompIso_fac F G) K

/-- The composite unit `Functor.rightDerivedFunctorPlusCompUnit` is pointwise the composite
of the units of `R⁺G` and `R⁺F`: the comparison isomorphism
`Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))` occurring in its definition is
the identity. -/
lemma rightDerivedFunctorPlusCompUnit_app (K : HomotopyCategory.Plus C) :
    (rightDerivedFunctorPlusCompUnit F G).app K =
      G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  simp [rightDerivedFunctorPlusCompUnit, mapHomotopyCategoryPlusCompIso_refl_inv_app]

/-- The pointwise form of `Functor.rightDerivedFunctorPlusCompIso_fac`, with the composite
unit spelled out: the composition isomorphism turns the unit of `R⁺(F ⋙ G)` into the
composite of the units of `R⁺G` and `R⁺F`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompIso_fac_app' [F.PreservesInjectiveObjects]
    (K : HomotopyCategory.Plus C) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIso F G).hom.app (DerivedCategory.Plus.Qh.obj K) =
      G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) :=
  (rightDerivedFunctorPlusCompIso_fac_app F G K).trans
    (rightDerivedFunctorPlusCompUnit_app F G K)

/-- The composition isomorphism `R⁺F ⋙ R⁺G ≅ R⁺H` associated with an isomorphism
`F ⋙ G ≅ H` of additive functors, for `F` preserving injective objects. This is the form in
which the composition theorem is usually applied, e.g. for the Leray isomorphism
`RΓ(Y, R⁺f_* K) ≅ RΓ(X, K)`. -/
noncomputable def rightDerivedFunctorPlusCompIso' {H : C ⥤ E} [H.Additive]
    [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H) :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅ H.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIso F G).symm ≪≫ rightDerivedFunctorPlusNatIso e

/-- The composition isomorphism `Functor.rightDerivedFunctorPlusCompIso'` attached to an
isomorphism `e : F ⋙ G ≅ H` is characterized by its compatibility with the units: composing
the composite unit with it gives the unit of `R⁺H`, transported along `e`. -/
@[reassoc]
lemma rightDerivedFunctorPlusCompIso'_fac {H : C ⥤ E} [H.Additive]
    [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H) :
    rightDerivedFunctorPlusCompUnit F G ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
        (rightDerivedFunctorPlusCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus e.hom) DerivedCategory.Plus.Qh ≫
        H.rightDerivedFunctorPlusUnit := by
  rw [← rightDerivedFunctorPlusCompIso_fac F G, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [rightDerivedFunctorPlusCompIso', Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact rightDerivedNatTrans_fac _ _ _ _ (HomotopyCategory.Plus.quasiIso C) _

end Composition

section Identity

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]
  [EnoughInjectives C]

/-- The unit exhibiting the identity functor of `DerivedCategory.Plus C` as a right derived
functor of `(𝟭 C).mapHomotopyCategoryPlus ⋙ Qh`. It is an isomorphism: the functor
`(𝟭 C).mapHomotopyCategoryPlus ⋙ Qh` is `Qh` itself, which already inverts the
quasi-isomorphisms. -/
noncomputable def rightDerivedFunctorPlusIdUnit :
    (𝟭 C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ 𝟭 (DerivedCategory.Plus C) :=
  Functor.whiskerRight (mapHomotopyCategoryPlusIdIso C).hom DerivedCategory.Plus.Qh ≫
    DerivedCategory.Plus.Qh.leftUnitor.hom ≫ DerivedCategory.Plus.Qh.rightUnitor.inv

instance : IsIso (rightDerivedFunctorPlusIdUnit C) := by
  dsimp only [rightDerivedFunctorPlusIdUnit]
  infer_instance

instance isRightDerivedFunctor_id_rightDerivedFunctorPlusIdUnit :
    (𝟭 (DerivedCategory.Plus C)).IsRightDerivedFunctor (rightDerivedFunctorPlusIdUnit C)
      (HomotopyCategory.Plus.quasiIso C) :=
  isRightDerivedFunctor_of_inverts _ _ (asIso (rightDerivedFunctorPlusIdUnit C)).symm

/-- **The identity functor is its own bounded below right derived functor**: the canonical
comparison `R⁺(𝟭 C) ≅ 𝟭` is an isomorphism. -/
noncomputable def rightDerivedFunctorPlusIdIso :
    (𝟭 C).rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus C) :=
  rightDerivedUnique (𝟭 C).rightDerivedFunctorPlus (𝟭 (DerivedCategory.Plus C))
    (𝟭 C).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusIdUnit C)
    (HomotopyCategory.Plus.quasiIso C)

/-- The characterization of `Functor.rightDerivedFunctorPlusIdIso`: it transforms the unit of
`R⁺(𝟭 C)` into the identity, up to the unitors. -/
@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso :
    (𝟭 C).rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusIdIso C).hom =
      rightDerivedFunctorPlusIdUnit C := by
  simp [rightDerivedFunctorPlusIdIso]

/-- The pointwise form of
`Functor.rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso`: the identity
isomorphism `Functor.rightDerivedFunctorPlusIdIso` turns the unit of `R⁺(𝟭 C)` into
`Functor.mapHomotopyCategoryPlusIdIso`. -/
@[reassoc]
lemma rightDerivedFunctorPlusIdIso_fac_app (K : HomotopyCategory.Plus C) :
    (𝟭 C).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusIdIso C).hom.app K) := by
  have := congr_app (rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso C) K
  simpa [rightDerivedFunctorPlusIdUnit,
    -rightDerivedFunctorPlusUnit_comp_rightDerivedFunctorPlusIdIso] using this

/-- Sharpened form of `Functor.rightDerivedFunctorPlusIdIso_fac_app`: since
`Functor.mapHomotopyCategoryPlusIdIso` is the identity, the identity isomorphism
`Functor.rightDerivedFunctorPlusIdIso` is inverse to the unit of `R⁺(𝟭 C)`. -/
@[reassoc]
lemma rightDerivedFunctorPlusIdIso_fac_app' (K : HomotopyCategory.Plus C) :
    (𝟭 C).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K) =
      𝟙 (DerivedCategory.Plus.Qh.obj K) := by
  rw [rightDerivedFunctorPlusIdIso_fac_app, mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
  exact DerivedCategory.Plus.Qh.map_id K

end Identity

section Coherence

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- The left unit law for `Functor.rightDerivedFunctorPlusCompIso`: the composition
isomorphism for `𝟭 C` and `G`, followed by the identity isomorphism
`Functor.rightDerivedFunctorPlusIdIso`, is the identity. -/
lemma rightDerivedFunctorPlusCompIso_id_comp [EnoughInjectives C] (G : C ⥤ D) [G.Additive] :
    (rightDerivedFunctorPlusCompIso (𝟭 C) G).hom ≫
        Functor.whiskerRight (rightDerivedFunctorPlusIdIso C).hom G.rightDerivedFunctorPlus =
      𝟙 G.rightDerivedFunctorPlus := by
  refine (𝟭 C ⋙ G).rightDerivedFunctorPlus.rightDerived_ext
    (𝟭 C ⋙ G).rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app]
  have hmap : G.rightDerivedFunctorPlus.map ((𝟭 C).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusIdIso C).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      𝟙 (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) :=
    (congrArg G.rightDerivedFunctorPlus.map
      (rightDerivedFunctorPlusIdIso_fac_app' C K)).trans
      (G.rightDerivedFunctorPlus.map_id _)
  refine Eq.trans ?_ (Category.comp_id _).symm
  rw [← Category.assoc, rightDerivedFunctorPlusCompIso_fac_app', Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  exact (congrArg (fun f => G.rightDerivedFunctorPlusUnit.app
    ((𝟭 C).mapHomotopyCategoryPlus.obj K) ≫ f) hmap).trans (Category.comp_id _)

/-- The right unit law for `Functor.rightDerivedFunctorPlusCompIso`: the composition
isomorphism for `F` and `𝟭 D`, followed by the identity isomorphism
`Functor.rightDerivedFunctorPlusIdIso`, is the identity. -/
lemma rightDerivedFunctorPlusCompIso_comp_id [EnoughInjectives C] [EnoughInjectives D]
    (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] :
    (rightDerivedFunctorPlusCompIso F (𝟭 D)).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusIdIso D).hom =
      𝟙 F.rightDerivedFunctorPlus := by
  refine (F ⋙ 𝟭 D).rightDerivedFunctorPlus.rightDerived_ext
    (F ⋙ 𝟭 D).rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  have hnat : (𝟭 D).rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedFunctorPlusIdIso D).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (rightDerivedFunctorPlusIdIso D).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        F.rightDerivedFunctorPlusUnit.app K :=
    (rightDerivedFunctorPlusIdIso D).hom.naturality _
  rw [← Category.assoc, rightDerivedFunctorPlusCompIso_fac_app', Category.assoc, hnat,
    ← Category.assoc, rightDerivedFunctorPlusIdIso_fac_app']
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The associativity law for `Functor.rightDerivedFunctorPlusCompIso`: the two ways of
comparing `R⁺(F ⋙ G ⋙ H)` with `R⁺F ⋙ R⁺G ⋙ R⁺H` agree. -/
lemma rightDerivedFunctorPlusCompIso_assoc {E' : Type u₄} [Category.{v₄} E'] [Abelian E']
    [HasDerivedCategory E'] [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives E]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects] :
    (rightDerivedFunctorPlusCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIso G H).hom =
      (rightDerivedFunctorPlusCompIso (F ⋙ G) H).hom ≫
        Functor.whiskerRight (rightDerivedFunctorPlusCompIso F G).hom
          H.rightDerivedFunctorPlus := by
  refine (F ⋙ G ⋙ H).rightDerivedFunctorPlus.rightDerived_ext
    (F ⋙ G ⋙ H).rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hnat : (G ⋙ H).rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedFunctorPlusCompIso G H).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (rightDerivedFunctorPlusCompIso G H).hom.app
          (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlus.map
          (F.rightDerivedFunctorPlusUnit.app K)) :=
    (rightDerivedFunctorPlusCompIso G H).hom.naturality _
  have facAssoc : (F ⋙ G ⋙ H).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompIso (F ⋙ G) H).hom.app
          (DerivedCategory.Plus.Qh.obj K) =
      H.rightDerivedFunctorPlusUnit.app
          (G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
        H.rightDerivedFunctorPlus.map ((F ⋙ G).rightDerivedFunctorPlusUnit.app K) :=
    rightDerivedFunctorPlusCompIso_fac_app' (F ⋙ G) H K
  rw [← Category.assoc, rightDerivedFunctorPlusCompIso_fac_app', Category.assoc, hnat,
    ← Category.assoc, rightDerivedFunctorPlusCompIso_fac_app', Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← Category.assoc, facAssoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, rightDerivedFunctorPlusCompIso_fac_app']

end Coherence

end Functor

end CategoryTheory
