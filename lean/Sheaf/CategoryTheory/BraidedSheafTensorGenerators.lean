/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-!
# Braided sheaf tensor and its sheafification generators

Source: blueprint `sec-proetale-coefficients`,
`sk-def-sfb-module-pushforward-pullback/lem-sfb-pushforward-comp-monoidal.proof.md`,
first sentence (blueprint: lem-sfb-braided-sheaf-tensor-generators).

The structure below packages the entire conclusion, including the specified tensor
bifunctor, canonical comparisons, and both universal generator tests. No choice of a
monoidal structure is made from an unproved existence theorem.
-/

@[expose] public section

set_option autoImplicit false

universe w uA uC vC

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Sheaf

/-- The data asserted by the braided sheaf tensor lemma, on the prescribed sheafified
pointwise tensor. Source: blueprint `lem-sfb-pushforward-comp-monoidal.proof.md`, first
sentence, expanded by `lem-sfb-braided-sheaf-tensor-generators`, clauses 1--4
(blueprint: lem-sfb-braided-sheaf-tensor-generators).

`tensorObj_eq`, `tensorHom_heq`, and `tensorUnit_eq` prescribe the actual bifunctor
and unit. Heterogeneous equality only transports between the equal objects prescribed
by these equations. `cotensorator_heq` specifies the canonical inverse tensorator,
namely sheafification of the tensor of the two adjunction units. The tensorator is
therefore its unique inverse. `unitComparison_heq` specifies the identity comparison.
The presheaf generator maps used below are exactly `toSheafify`, whose type already
contains naturality in the site variable. -/
structure BraidedTensorGenerators
    {C : Type w} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify J A] where
  monoidal : MonoidalCategory (Sheaf J A)
  braided : @BraidedCategory (Sheaf J A) _ monoidal
  sheafification :
    @Functor.Braided (Cᵒᵖ ⥤ A) _ _ _ (Sheaf J A) _ monoidal braided
      (presheafToSheaf J A)
  tensorObj_eq : ∀ F G : Sheaf J A,
    monoidal.tensorObj F G = (presheafToSheaf J A).obj (F.obj ⊗ G.obj)
  tensorHom_heq : ∀ {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G'),
    HEq (@tensorHom (Sheaf J A) _ monoidal.toMonoidalCategoryStruct _ _ _ _ f g)
      ((presheafToSheaf J A).map (f.hom ⊗ₘ g.hom))
  tensorUnit_eq : monoidal.tensorUnit = (presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A))
  braiding_heq : ∀ F G : Sheaf J A,
    HEq (@BraidedCategory.braiding (Sheaf J A) _ monoidal braided F G).hom
      ((presheafToSheaf J A).map (β_ F.obj G.obj).hom)
  cotensorator_heq : ∀ P Q : Cᵒᵖ ⥤ A,
    HEq (@Functor.OplaxMonoidal.δ (Cᵒᵖ ⥤ A) _ _ (Sheaf J A) _ monoidal
      (presheafToSheaf J A) sheafification.toMonoidal.toOplaxMonoidal P Q)
      ((presheafToSheaf J A).map (toSheafify J P ⊗ₘ toSheafify J Q))
  unitComparison_heq :
    HEq (@Functor.LaxMonoidal.ε (Cᵒᵖ ⥤ A) _ _ (Sheaf J A) _ monoidal
      (presheafToSheaf J A) sheafification.toMonoidal.toLaxMonoidal)
      (𝟙 ((presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A))))
  tensorGenerators_naturality :
    ∀ {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G'),
      (f.hom ⊗ₘ g.hom) ≫ toSheafify J (F'.obj ⊗ G'.obj) =
        toSheafify J (F.obj ⊗ G.obj) ≫
          ((presheafToSheaf J A).map (f.hom ⊗ₘ g.hom)).hom
  tensorHom_bijective : ∀ F G H : Sheaf J A,
    Function.Bijective
      (fun h : (presheafToSheaf J A).obj (F.obj ⊗ G.obj) ⟶ H ↦
        toSheafify J (F.obj ⊗ G.obj) ≫ h.hom)
  unitHom_bijective : ∀ H : Sheaf J A,
    Function.Bijective
      (fun h : (presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A)) ⟶ H ↦
        toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫ h.hom)
  tensorHom_ext : ∀ (F G H : Sheaf J A)
      (f g : (presheafToSheaf J A).obj (F.obj ⊗ G.obj) ⟶ H),
    toSheafify J (F.obj ⊗ G.obj) ≫ f.hom =
      toSheafify J (F.obj ⊗ G.obj) ≫ g.hom → f = g
  unitHom_ext : ∀ (H : Sheaf J A)
      (f g : (presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A)) ⟶ H),
    toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫ f.hom =
      toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫ g.hom → f = g

section BraidedTensorProof

open CategoryTheory.Category
open scoped CategoryTheory.MonoidalClosed

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

/- Transport coherence along a natural comparison of tensor bifunctors. The copy keeps
   the old and prescribed monoidal instances separate during elaboration. -/
namespace Retensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
private def Copy (D : Type u) := D
private local instance copyCategory : Category (Copy D) := inferInstanceAs (Category D)
private def forget : Copy D ⥤ D := 𝟭 D
private local instance : (forget (D := D)).Faithful := inferInstanceAs (𝟭 D).Faithful
private local instance : (forget (D := D)).Full := inferInstanceAs (𝟭 D).Full
variable (T : D ⥤ D ⥤ D) (c : T ≅ curriedTensor D)
private abbrev cmp (X Y : D) := (c.app X).app Y
@[instance_reducible]
private def struct : MonoidalCategoryStruct (Copy D) where
  tensorObj X Y := (T.obj X).obj Y
  whiskerLeft X _ _ g := (T.obj X).map g
  whiskerRight f Y := (T.map f).app Y
  tensorHom f g := (T.map f).app _ ≫ (T.obj _).map g
  tensorUnit := 𝟙_ D
  associator X Y Z := cmp T c ((T.obj X).obj Y) Z ≪≫
    @tensorIso D _ _ _ _ _ _ (cmp T c X Y) (Iso.refl Z) ≪≫
    @associator D _ _ X Y Z ≪≫
    @tensorIso D _ _ _ _ _ _ (Iso.refl X) (cmp T c Y Z).symm ≪≫
    (cmp T c X ((T.obj Y).obj Z)).symm
  leftUnitor X := cmp T c (𝟙_ D) X ≪≫ @leftUnitor D _ _ X
  rightUnitor X := cmp T c X (𝟙_ D) ≪≫ @rightUnitor D _ _ X
set_option backward.defeqAttrib.useBackward true in
private def data : letI := struct T c; Monoidal.InducingFunctorData (forget (D := D)) := by
  letI := struct T c
  refine { μIso := fun X Y ↦ (cmp T c X Y).symm
           εIso := Iso.refl _
           whiskerLeft_eq := ?_
           whiskerRight_eq := ?_
           tensorHom_eq := ?_
           associator_eq := ?_
           leftUnitor_eq := ?_
           rightUnitor_eq := ?_ }
  · intro X Y Y' f
    change (T.obj X).map f =
      (cmp T c X Y).hom ≫ ((forget (D := D)).obj X ◁ (forget (D := D)).map f) ≫ (cmp T c X Y').inv
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact (c.hom.app X).naturality f
  · intro X X' f Y
    change (T.map f).app Y =
      (cmp T c X Y).hom ≫ ((forget (D := D)).map f ▷ (forget (D := D)).obj Y) ≫ (cmp T c X' Y).inv
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact NatTrans.naturality_app c.hom Y f
  · intro X X' Y Y' f g
    change (T.map f).app Y ≫ (T.obj X').map g =
      (cmp T c X Y).hom ≫ ((forget (D := D)).map f ⊗ₘ (forget (D := D)).map g) ≫ (cmp T c X' Y').inv
    rw [← Category.assoc, Iso.eq_comp_inv]
    change _ = (c.hom.app X).app Y ≫ ((forget (D := D)).map f ⊗ₘ (forget (D := D)).map g)
    change ((T.map f).app Y ≫ (T.obj X').map g) ≫ (c.hom.app X').app Y' =
      (c.hom.app X).app Y ≫ ((forget (D := D)).map f ⊗ₘ (forget (D := D)).map g)
    rw [Category.assoc, (c.hom.app X').naturality g, ← Category.assoc,
      NatTrans.naturality_app c.hom Y f, Category.assoc, tensorHom_def]
    rfl
  · intros
    dsimp +instances only [struct, forget]
    simp only [Iso.trans_hom, Category.assoc]
    rfl
  · intro X
    dsimp +instances only [struct, forget]
    simp
  · intro X
    dsimp +instances only [struct, forget]
    simp
@[instance_reducible]
private def monoidal : MonoidalCategory (Copy D) :=
  letI := struct T c
  Monoidal.induced (forget (D := D)) (data T c)
private local instance : letI := monoidal T c; (forget (D := D)).Monoidal :=
  letI := struct T c
  Monoidal.fromInducedMonoidal _ (data T c)
private def equivalence : Copy D ≌ D := CategoryTheory.Equivalence.refl
variable [BraidedCategory D]
@[instance_reducible]
private noncomputable def braided : letI := monoidal T c; BraidedCategory (Copy D) := by
  letI := monoidal T c
  letI : (forget (D := D)).Monoidal := inferInstance
  exact BraidedCategory.ofFaithful (forget (D := D))
    (fun X Y ↦ cmp T c X Y ≪≫ @BraidedCategory.braiding D _ _ _ X Y ≪≫
      (cmp T c Y X).symm)
    (fun X Y ↦ by
      simp +instances [Monoidal.fromInducedCoreMonoidal,
        Functor.CoreMonoidal.toLaxMonoidal, data, forget])
@[instance_reducible]
private noncomputable def inverseMonoidal :
    letI := monoidal T c
    (equivalence (D := D)).inverse.Monoidal := by
  letI := monoidal T c
  letI : (equivalence (D := D)).functor.Monoidal := inferInstanceAs
    (forget (D := D)).Monoidal
  exact (equivalence (D := D)).inverseMonoidal
omit [BraidedCategory D] in
private theorem inverse_μ (X Y : D) :
    let := monoidal T c
    let := inverseMonoidal T c
    Functor.LaxMonoidal.μ (equivalence (D := D)).inverse X Y = (cmp T c X Y).hom := by
  let := monoidal T c
  let := inverseMonoidal T c
  simp +instances only [equivalence, CategoryTheory.Equivalence.refl, Functor.id_obj,
    inverseMonoidal,
    Equivalence.inverseMonoidal, data, forget, curriedTensor_obj_obj,
    Monoidal.fromInducedMonoidal, Monoidal.fromInducedCoreMonoidal,
    Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
    Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    Functor.CoreMonoidal.toOplaxMonoidal, Iso.refl_inv, Iso.symm_inv, Iso.app_hom,
    Adjunction.rightAdjointLaxMonoidal_μ, Equivalence.toAdjunction_counit,
    Equivalence.Equivalence_mk'_counit, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_obj, tensorHom_id, id_whiskerRight, comp_id]
  erw [Adjunction.homEquiv_unit]
  simp
omit [BraidedCategory D] in
private theorem inverse_δ (X Y : D) :
    let := monoidal T c
    let := inverseMonoidal T c
    Functor.OplaxMonoidal.δ (equivalence (D := D)).inverse X Y = (cmp T c X Y).inv := by
  let := monoidal T c
  let := inverseMonoidal T c
  apply (cancel_epi (Functor.LaxMonoidal.μ (equivalence (D := D)).inverse X Y)).1
  rw [Functor.Monoidal.μ_δ, inverse_μ]
  exact (cmp T c X Y).hom_inv_id.symm
omit [BraidedCategory D] in
private theorem inverse_ε :
    let := monoidal T c
    let := inverseMonoidal T c
    Functor.LaxMonoidal.ε (equivalence (D := D)).inverse = 𝟙 (𝟙_ D) := by
  let := monoidal T c
  let := inverseMonoidal T c
  simp +instances only [equivalence, CategoryTheory.Equivalence.refl, Functor.id_obj,
    inverseMonoidal,
    Equivalence.inverseMonoidal, data, forget, curriedTensor_obj_obj,
    Monoidal.fromInducedMonoidal, Monoidal.fromInducedCoreMonoidal,
    Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
    Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    Functor.CoreMonoidal.toOplaxMonoidal, Iso.refl_inv, Iso.symm_inv, Iso.app_hom,
    Adjunction.rightAdjointLaxMonoidal_ε]
  erw [Adjunction.homEquiv_unit]
  simp
@[instance_reducible]
private noncomputable def inverseBraided :
    letI := monoidal T c
    letI := braided T c
    (equivalence (D := D)).inverse.Braided := by
  letI := monoidal T c
  letI := braided T c
  letI := inverseMonoidal T c
  refine { braided := fun X Y ↦ ?_ }
  rw [inverse_μ, inverse_μ]
  change (cmp T c X Y).hom ≫ (β_ X Y).hom =
    ((cmp T c X Y).hom ≫ (β_ X Y).hom ≫ (cmp T c Y X).inv) ≫
      (cmp T c Y X).hom
  simp
end Retensor
attribute [local instance] Retensor.copyCategory
variable {C : Type w} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify J A]
private local instance globalEnds (F G : Cᵒᵖ ⥤ A) : Enriched.FunctorCategory.HasEnrichedHom A F G :=
  inferInstance
private local instance sliceEnds (F G : Cᵒᵖ ⥤ A) :
    Enriched.FunctorCategory.HasFunctorEnrichedHom A F G :=
  inferInstance
private noncomputable def prescribedTensor : Sheaf J A ⥤ Sheaf J A ⥤ Sheaf J A where
  obj F := sheafToPresheaf J A ⋙ tensorLeft F.obj ⋙ presheafToSheaf J A
  map f :=
    { app G := (presheafToSheaf J A).map (f.hom ▷ G.obj)
      naturality G G' g := by
        dsimp
        simp only [← Functor.map_comp, whisker_exchange] }
  map_id F := by ext G; simp
  map_comp f g := by ext G; simp
private noncomputable def comparison (F G : Sheaf J A) :
    letI : MonoidalCategory (Sheaf J A) := Sheaf.monoidalCategory J A
    (prescribedTensor J A |>.obj F).obj G ≅ F ⊗ G := by
  letI : MonoidalCategory (Sheaf J A) := Sheaf.monoidalCategory J A
  exact (Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).symm ≪≫
    (asIso ((sheafificationAdjunction J A).counit.app F) ⊗ᵢ
      asIso ((sheafificationAdjunction J A).counit.app G))
private noncomputable def comparisonNatIso :
    letI : MonoidalCategory (Sheaf J A) := Sheaf.monoidalCategory J A
    prescribedTensor J A ≅ curriedTensor (Sheaf J A) := by
  letI : MonoidalCategory (Sheaf J A) := Sheaf.monoidalCategory J A
  refine NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun G ↦ comparison J A F G)
    (fun {G G'} g ↦ ?_)) (fun {F F'} f ↦ ?_)
  · dsimp [comparison, prescribedTensor]
    simp only [Category.assoc, ← Functor.OplaxMonoidal.δ_natural_right_assoc,
      tensorHom_def']
    have h := (sheafificationAdjunction J A).counit.naturality g
    change (presheafToSheaf J A).map g.hom ≫
      (sheafificationAdjunction J A).counit.app G' =
      (sheafificationAdjunction J A).counit.app G ≫ g at h
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, h,
      MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [whisker_exchange, whisker_exchange_assoc]
  · apply NatTrans.ext
    funext G
    dsimp [comparison, prescribedTensor]
    simp only [Category.assoc, ← Functor.OplaxMonoidal.δ_natural_left_assoc,
      tensorHom_def]
    have h := (sheafificationAdjunction J A).counit.naturality f
    change (presheafToSheaf J A).map f.hom ≫
      (sheafificationAdjunction J A).counit.app F' =
      (sheafificationAdjunction J A).counit.app F ≫ f at h
    rw [← comp_whiskerRight_assoc, h, comp_whiskerRight_assoc]
    simp only [whisker_exchange]

/-- Closed braided Grothendieck coefficients give the canonical braided structure on
exactly the sheafified pointwise tensor, together with its two generator tests.
Source: blueprint `lem-sfb-pushforward-comp-monoidal.proof.md`, first sentence
(blueprint: lem-sfb-braided-sheaf-tensor-generators).

Proof. 1. The coefficient tensor, associator, unitors and braiding act pointwise on
presheaves; all coherence equations hold at each object.
2. The sheafification adjunction identifies the Hom-defined local maps with maps
inverted by sheafification. Its unit is local and its counit is invertible, since
sheaves form a full subcategory.
3. Grothendieck coefficients with morphisms in universe `w` have all `w`-small limits
(`lem-coef-grothendieck-small-limits`). The internal-hom end construction and
`lem-sfb-local-equivalences-braided-tensor` show that local maps are stable under
both tensorings, using the braiding without symmetry. In particular the tensor of
two sheafification units becomes invertible after sheafification.
4. The reflector is a localization: a functor inverting local maps extends by
composition with the inclusion, and its unit and counit give inverse equivalences
on the corresponding functor categories, also on natural transformations.
5. Apply `lem-sfb-braided-monoidal-localization` to obtain the localized braided
structure with unit the sheafification of the constant tensor unit.
6. The localization tensor is naturally isomorphic to the prescribed bifunctor
`(F,G) ↦ a(UF ⊗ UG)` via the inverse tensorator followed by the two counits.
Conjugate associators, unitors and braiding by this comparison. On a coherence
path the successive comparison and inverse-comparison factors cancel, reducing
pentagon, triangle and both hexagons to the localized equations.
7. Naturality of the old tensorator and the adjunction triangle identities show
that the new inverse tensorator is `a(η_P ⊗ η_Q)`, the unit comparison is the
identity, and the braiding is `a(β_(UF,UG))`. Transport of the old functor coherence
equations proves that sheafification is strong braided monoidal.
8. The maps `t` and `u` are the actual sheafification units. Their types make them
presheaf natural transformations, and naturality of the adjunction unit at
`Uf ⊗ Ug` gives simultaneous sheaf naturality of `t`. The adjunction Hom equivalence
at `UF ⊗ UG` and at the constant unit gives both displayed bijections. Their
injectivity gives the two equality tests. -/
theorem nonempty_braidedTensorGenerators
    {C : Type w} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify J A] : Nonempty (BraidedTensorGenerators J A) := by
  let : MonoidalCategory (Sheaf J A) := Sheaf.monoidalCategory J A
  let : BraidedCategory (Sheaf J A) := Sheaf.braidedCategory J A
  let T := prescribedTensor J A
  let c := comparisonNatIso J A
  let : MonoidalCategory (Retensor.Copy (Sheaf J A)) := Retensor.monoidal T c
  let : BraidedCategory (Retensor.Copy (Sheaf J A)) := Retensor.braided T c
  let : (Retensor.equivalence (D := Sheaf J A)).inverse.Braided := Retensor.inverseBraided T c
  let L : (Cᵒᵖ ⥤ A) ⥤ Retensor.Copy (Sheaf J A) :=
    presheafToSheaf J A ⋙ (Retensor.equivalence (D := Sheaf J A)).inverse
  let lb : L.Braided := inferInstance
  refine ⟨{ monoidal := Retensor.monoidal T c
            braided := Retensor.braided T c
            sheafification := lb
            tensorObj_eq := ?_
            tensorHom_heq := ?_
            tensorUnit_eq := ?_
            braiding_heq := ?_
            cotensorator_heq := ?_
            unitComparison_heq := ?_
            tensorGenerators_naturality := ?_
            tensorHom_bijective := ?_
            unitHom_bijective := ?_
            tensorHom_ext := ?_
            unitHom_ext := ?_ }⟩
  · intro F G
    rfl
  · intro F F' G G' f g
    apply heq_of_eq
    change (presheafToSheaf J A).map (f.hom ▷ G.obj) ≫
      (presheafToSheaf J A).map (F'.obj ◁ g.hom) = _
    rw [← Functor.map_comp, tensorHom_def]
  · rfl
  · intro F G
    apply heq_of_eq
    change (comparison J A F G).hom ≫ (β_ F G).hom ≫
      (comparison J A G F).inv = (presheafToSheaf J A).map (β_ F.obj G.obj).hom
    simp [comparison]
  · intro P Q
    apply heq_of_eq
    change Functor.OplaxMonoidal.δ L P Q = _
    simp only [L, Functor.OplaxMonoidal.comp_δ, Retensor.inverse_δ]
    simp only [c, comparisonNatIso, comparison]
    change Functor.OplaxMonoidal.δ (presheafToSheaf J A) P Q ≫
      (inv ((sheafificationAdjunction J A).counit.app ((presheafToSheaf J A).obj P)) ⊗ₘ
        inv ((sheafificationAdjunction J A).counit.app ((presheafToSheaf J A).obj Q))) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J A) _ _ = _
    have h (R : Cᵒᵖ ⥤ A) :
        inv ((sheafificationAdjunction J A).counit.app ((presheafToSheaf J A).obj R)) =
          (presheafToSheaf J A).map (toSheafify J R) := by
      apply (cancel_mono ((sheafificationAdjunction J A).counit.app _)).1
      simp [← sheafificationAdjunction_unit_app]
    rw [h P, h Q]
    erw [Functor.LaxMonoidal.μ_natural, Functor.Monoidal.δ_μ_assoc]
  · apply heq_of_eq
    change Functor.LaxMonoidal.ε L = _
    simp only [L, Functor.LaxMonoidal.comp_ε, Retensor.inverse_ε]
    change 𝟙 _ ≫ 𝟙 _ = _
    rw [Category.id_comp]
    rfl
  · intro F F' G G' f g
    exact (sheafificationAdjunction J A).unit.naturality (f.hom ⊗ₘ g.hom)
  · intro F G H
    exact (sheafificationAdjunction J A).homEquiv _ _ |>.bijective
  · intro H
    exact (sheafificationAdjunction J A).homEquiv _ _ |>.bijective
  · intro F G H f g h
    exact ((sheafificationAdjunction J A).homEquiv _ _).injective h
  · intro H f g h
    exact ((sheafificationAdjunction J A).homEquiv _ _).injective h

/-- The same assertions for an essentially small site, explicitly after passage to its
small skeleton with the induced topology. Source: blueprint
`lem-sfb-pushforward-comp-monoidal.proof.md`, first sentence; the small-skeleton clause
of `lem-sfb-braided-sheaf-tensor-generators`
(blueprint: lem-sfb-braided-sheaf-tensor-generators).

Proof (step 9 of the node). Take `Skeleton (SmallModel C)`, using
`skeletonEquivalence` and the inverse of
`equivSmallModel C` to include it into the original site. Pull the topology back along
this composite equivalence, and apply the small-site
assertion `nonempty_braidedTensorGenerators` there. All ends and Hom tests are now
indexed in universe `w`; no ends over the original large object type are required. -/
theorem nonempty_braidedTensorGenerators_smallSkeleton
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A] :
    Nonempty (BraidedTensorGenerators
      (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A) := by
  exact nonempty_braidedTensorGenerators _ A

end BraidedTensorProof

end CategoryTheory.Sheaf
