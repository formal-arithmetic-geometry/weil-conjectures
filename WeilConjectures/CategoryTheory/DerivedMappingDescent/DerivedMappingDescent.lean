/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering

/-! # Descent of maps of derived mapping bifunctors

Source: the replacement-of-representatives argument in Stacks Project, Tag 070I.
(blueprint: lem-sf-derived-mapping-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace CategoryTheory.DerivedMappingDescent

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (P : C ⥤ D) [P.Full] [P.EssSurj] {F G : D ⥤ E}

/-- Descend a natural transformation along a full essentially surjective functor.
The component formula uses the functor's recorded object preimages and their isomorphisms.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-descent). -/
def descend (η : P ⋙ F ⟶ P ⋙ G) : F ⟶ G where
  app X := F.map (P.objObjPreimageIso X).inv ≫ η.app (P.objPreimage X) ≫
    G.map (P.objObjPreimageIso X).hom
  naturality X Y f := by
    have h := η.naturality
      (P.preimage ((P.objObjPreimageIso X).hom ≫ f ≫ (P.objObjPreimageIso Y).inv))
    dsimp only [Functor.comp_map] at h
    rw [P.map_preimage] at h
    simp only [Functor.map_comp, Category.assoc] at h
    apply (cancel_epi (F.map (P.objObjPreimageIso X).hom)).mp
    apply (cancel_mono (G.map (P.objObjPreimageIso Y).inv)).mp
    simpa [Category.assoc] using h

/-- Descent recovers the original transformation on every representative.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-descent).
Proof: lift the preimage comparison isomorphism by fullness, apply naturality of the
original transformation, and cancel its image under F. -/
theorem whisker_descend (η : P ⋙ F ⟶ P ⋙ G) :
    Functor.whiskerLeft P (descend P η) = η := by
  ext X
  have h := η.naturality (P.preimage (P.objObjPreimageIso (P.obj X)).hom)
  dsimp only [Functor.comp_map] at h
  rw [P.map_preimage] at h
  change F.map (P.objObjPreimageIso (P.obj X)).inv ≫
    η.app (P.objPreimage (P.obj X)) ≫ G.map (P.objObjPreimageIso (P.obj X)).hom = η.app X
  rw [← h]
  simp

omit [P.Full] in
/-- Equality of natural transformations can be checked on these representatives.
Source: Stacks 070I (blueprint: lem-sf-derived-mapping-descent).
Proof: naturality at each recorded comparison isomorphism transports the assumed
component equality from its chosen representative to the object itself. -/
theorem whisker_injective (η θ : F ⟶ G)
    (h : Functor.whiskerLeft P η = Functor.whiskerLeft P θ) : η = θ := by
  ext X
  have hX := congrArg (fun α ↦ α.app (P.objPreimage X)) h
  have hη := η.naturality (P.objObjPreimageIso X).hom
  have hθ := θ.naturality (P.objObjPreimageIso X).hom
  apply (cancel_epi (F.map (P.objObjPreimageIso X).hom)).mp
  rw [hη, hθ]
  exact congrArg (fun f ↦ f ≫ G.map (P.objObjPreimageIso X).hom) hX

end CategoryTheory.DerivedMappingDescent
