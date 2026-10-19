module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Canonical enlargement of the universe of a fixed scheme

Source: Stacks Project, Schemes, gluing of schemes (Tag 01JA); the affine-colimit description
of a scheme, used for geometric fibres in the proof of Temkin, Stable modification,
Theorem 1.1 (blueprint: def-trf-scheme-universe-enlargement).
-/

@[expose] public section

set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Lift a coordinate ring, together with its ring homomorphisms, by `ULift`.
Source: the ring-equivalent coordinate rings in Stacks Tag 01JA
(blueprint: def-trf-scheme-universe-enlargement). -/
def schemeCoordinateRingLift : CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj R := .of (ULift.{v} R)
  map f := CommRingCat.ofHom f.hom.ulift
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The affine presentation of a fixed scheme with its coordinate rings enlarged.
Source: affine-colimit description of a scheme and Stacks Tag 01JA
(blueprint: def-trf-scheme-universe-enlargement). -/
noncomputable def schemeUniverseDiagram (X : Scheme.{u}) :
    CostructuredArrow Scheme.Spec X ⥤ Scheme.{max u v} :=
  CostructuredArrow.proj Scheme.Spec X ⋙ schemeCoordinateRingLift.{u, v}.op ⋙ Scheme.Spec

/-- The lifted affine presentation has a colimit in schemes.
Source: Stacks Tag 01JA, gluing schemes along open subschemes
(blueprint: def-trf-scheme-universe-enlargement).

Proof: cover `X` by its affine opens. Replace each coordinate ring `A` by `ULift A`,
transport every localization and restriction homomorphism by `ULift.ringEquiv`, and glue the
resulting affine schemes along the lifted open intersections. The cocycle identities are
transported ring identities, so the gluing theorem applies. A cocone on all affine schemes
mapping to `X` restricts to these affine-open charts. Its restrictions agree on intersections:
cover each intersection by affine opens and use the cocone identities there. Hence it glues
to a unique morphism from the glued scheme. Conversely, any affine map into `X` is covered
by the inverse images of the affine-open charts; checking on affine refinements shows that
the glued morphism recovers its given cocone leg. This proves the colimit universal property.
-/
theorem schemeUniverseDiagram_hasColimit (X : Scheme.{u}) :
    HasColimit (schemeUniverseDiagram.{u, v} X) := by
  sorry

/-- The canonical universe enlargement, determined up to its unique colimit isomorphism.
Only the proof of existence of this universal object is postponed; its data is Mathlib's
chosen colimit of the explicit affine diagram. Source: Stacks Tag 01JA
(blueprint: def-trf-scheme-universe-enlargement). -/
noncomputable def schemeUniverseLift (X : Scheme.{u}) : Scheme.{max u v} :=
  haveI := schemeUniverseDiagram_hasColimit.{u, v} X
  colimit (schemeUniverseDiagram.{u, v} X)

/-- The canonical enlarged morphism is induced by postcomposition of affine maps.
Source: the gluing universal property, Stacks Tag 01JA
(blueprint: def-trf-scheme-universe-enlargement). -/
noncomputable def schemeUniverseLiftMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeUniverseLift.{u, v} X ⟶ schemeUniverseLift.{u, v} Y :=
  haveI := schemeUniverseDiagram_hasColimit.{u, v} X
  haveI := schemeUniverseDiagram_hasColimit.{u, v} Y
  colimit.desc (schemeUniverseDiagram.{u, v} X)
    ((colimit.cocone (schemeUniverseDiagram.{u, v} Y)).whisker (CostructuredArrow.map f))

/-- Universe enlargement respects composition.
Source: uniqueness in the gluing universal property, Stacks Tag 01JA
(blueprint: def-trf-scheme-universe-enlargement).

Proof: precompose both maps with every affine leg of the source colimit. By the defining
cocone equations both composites are the leg indexed by the affine map followed by `f ≫ g`.
The uniqueness clause of the source colimit identifies the two morphisms.
-/
theorem schemeUniverseLiftMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeUniverseLiftMap.{u, v} (f ≫ g) =
      schemeUniverseLiftMap.{u, v} f ≫ schemeUniverseLiftMap.{u, v} g := by
  let := schemeUniverseDiagram_hasColimit.{u, v} X
  let := schemeUniverseDiagram_hasColimit.{u, v} Y
  let := schemeUniverseDiagram_hasColimit.{u, v} Z
  apply colimit.hom_ext
  intro j
  simp only [schemeUniverseLiftMap, colimit.ι_desc,
    colimit.ι_desc_assoc, Cocone.whisker_ι, Functor.whiskerLeft_app]
  change colimit.ι (schemeUniverseDiagram Z) ((CostructuredArrow.map (f ≫ g)).obj j) =
    colimit.ι (schemeUniverseDiagram Y) ((CostructuredArrow.map f).obj j) ≫ _
  rw [colimit.ι_desc]
  dsimp only [Cocone.whisker_ι, Functor.whiskerLeft_app]
  let e : (CostructuredArrow.map (f ≫ g)).obj j ⟶
      (CostructuredArrow.map g).obj ((CostructuredArrow.map f).obj j) :=
    CostructuredArrow.homMk (𝟙 j.left) (by simp [Category.assoc])
  have he : (schemeUniverseDiagram.{u, v} Z).map e = 𝟙 _ := by
    change Scheme.Spec.map (schemeCoordinateRingLift.{u, v}.map (𝟙 _)).op = _
    simp
    rfl
  have h := colimit.w (schemeUniverseDiagram.{u, v} Z) e
  rw [he, Category.id_comp] at h
  exact h.symm

end AlgebraicGeometry
