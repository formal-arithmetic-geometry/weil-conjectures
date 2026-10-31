/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The Hilbert functor of proper families

Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B, and the definition of Hilb
(blueprint: def-sfb-proper-hilbert-presheaf).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Proper, flat, finitely presented closed families in the Hilbert functor.
Properness supplies quasi-compactness and quasi-separatedness, so local finite presentation
here is equivalent to finite presentation. Source: Stacks Project, quot.tex, Tag 0D1A
(blueprint: def-sfb-proper-hilbert-presheaf). -/
def IsProperHilbertFamily {W S : Scheme.{u}} (w : W ⟶ S) (T : Over S)
    (I : (pullback w T.hom).IdealSheafData) : Prop :=
  IsProper (I.subschemeι ≫ pullback.snd w T.hom) ∧
    Flat (I.subschemeι ≫ pullback.snd w T.hom) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd w T.hom)

/-- The full Hilbert presheaf: closed subschemes proper, flat and finitely presented over
the test scheme, pulled back by inverse image of their ideal sheaves. The proof fields
are the existing base-change stability of these three morphism properties and the
identity/composition laws of ideal pullback. Source: Stacks Project, quot.tex, Tag 0D1A
(blueprint: def-sfb-proper-hilbert-presheaf). -/
noncomputable def properHilbertPresheaf {W S : Scheme.{u}} (w : W ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := { I : (pullback w T.unop.hom).IdealSheafData // IsProperHilbertFamily w T.unop I }
  map φ := TypeCat.ofHom fun I ↦ ⟨I.1.comap (baseChangeMap w φ.unop), by
    have hsq : IsPullback
        ((I.1.comapIso (baseChangeMap w φ.unop)).hom ≫ pullback.snd _ _)
        ((I.1.comap (baseChangeMap w φ.unop)).subschemeι ≫ pullback.snd w _)
        (I.1.subschemeι ≫ pullback.snd w _) φ.unop.left :=
      ((IsPullback.of_hasPullback (baseChangeMap w φ.unop) I.1.subschemeι).flip.paste_vert
        (isPullback_baseChangeMap w φ.unop)).of_iso'
          (I.1.comapIso _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp) (by simp) (by simp)
    exact ⟨MorphismProperty.of_isPullback hsq I.2.1,
      MorphismProperty.of_isPullback hsq I.2.2.1,
      MorphismProperty.of_isPullback hsq I.2.2.2⟩⟩
  map_id T := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp [baseChangeMap_id, Scheme.IdealSheafData.comap_id]))
  map_comp φ ψ := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp only [unop_comp, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp]
    rfl))

end AlgebraicGeometry
