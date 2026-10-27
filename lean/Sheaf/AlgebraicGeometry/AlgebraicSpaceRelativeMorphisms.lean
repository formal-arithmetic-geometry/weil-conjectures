module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.TraceFormula.SpaceLinePresentationDefs

/-! # Relative morphisms of algebraic spaces on scheme tests

Source: Stacks Project, quot.tex, Section 99.12, paragraph before Tag 0D1A
(blueprint: def-sfb-space-relative-morphism-values).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure map of a scheme test, bundled as an algebraic-space map.
Source: Stacks, paragraph before Tag 0D1A
(blueprint: def-sfb-space-relative-morphism-values). -/
def schemeTestMap {S : Scheme.{u}} {B : AlgebraicSpace S} (T : SchemeTests B.obj.obj) :
    schemeSpace T.left ⟶ B :=
  ObjectProperty.homMk ⟨T.hom⟩

/-- The actual sheaf fibre product T ×_B Z.
Source: Stacks, paragraph before Tag 0D1A
(blueprint: def-sfb-space-relative-morphism-values). -/
def relativeSpace {S : Scheme.{u}} {Z B : AlgebraicSpace S} (z : Z ⟶ B)
    (T : SchemeTests B.obj.obj) : AlgebraicSpace S :=
  enlargedFibreProduct (schemeTestMap T) z

/-- The projection Z_T → T.
Source: Stacks, paragraph before Tag 0D1A
(blueprint: def-sfb-space-relative-morphism-values). -/
def relativeSpaceProjection {S : Scheme.{u}} {Z B : AlgebraicSpace S} (z : Z ⟶ B)
    (T : SchemeTests B.obj.obj) : relativeSpace z T ⟶ schemeSpace T.left :=
  enlargedFibreProductFst (schemeTestMap T) z

/-- Canonical base change of the relative source along a scheme test map.
Source: Stacks, paragraph before Tag 0D1A
(blueprint: def-sfb-space-relative-morphism-values). -/
def relativeSpaceMap {S : Scheme.{u}} {Z B : AlgebraicSpace S} (z : Z ⟶ B)
    {T' T : SchemeTests B.obj.obj} (h : T' ⟶ T) : relativeSpace z T' ⟶ relativeSpace z T :=
  ObjectProperty.homMk
    (pullback.map (schemeTestMap T').hom z.hom (schemeTestMap T).hom z.hom
      ⟨yoneda.map h.left⟩ (𝟙 Z.obj) (𝟙 B.obj)
      (by
        apply Sheaf.hom_ext
        change T'.hom = yoneda.map h.left ≫ T.hom
        exact (CostructuredArrow.w h).symm) (by simp))

/-- Relative morphisms, encoded by Z_T → W over B, equivalently Z_T → W_T over T.
The transition maps are precomposition with relativeSpaceMap.
Source: Stacks, paragraph before Tag 0D1A
(blueprint: def-sfb-space-relative-morphism-values). -/
abbrev RelativeMorphism {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    (z : Z ⟶ B) (w : W ⟶ B) (T : SchemeTests B.obj.obj) :=
  {f : relativeSpace z T ⟶ W //
    f ≫ w = relativeSpaceProjection z T ≫ schemeTestMap T}

/-- The structural map Z ×_B W → B.
Source: Stacks, Tag 0D1A (blueprint: def-sfb-space-relative-morphism-values). -/
def relativeProductMap {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    (z : Z ⟶ B) (w : W ⟶ B) : enlargedFibreProduct z w ⟶ B :=
  enlargedFibreProductFst z w ≫ z

/-- First projection (Z ×_B W)_T → Z_T.
Source: Stacks, Tags 0D1A--0D1B (blueprint: def-sfb-space-relative-morphism-values). -/
def relativeFirstProjection {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    (z : Z ⟶ B) (w : W ⟶ B) (T : SchemeTests B.obj.obj) :
    relativeSpace (relativeProductMap z w) T ⟶ relativeSpace z T :=
  ObjectProperty.homMk (pullback.lift
    (pullback.fst (schemeTestMap T).hom (relativeProductMap z w).hom)
    (pullback.snd (schemeTestMap T).hom (relativeProductMap z w).hom ≫
      pullback.fst z.hom w.hom)
    (by simpa [relativeProductMap, enlargedFibreProductFst] using
      (pullback.condition (f := (schemeTestMap T).hom)
        (g := (relativeProductMap z w).hom))))

/-- Second projection to W, determining the projection to W_T together with T.
Source: Stacks, Tags 0D1A--0D1B (blueprint: def-sfb-space-relative-morphism-values). -/
def relativeSecondProjection {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    (z : Z ⟶ B) (w : W ⟶ B) (T : SchemeTests B.obj.obj) :
    relativeSpace (relativeProductMap z w) T ⟶ W :=
  ObjectProperty.homMk (pullback.snd (schemeTestMap T).hom
    (relativeProductMap z w).hom ≫ pullback.snd z.hom w.hom)

/-- The actual graph map, with first coordinate the identity and second coordinate f.
Source: Stacks, Tag 0D1A (blueprint: def-sfb-space-relative-morphism-values). -/
def relativeSpaceGraph {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    (z : Z ⟶ B) (w : W ⟶ B) (T : SchemeTests B.obj.obj) (f : RelativeMorphism z w T) :
    relativeSpace z T ⟶ relativeSpace (relativeProductMap z w) T :=
  ObjectProperty.homMk (pullback.lift
    (pullback.fst (schemeTestMap T).hom z.hom)
    (pullback.lift (pullback.snd (schemeTestMap T).hom z.hom) f.val.hom
      (by
        have hf := congrArg (fun k : relativeSpace z T ⟶ B ↦ k.hom) f.property
        simpa [relativeSpaceProjection, enlargedFibreProductFst] using
          (pullback.condition (f := (schemeTestMap T).hom) (g := z.hom)).symm.trans
            hf.symm))
    (by
      change _ = _ ≫ (pullback.fst z.hom w.hom ≫ z.hom)
      rw [pullback.lift_fst_assoc]
      exact pullback.condition))

end AlgebraicGeometry.AlgebraicSpace
