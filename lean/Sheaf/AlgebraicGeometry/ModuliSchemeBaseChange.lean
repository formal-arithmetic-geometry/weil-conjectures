/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Scheme base change of a moduli groupoid

Source: Stacks Project, Tag 003R (iso-comma construction), and Tag 04WV
(localization of stacks) (blueprint: def-sfb-moduli-scheme-base-change).

The category is constructed from triples, retaining the isomorphism of bases and all
arrows. The base-changed scheme map is explicit, using the scheme pullback projection.
No algebraicity or descent assertion is built into these definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction along `Sch/S' → Sch/S`, realized as the iso-comma category of the
projection and composition with the base morphism. Its projection remembers the
`S'`-scheme. Source: Stacks Project, Tag 003R, with Tag 04WV
(blueprint: def-sfb-moduli-scheme-base-change). -/
def moduliSchemeBaseChange {S S' : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (g : S' ⟶ S) : BasedCategory (Over S') :=
  BasedCategory.ofFunctor
    (ObjectProperty.ι (fun x : Comma F.p (Over.map g) ↦ IsIso x.hom) ⋙
      Comma.snd F.p (Over.map g))

/-- On total categories of representable groupoids, send a map `V → U ×_S S'`
to `V → U`, remembering `V` as an `S`-scheme. The counit is the first scheme
pullback projection. Source: Stacks Project, Tag 003R
(blueprint: def-sfb-moduli-scheme-base-change). -/
def schemeModuliBaseChangeForget {S S' : Scheme.{u}} (U : Over S) (g : S' ⟶ S) :
    (discreteModuli (yoneda.obj ((Over.pullback g).obj U))).obj ⥤
      (discreteModuli (yoneda.obj U)).obj where
  obj x := CostructuredArrow.mk (Y := (Over.map g).obj x.left) (yoneda.map
    ((Over.map g).map (yoneda.preimage x.hom) ≫ (Over.mapPullbackAdj g).counit.app U))
  map {x y} b :=
    { left := (Over.map g).map b.left
      right := 𝟙 _
      w := by
        dsimp
        rw [Category.comp_id, ← yoneda.map_comp, ← Category.assoc,
          ← (Over.map g).map_comp]
        congr 2
        have h : b.left ≫ yoneda.preimage y.hom = yoneda.preimage x.hom := by
          apply yoneda.map_injective
          simpa only [yoneda.map_comp, yoneda.map_preimage] using CostructuredArrow.w b
        exact congrArg ((Over.map g).map) h }
  map_id x := by
    apply CostructuredArrow.hom_ext
    exact (Over.map g).map_id x.left
  map_comp b c := by
    apply CostructuredArrow.hom_ext
    exact (Over.map g).map_comp b.left c.left

/-- Base change of a specified scheme map into a moduli groupoid. On an object
`V → U ×_S S'`, take its composite into `F`, its base `V/S'`, and the canonical
identity isomorphism between their underlying `S`-schemes.
Source: Stacks Project, Tag 003R and Tag 075W
(blueprint: def-sfb-moduli-scheme-base-change). -/
def moduliSchemeBaseChangeAtlas {S S' : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {U : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) (g : S' ⟶ S) :
    BasedFunctor (discreteModuli (yoneda.obj ((Over.pullback g).obj U)))
      (moduliSchemeBaseChange F g) where
  obj x := ⟨⟨a.obj ((schemeModuliBaseChangeForget U g).obj x), x.left,
    eqToHom ((a.w_obj ((schemeModuliBaseChangeForget U g).obj x)).trans (by rfl))⟩, inferInstance⟩
  map {x y} b := ObjectProperty.homMk
    { left := a.map ((schemeModuliBaseChangeForget U g).map b)
      right := b.left
      w := by
        have h := Functor.congr_hom a.w ((schemeModuliBaseChangeForget U g).map b)
        simpa [Category.assoc, schemeModuliBaseChangeForget, discreteModuli,
          BasedCategory.ofFunctor, CostructuredArrow.proj, CostructuredArrow.mk] using
          congrArg (fun k ↦ k ≫ eqToHom
            (a.w_obj ((schemeModuliBaseChangeForget U g).obj y))) h }
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · change a.map ((schemeModuliBaseChangeForget U g).map (𝟙 x)) = 𝟙 _
      rw [Functor.map_id, Functor.map_id]
    · rfl
  map_comp b c := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · change a.map ((schemeModuliBaseChangeForget U g).map (b ≫ c)) =
        a.map ((schemeModuliBaseChangeForget U g).map b) ≫
          a.map ((schemeModuliBaseChangeForget U g).map c)
      rw [Functor.map_comp, Functor.map_comp]
    · rfl
  w := rfl

end CategoryTheory
