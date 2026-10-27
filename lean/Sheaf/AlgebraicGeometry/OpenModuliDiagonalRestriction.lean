/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
import Sheaf.AlgebraicGeometry.OpenModuliSubstackAlgebraicity

/-! # Restricting an unramified diagonal to a full substack

Source: Stacks Project, stacks-morphisms.tex, Tag 06N3, restriction to open substacks
(blueprint: lem-sfb-open-moduli-diagonal-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v w
open AlgebraicGeometry CategoryTheory.Limits
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- A full substack of an open with unramified diagonal has unramified diagonal.
The two scheme tests and both projections are unchanged under the full inclusion.
Source: Stacks Project, stacks-morphisms.tex, Tag 06N3, restriction to open substacks
(blueprint: lem-sfb-open-moduli-diagonal-restriction).
Proof: for two scheme-valued functors to U, compose with the full inclusion into V.
Full faithfulness identifies the two iso-comma categories over the base, by lifting
comparison isomorphisms and their commuting squares. Compose the representing
space equivalence for V with this identification. Its map to the product of the two
test schemes and its two projection comparisons are unchanged. -/
theorem OpenModuliSubstack.hasUnramifiedDiagonal_of_contained {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (U V : OpenModuliSubstack F)
    (h : U.IsContainedIn V) (hV : HasUnramifiedModuliDiagonal V.category) :
    HasUnramifiedModuliDiagonal U.category := by
  let i : BasedFunctor U.category V.category :=
    { toFunctor := ObjectProperty.ιOfLE h, w := rfl }
  intro T R a b
  obtain ⟨Z, p, hp, e, he, hf, hs⟩ := hV T R (a.comp i) (b.comp i)
  let q : BasedFunctor (moduliTwoFiberProduct (a.comp i) (b.comp i))
      (moduliTwoFiberProduct a b) :=
    { toFunctor :=
        { obj := fun x ↦
            ⟨{ left := x.obj.left
               right := x.obj.right
               hom := ObjectProperty.homMk x.obj.hom.hom }, by
              exact ⟨(ObjectProperty.isIso_hom_iff (P := U.property) _).mp
                ((ObjectProperty.isIso_hom_iff (P := V.property) x.obj.hom).mpr
                  x.property.1),
                (fullModuli_isHomLift (P := U.property) _ _).mpr
                  ((fullModuli_isHomLift (P := V.property) _ _).mp x.property.2)⟩⟩
          map := fun f ↦ ObjectProperty.homMk
            { left := f.hom.left
              right := f.hom.right
              w := by
                apply (ObjectProperty.ι U.property).map_injective
                exact congrArg (fun t ↦ t.hom) f.hom.w }
          map_id := by intro x; rfl
          map_comp := by intro x y z f g; rfl }
      w := rfl }
  have hq : q.toFunctor.IsEquivalence := by
    have : q.toFunctor.Faithful :=
      ⟨by
        intro x y f g hfg
        apply ObjectProperty.hom_ext
        apply Comma.hom_ext
        · exact congrArg (fun t ↦ t.hom.left) hfg
        · exact congrArg (fun t ↦ t.hom.right) hfg⟩
    have : q.toFunctor.Full :=
      ⟨fun f ↦ ⟨ObjectProperty.homMk
        { left := f.hom.left
          right := f.hom.right
          w := by
            apply (ObjectProperty.ι V.property).map_injective
            exact congrArg (fun t ↦ t.hom) f.hom.w }, rfl⟩⟩
    have : q.toFunctor.EssSurj :=
      ⟨fun x ↦ by
        let y : (moduliTwoFiberProduct (a.comp i) (b.comp i)).obj :=
          ⟨{ left := x.obj.left
             right := x.obj.right
             hom := ObjectProperty.homMk x.obj.hom.hom }, by
            exact ⟨(ObjectProperty.isIso_hom_iff (P := V.property) _).mp
              ((ObjectProperty.isIso_hom_iff (P := U.property) x.obj.hom).mpr
                x.property.1),
              (fullModuli_isHomLift (P := V.property) _ _).mpr
                ((fullModuli_isHomLift (P := U.property) _ _).mp x.property.2)⟩⟩
        exact ⟨y, ⟨Iso.refl _⟩⟩⟩
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have : e.toFunctor.IsEquivalence := he
  have : q.toFunctor.IsEquivalence := hq
  refine ⟨Z, p, hp, e.comp q,
    (show (e.toFunctor ⋙ q.toFunctor).IsEquivalence from inferInstance), ?_, ?_⟩
  · exact hf
  · exact hs

end CategoryTheory
