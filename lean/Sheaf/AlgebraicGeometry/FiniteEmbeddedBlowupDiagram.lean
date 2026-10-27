/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import WeilConjectures.Blowup.FlatBaseChange
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Compactification.FiniteTypeExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Finite ambient blowup and strict-transform diagrams

Source: Stacks Project, Divisors, Tags 080E and 0805, iterated finite diagrams
(blueprint: def-per-finite-embedded-blowup-diagram).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An uncontracted finite diagram of ordinary ambient blowups and closed strict transforms.
All transition morphisms and all center ideals are retained, including identity stages.
Neither reducedness nor regularity of the schemes or centers is part of this definition.
Source: Stacks Project, Divisors, Tag 080E, iterated
(blueprint: def-per-finite-embedded-blowup-diagram). -/
structure FiniteEmbeddedBlowupDiagram (n : ℕ) where
  ambient : (Fin (n + 1))ᵒᵖ ⥤ Scheme.{u}
  intrinsic : (Fin (n + 1))ᵒᵖ ⥤ Scheme.{u}
  inclusion : intrinsic ⟶ ambient
  closed : ∀ k, IsClosedImmersion (inclusion.app (op k))
  center : ∀ j : Fin n, (ambient.obj (op j.castSucc)).IdealSheafData
  finiteType : ∀ j, (center j).ofFiniteType
  ambientIso : ∀ j, ambient.obj (op j.succ) ≅ (center j).blowup
  ambient_fac : ∀ j, (ambientIso j).hom ≫ (center j).blowupMap =
    ambient.map (homOfLE (le_of_lt j.castSucc_lt_succ)).op
  intrinsicIso : ∀ j, intrinsic.obj (op j.succ) ≅
    (center j).strictTransform (inclusion.app (op j.castSucc))
  intrinsic_fac : ∀ j, (intrinsicIso j).hom ≫ AlgebraicGeometry.strictTransformToSource
      (inclusion.app (op j.castSucc)) (center j).blowupMap (center j).support.compl =
    intrinsic.map (homOfLE (le_of_lt j.castSucc_lt_succ)).op
  inclusion_fac : ∀ j, (intrinsicIso j).hom ≫ AlgebraicGeometry.strictTransformMap
      (inclusion.app (op j.castSucc)) (center j).blowupMap (center j).support.compl =
    inclusion.app (op j.succ) ≫ (ambientIso j).hom

/-- A smooth pullback comparison of finite embedded diagrams. The ambient stage map is
explicitly the published canonical flat-base-change comparison, transported by the chosen
stage isomorphisms. Cartesian squares for the closed subschemes retain their scheme
structures. Naturality keeps every earlier ideal, without deleting any identity stage.
Source: Stacks Project, Divisors, Tags 0805 and 080E, and Morphisms, Tag 081I
(blueprint: def-per-finite-embedded-blowup-diagram). -/
structure FiniteEmbeddedBlowupDiagram.Comparison {n : ℕ}
    (E D : FiniteEmbeddedBlowupDiagram.{u} n) where
  ambient : E.ambient ⟶ D.ambient
  intrinsic : E.intrinsic ⟶ D.intrinsic
  square : E.inclusion ≫ ambient = intrinsic ≫ D.inclusion
  smooth : ∀ k, Smooth (ambient.app (op k))
  flat : ∀ k, Flat (ambient.app (op k))
  cartesian : ∀ k, IsPullback (intrinsic.app (op k)) (E.inclusion.app (op k))
    (D.inclusion.app (op k)) (ambient.app (op k))
  center_eq : ∀ j, E.center j = (D.center j).comap (ambient.app (op j.castSucc))
  ambient_cartesian : ∀ j : Fin n,
    IsPullback (ambient.app (op j.succ))
      (E.ambient.map (homOfLE (le_of_lt j.castSucc_lt_succ)).op)
      (D.ambient.map (homOfLE (le_of_lt j.castSucc_lt_succ)).op)
      (ambient.app (op j.castSucc))
  canonical : ∀ j,
    (E.ambientIso j).hom ≫ eqToHom (congrArg Scheme.IdealSheafData.blowup (center_eq j)) ≫
      @Scheme.IdealSheafData.blowupFlatBaseChange _ _ (D.center j)
        (ambient.app (op j.castSucc)) (flat j.castSucc) ≫
      pullback.fst (D.center j).blowupMap (ambient.app (op j.castSucc)) =
    ambient.app (op j.succ) ≫ (D.ambientIso j).hom

end AlgebraicGeometry
