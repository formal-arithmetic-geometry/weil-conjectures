/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenUnit
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso

/-! # Naturality in the coefficient of derived base change

Source: Stacks Project, Tags 08HY, 08BV and 0DJ9.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Naturality of the canonical derived base-change map in its coefficient object.
Source: Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-pc-derived-base-change-coefficient-naturality).
Proof: The map is the mate of the natural pullback-composition comparison followed
by the pulled-back counit. Naturality of the adjunction Hom equivalence moves a
coefficient map to the two ends of the transpose. Naturality of the comparison
moves it into the pulled-back counit, and naturality of the counit equates the
resulting transposes. -/
theorem schemeDerivedBaseChangeMap_naturality
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) {K L : schemeDerivedCategory X} (k : K ⟶ L) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map k ≫
        schemeDerivedBaseChangeMap f f' g g' h L =
      schemeDerivedBaseChangeMap f f' g g' h K ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map k) := by
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) a b
  let e := c f' g ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) h.symm) ≪≫ (c g' f).symm
  have hn := mate_naturality (canonicalPullbackAdjunction f)
    (canonicalPullbackAdjunction f') (derivedPullback g) (derivedPullback g') e k
  change (derivedPullback g).map ((schemeDerivedDirectImage f).map k) ≫
      (canonicalPullbackAdjunction f').homEquiv _ _
        ((c f' g).hom.app ((schemeDerivedDirectImage f).obj L) ≫
          eqToHom (congrArg (fun t ↦
            (derivedPullback t).obj ((schemeDerivedDirectImage f).obj L)) h.symm) ≫
          (c g' f).inv.app ((schemeDerivedDirectImage f).obj L) ≫
          (derivedPullback g').map ((canonicalPullbackAdjunction f).counit.app L)) =
      (canonicalPullbackAdjunction f').homEquiv _ _
        ((c f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
          eqToHom (congrArg (fun t ↦
            (derivedPullback t).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
          (c g' f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((canonicalPullbackAdjunction f).counit.app K)) ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map k)
  simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToHom_app, Functor.comp_obj, Functor.comp_map, Functor.id_obj, Category.assoc] using hn


end AlgebraicGeometry

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The unbounded derived base-change map is natural in a complex of étale module sheaves.
Source: blueprint, sec-smooth-base-change, sk-def-bc, node sbc-lem-bc-naturality
(blueprint: sbc-lem-bc-naturality).

Proof: expand sbc-def-base-change-map into four arrows `a`, `b`, `c`, `d`: the unit of
`Le* ⊣ Re*` whiskered by `Lf* Rg*`, the two canonical composite-functor identifications,
and the counit of `Lf* ⊣ Rf*`. Write their source and target functors as `F₀`, ..., `F₄`.
Unit naturality and functoriality give `F₀(u) ≫ a(K') = a(K) ≫ F₁(u)`.
Naturality of the two canonical identifications gives
`F₁(u) ≫ b(K') = b(K) ≫ F₂(u)` and `F₂(u) ≫ c(K') = c(K) ≫ F₃(u)`.
Counit naturality gives `F₃(u) ≫ d(K') = d(K) ≫ F₄(u)`.
Substitute these equations successively, using associativity, to move `u` through the
four arrows. Their composite is the recorded `derivedBaseChangeMap` on the exchanged
square `sq.toCommSq.flip`, so the result is precisely the displayed equality.
Equivalently apply the naturality axiom of that natural transformation; no geometric
base-change isomorphism theorem is needed. -/
theorem derivedBaseChangeMap_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    {K K' : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : K ⟶ K') :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map
        ((R((g)_*[ModuleCat.{u + 1} Λ])).map v) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app K' =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app K ≫
        (R((h)_*[ModuleCat.{u + 1} Λ])).map
          ((L((e)^*[ModuleCat.{u + 1} Λ])).map v) := by
  sorry

end AlgebraicGeometry.Etale
