/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCoverSheafDescent
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.FppfSpaceDatumSheafRealization
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Effective descent of étale spaces along one étale cover

Source: Stacks Project, Bootstrap, Tag 0ADV(1), singleton covering; Spaces Descent,
Tags 0ADT and 042B (blueprint: lem-sfb-etale-space-single-cover-effective-descent).

The existing transport description of descent data gives exactly the overlap isomorphism,
its diagonal identity and its triple-overlap cocycle. Étaleness means the chart test,
without an additional scheme-representability requirement on the morphism of spaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A space over `M`, viewed in the existing category of locally algebraic sheaves for
the singleton cover. Its local algebraicity is the sheaf fibre-product theorem.
Source: Stacks, Spaces Descent, Tag 0ADT, canonical restriction functor
(blueprint: lem-sfb-etale-space-single-cover-effective-descent). -/
def singleCoverSheafObject {S : Scheme.{u}} {M U N : AlgebraicSpace S}
    (a : U ⟶ M) (f : N ⟶ M) :
    (IsLocallyAlgebraicSpaceSheaf (fun _ : Unit ↦ a)).FullSubcategory :=
  ⟨Over.mk f.hom, fun _ ↦ (fibreProduct_isAlgebraicSpace N U M f a).1⟩

/-- Étale descent data for one surjective étale map have an algebraic-space realization,
étale over the base, with precisely the prescribed overlap identification.
Source: Stacks, Bootstrap, Tag 0ADV(1); Spaces Descent, Tags 0ADT and 042B
(blueprint: lem-sfb-etale-space-single-cover-effective-descent).

Proof: (1) The chartwise calculus makes the étale cover flat and locally of finite
presentation. Together with the given point surjectivity this is a singleton fppf cover.
(2) Apply lem-sfb-fppf-space-datum-sheaf-realization to obtain a sheaf `F → M` and an
isomorphism of its restriction with the given datum. This retains the overlap transport.
(3) Let `q : V → F` be the local projection. For every scheme `T → F`, its base change
is `T ×_M U`: the inverse maps keep the `T` coordinate and use the displayed local
identification to exchange the `V` and `U` coordinates. Fibre-product closure and
chartwise base change show this is a surjective étale algebraic space over `T`, hence
flat and locally of finite presentation. Apply lem-sfb-fppf-space-atlas-bootstrap
to conclude that `F` is algebraic, and call it `N`.
(4) The map `N → M` pulls back to the given étale local map. The étale clause of
lem-sfb-representable-fppf-etale-open-descent (Tag 042B) descends this chartwise
property. The same datum isomorphism still induces the specified overlap map.
No quasi-compactness, finite type, or separatedness is used. -/
theorem etaleSpaceSingleCover_effective {S : Scheme.{u}} {M U : AlgebraicSpace S}
    (a : U ⟶ M) (ha : MapIsLocally (@Etale) a)
    (hsurj : IsJointlySurjective (fun _ : Unit ↦ a.hom.hom))
    (D : SpaceCoverSheafDescent (fun _ : Unit ↦ a))
    (hv : MapIsLocally (@Etale)
      (ObjectProperty.homMk (D.localObject ()).hom :
        (⟨(D.localObject ()).left, D.local_algebraic ()⟩ : AlgebraicSpace S) ⟶ U)) :
    ∃ (N : AlgebraicSpace S) (f : N ⟶ M), MapIsLocally (@Etale) f ∧
      Nonempty (D ≅ (spaceCoverSheafRestriction (fun _ : Unit ↦ a)).obj
        (singleCoverSheafObject a f)) := by
  sorry

/-- Pullback along the cover is bijective on morphisms between étale spaces over `M`;
the target consists of exactly the local maps respecting the canonical overlap maps.
Source: Stacks, Spaces Descent, Tag 0ADT, full faithfulness
(blueprint: lem-sfb-etale-space-single-cover-effective-descent).

Proof: (5) Fibre-product closure puts both global spaces in the locally algebraic sheaf
category. As in step (1), the singleton cover is fppf. Full faithfulness in
lem-sfb-fppf-space-datum-sheaf-realization gives this bijection. Maps of algebraic
spaces are sheaf maps by def-trf-algebraic-space, and morphisms in the existing descent
category are exactly maps over `U` commuting with every overlap transport. -/
theorem etaleSpaceSingleCover_bijective {S : Scheme.{u}} {M U N₁ N₂ : AlgebraicSpace S}
    (a : U ⟶ M) (ha : MapIsLocally (@Etale) a)
    (hsurj : IsJointlySurjective (fun _ : Unit ↦ a.hom.hom))
    (f₁ : N₁ ⟶ M) (f₂ : N₂ ⟶ M)
    (hf₁ : MapIsLocally (@Etale) f₁) (hf₂ : MapIsLocally (@Etale) f₂) :
    Function.Bijective
      ((spaceCoverSheafRestriction (fun _ : Unit ↦ a)).map :
        (singleCoverSheafObject a f₁ ⟶ singleCoverSheafObject a f₂) →
          ((spaceCoverSheafRestriction (fun _ : Unit ↦ a)).obj
              (singleCoverSheafObject a f₁) ⟶
            (spaceCoverSheafRestriction (fun _ : Unit ↦ a)).obj
              (singleCoverSheafObject a f₂))) := by
  sorry

/-- Two realizations have a unique isomorphism over `M` compatible with their displayed
identifications with the given descent datum.
Source: Stacks, Spaces Descent, Tag 0ADT, equivalence and full faithfulness
(blueprint: lem-sfb-etale-space-single-cover-effective-descent).

Proof: (5) Compose the two displayed datum isomorphisms to obtain inverse compatible
local maps. Descend each using etaleSpaceSingleCover_bijective. Their composites are
identities by injectivity of pullback, so they form an isomorphism. The same injectivity
shows that every compatible isomorphism equals this one. -/
theorem etaleSpaceSingleCover_unique {S : Scheme.{u}} {M U N₁ N₂ : AlgebraicSpace S}
    (a : U ⟶ M) (ha : MapIsLocally (@Etale) a)
    (hsurj : IsJointlySurjective (fun _ : Unit ↦ a.hom.hom))
    (D : SpaceCoverSheafDescent (fun _ : Unit ↦ a))
    (f₁ : N₁ ⟶ M) (f₂ : N₂ ⟶ M)
    (hf₁ : MapIsLocally (@Etale) f₁) (hf₂ : MapIsLocally (@Etale) f₂)
    (e₁ : D ≅ (spaceCoverSheafRestriction (fun _ : Unit ↦ a)).obj
      (singleCoverSheafObject a f₁))
    (e₂ : D ≅ (spaceCoverSheafRestriction (fun _ : Unit ↦ a)).obj
      (singleCoverSheafObject a f₂)) :
    ∃! e : singleCoverSheafObject a f₁ ≅ singleCoverSheafObject a f₂,
      (spaceCoverSheafRestriction (fun _ : Unit ↦ a)).mapIso e = e₁.symm ≪≫ e₂ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
