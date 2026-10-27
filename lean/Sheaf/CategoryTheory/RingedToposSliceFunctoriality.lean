/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.CategoryTheory.LocallyRingedTopos
public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-!
# Functorial ringed relocalization at a sheaf map

Source: Stacks Project, sites-modules.tex, Tags 04J8 and 04IH; sites.tex, Tag 04IV;
spaces-properties.tex, Tag 04M6 (blueprint: lem-sfb-ringed-topos-slice-functoriality).

The comparison maps are given in the actual sheaf slices. Their first projections fix
both their maps and their coherence. The element-site models identify these slice
comparisons with comparisons of the displayed ringed geometric morphisms.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The specified inverse image `(H → B) ↦ (L H ×[L B] A → A)`.
Source: Stacks Project, Tag 04IV
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
noncomputable def ringedSliceInverse
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    {A : Sheaf J (Type u)} {B : Sheaf K (Type u)} (s : A ⟶ L.obj B) :
    Over B ⥤ Over A :=
  Over.post L ⋙ Over.pullback s

/-- The first, sheaf-valued coordinate of the inverse image of a slice object.
Source: Stacks Project, Tag 04IV
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
noncomputable def ringedSliceFirst
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    {A : Sheaf J (Type u)} {B : Sheaf K (Type u)} (s : A ⟶ L.obj B)
    (H : Over B) : ((ringedSliceInverse L s).obj H).left ⟶ L.obj H.left :=
  pullback.fst (L.map H.hom) s

/-- The projection comparison in slice coordinates, before applying the structural ring map.
Source: Stacks Project, Tags 04IV and 04J8
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
noncomputable def ringedSliceProjection
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    {A : Sheaf J (Type u)} {B : Sheaf K (Type u)} (s : A ⟶ L.obj B)
    (H : Sheaf K (Type u)) :
    ((ringedSliceInverse L s).obj ((Over.star B).obj H)).left ⟶ L.obj H :=
  ringedSliceFirst L s ((Over.star B).obj H) ≫ L.map prod.snd

/-- A fibre-normalized element-site presentation of a ringed slice.
Source: Stacks Project, Tags 0791 and 04IE
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
structure RingedSlicePresentation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (A : Sheaf J (Type u)) where
  data : RingedSheafSliceAdjunctionData R A
  star : Over.star A ⋙ data.fibreEquivalence.inverse ≅ elementSheafPullback A
  star_formula : ∀ (H : Sheaf J (Type u)) (U : Cᵒᵖ) (a : A.obj.obj U)
    (z : (data.fibreEquivalence.inverse.obj ((Over.star A).obj H)).obj.obj
      (elementObj A U a)),
    ((star.hom.app H).hom.app (elementObj A U a)) z =
      (prod.snd : A ⨯ H ⟶ H).hom.app U
        (((data.fibre_iso.hom.app ((Over.star A).obj H)).app (elementObj A U a)) z).val

/-- Ringed relocalization, with its complete inverse-image and structural-map normalizations.
Source: Stacks Project, Tags 04J8, 04IV and 04IH
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
structure RingedSliceMorphismData
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (g : RingedToposMorphism R S)
    {A : Sheaf J (Type u)} {B : Sheaf K (Type u)} (s : A ⟶ g.inverse.obj B)
    (p : RingedSlicePresentation R A) (q : RingedSlicePresentation S B) where
  morphism : RingedToposMorphism (elementRing R A) (elementRing S B)
  /-- Inverse images on every slice sheaf, naturally in that sheaf. -/
  model : q.data.fibreEquivalence.inverse ⋙ morphism.inverse ⋙
      sheafToPresheaf (elementTopology A) (Type u) ≅
    ringedSliceInverse g.inverse s ⋙ elementFibrePresheafFunctor A
  /-- The canonical comparison with the two localization projections. -/
  projection : elementSheafPullback B ⋙ morphism.inverse ≅
    g.inverse ⋙ elementSheafPullback A
  /-- In slice coordinates the projection comparison retains the first coordinate. -/
  projection_formula : ∀ (H : Sheaf K (Type u)) (U : Cᵒᵖ) (a : A.obj.obj U)
    (z : (morphism.inverse.obj
      (q.data.fibreEquivalence.inverse.obj ((Over.star B).obj H))).obj.obj
        (elementObj A U a)),
    ((morphism.inverse.map (q.star.hom.app H) ≫ projection.hom.app H).hom.app
      (elementObj A U a)) z =
      (ringedSliceProjection g.inverse s H).hom.app U
        (((model.hom.app ((Over.star B).obj H)).app (elementObj A U a)) z).val
  /-- Under that comparison the structural map is the restriction of `g.ringMap`. -/
  ringMap_eq : morphism.ringMap =
    projection.hom.app (ringSheafUnderlying S) ≫
      (elementSheafPullback A).map g.ringMap
  isLocal : IsLocallyRingedTopos R → IsLocallyRingedTopos S →
    g.IsLocal → morphism.IsLocal

/-- A restriction-square comparison in the actual sheaf slices. Both maps preserve the
`A'` coordinate because they are morphisms in `Over A'`; the equation fixes the other one.
Source: Stacks Project, Tags 04IV and 04J8
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
structure RingedSliceRestrictionComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (g : RingedToposMorphism R S)
    {A A' : Sheaf J (Type u)} {B B' : Sheaf K (Type u)}
    (s : A ⟶ g.inverse.obj B) (s' : A' ⟶ g.inverse.obj B')
    (a : A' ⟶ A) (b : B' ⟶ B) where
  iso : ringedSliceInverse g.inverse s ⋙ Over.pullback a ≅
    Over.pullback b ⋙ ringedSliceInverse g.inverse s'
  first : ∀ H : Over B,
    (iso.hom.app H).left ≫
        ringedSliceFirst g.inverse s' ((Over.pullback b).obj H) ≫
          g.inverse.map (pullback.fst H.hom b) =
      pullback.fst ((ringedSliceInverse g.inverse s).obj H).hom a ≫
        ringedSliceFirst g.inverse s H
  /-- On the restricted structure ring both paths use the same structural map. -/
  ring : (iso.hom.app ((Over.star B).obj (ringSheafUnderlying S))).left ≫
      ringedSliceFirst g.inverse s'
        ((Over.pullback b).obj ((Over.star B).obj (ringSheafUnderlying S))) ≫
      g.inverse.map (pullback.fst ((Over.star B).obj (ringSheafUnderlying S)).hom b) ≫
      g.inverse.map prod.snd ≫ g.ringMap =
    pullback.fst
        ((ringedSliceInverse g.inverse s).obj ((Over.star B).obj
          (ringSheafUnderlying S))).hom a ≫
      ringedSliceProjection g.inverse s (ringSheafUnderlying S) ≫ g.ringMap

/-- Pasting two restriction comparisons with the canonical associators and pullback comparisons.
Source: Stacks Project, Tag 04IV
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
noncomputable def ringedSliceRestrictionComposite
    {E F : Type (u + 1)} [Category.{u} E] [Category.{u} F]
    [HasPullbacks E] [HasPullbacks F]
    {A₀ A₁ A₂ : E} {B₀ B₁ B₂ : F}
    {P₀ : Over B₀ ⥤ Over A₀} {P₁ : Over B₁ ⥤ Over A₁}
    {P₂ : Over B₂ ⥤ Over A₂}
    (a₁ : A₁ ⟶ A₀) (a₂ : A₂ ⟶ A₁) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₁)
    (c₁ : P₀ ⋙ Over.pullback a₁ ≅ Over.pullback b₁ ⋙ P₁)
    (c₂ : P₁ ⋙ Over.pullback a₂ ≅ Over.pullback b₂ ⋙ P₂) :
    P₀ ⋙ Over.pullback (a₂ ≫ a₁) ≅ Over.pullback (b₂ ≫ b₁) ⋙ P₂ :=
  Functor.isoWhiskerLeft P₀ (Over.pullbackComp a₂ a₁) ≪≫
    (Functor.associator P₀ (Over.pullback a₁) (Over.pullback a₂)).symm ≪≫
    Functor.isoWhiskerRight c₁ (Over.pullback a₂) ≪≫
    Functor.associator (Over.pullback b₁) P₁ (Over.pullback a₂) ≪≫
    Functor.isoWhiskerLeft (Over.pullback b₁) c₂ ≪≫
    (Functor.associator (Over.pullback b₁) (Over.pullback b₂) P₂).symm ≪≫
    Functor.isoWhiskerRight (Over.pullbackComp b₂ b₁).symm P₂

/-- A ring-compatible two-isomorphism on the slices, specified on both pullback coordinates.
Source: Stacks Project, Tag 04M6
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
structure RingedSliceTwoIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (g k : RingedToposMorphism R S) (t : g.inverse ≅ k.inverse)
    {A : Sheaf J (Type u)} {B : Sheaf K (Type u)} (s : A ⟶ g.inverse.obj B) where
  iso : ringedSliceInverse g.inverse s ≅
    ringedSliceInverse k.inverse (s ≫ t.hom.app B)
  first : ∀ H : Over B,
    (iso.hom.app H).left ≫ ringedSliceFirst k.inverse (s ≫ t.hom.app B) H =
      ringedSliceFirst g.inverse s H ≫ t.hom.app H.left
  ring : (iso.hom.app ((Over.star B).obj (ringSheafUnderlying S))).left ≫
      ringedSliceProjection k.inverse (s ≫ t.hom.app B) (ringSheafUnderlying S) ≫
        k.ringMap =
    ringedSliceProjection g.inverse s (ringSheafUnderlying S) ≫ g.ringMap

/-- The complete functorial relocalization system for a ringed geometric morphism.
All restriction comparisons are in the original sheaf slices; the `model` fields transport
these comparisons to the chosen element-site presentations, and the ring equations fix
compatibility with the restricted structure rings.
Source: Stacks Project, Tags 04J8, 04IH, 04IV and 04M6
(blueprint: lem-sfb-ringed-topos-slice-functoriality). -/
structure RingedToposSliceFunctorialityData
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (g : RingedToposMorphism R S) where
  source : ∀ A : Sheaf J (Type u), RingedSlicePresentation R A
  target : ∀ B : Sheaf K (Type u), RingedSlicePresentation S B
  slice : ∀ (A : Sheaf J (Type u)) (B : Sheaf K (Type u)) (s : A ⟶ g.inverse.obj B),
    RingedSliceMorphismData g s (source A) (target B)
  source_local : IsLocallyRingedTopos R →
    ∀ A : Sheaf J (Type u), IsLocallyRingedTopos (elementRing R A)
  target_local : IsLocallyRingedTopos S →
    ∀ B : Sheaf K (Type u), IsLocallyRingedTopos (elementRing S B)
  restriction : ∀ {A A' : Sheaf J (Type u)} {B B' : Sheaf K (Type u)}
    (s : A ⟶ g.inverse.obj B) (s' : A' ⟶ g.inverse.obj B')
    (a : A' ⟶ A) (b : B' ⟶ B),
    s' ≫ g.inverse.map b = a ≫ s → RingedSliceRestrictionComparison g s s' a b
  restriction_id : ∀ (A : Sheaf J (Type u)) (B : Sheaf K (Type u))
    (s : A ⟶ g.inverse.obj B) (h : s ≫ g.inverse.map (𝟙 B) = (𝟙 A) ≫ s),
    (restriction s s (𝟙 A) (𝟙 B) h).iso ≪≫
        Functor.isoWhiskerRight (Over.pullbackId (X := B)) (ringedSliceInverse g.inverse s) ≪≫
        Functor.leftUnitor (ringedSliceInverse g.inverse s) =
      Functor.isoWhiskerLeft (ringedSliceInverse g.inverse s) (Over.pullbackId (X := A)) ≪≫
        Functor.rightUnitor (ringedSliceInverse g.inverse s)
  restriction_comp : ∀ {A₀ A₁ A₂ : Sheaf J (Type u)}
    {B₀ B₁ B₂ : Sheaf K (Type u)}
    (s₀ : A₀ ⟶ g.inverse.obj B₀) (s₁ : A₁ ⟶ g.inverse.obj B₁)
    (s₂ : A₂ ⟶ g.inverse.obj B₂)
    (a₁ : A₁ ⟶ A₀) (a₂ : A₂ ⟶ A₁) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₁)
    (h₁ : s₁ ≫ g.inverse.map b₁ = a₁ ≫ s₀)
    (h₂ : s₂ ≫ g.inverse.map b₂ = a₂ ≫ s₁)
    (h : s₂ ≫ g.inverse.map (b₂ ≫ b₁) = (a₂ ≫ a₁) ≫ s₀),
    (restriction s₀ s₂ (a₂ ≫ a₁) (b₂ ≫ b₁) h).iso =
      ringedSliceRestrictionComposite a₁ a₂ b₁ b₂
        (restriction s₀ s₁ a₁ b₁ h₁).iso (restriction s₁ s₂ a₂ b₂ h₂).iso
  twoIso : ∀ (k : RingedToposMorphism R S) (t : g.inverse ≅ k.inverse),
    t.hom.app (ringSheafUnderlying S) ≫ k.ringMap = g.ringMap →
    ∀ (A : Sheaf J (Type u)) (B : Sheaf K (Type u)) (s : A ⟶ g.inverse.obj B),
      RingedSliceTwoIso g k t s
  twoIso_restriction : ∀ (k : RingedToposMorphism R S) (t : g.inverse ≅ k.inverse)
    (ht : t.hom.app (ringSheafUnderlying S) ≫ k.ringMap = g.ringMap)
    {A A' : Sheaf J (Type u)} {B B' : Sheaf K (Type u)}
    (s : A ⟶ g.inverse.obj B) (s' : A' ⟶ g.inverse.obj B')
    (a : A' ⟶ A) (b : B' ⟶ B)
    (h : s' ≫ g.inverse.map b = a ≫ s)
    (ck : RingedSliceRestrictionComparison k
      (s ≫ t.hom.app B) (s' ≫ t.hom.app B') a b),
    Functor.whiskerRight (twoIso k t ht A B s).iso.hom (Over.pullback a) ≫ ck.iso.hom =
      (restriction s s' a b h).iso.hom ≫
        Functor.whiskerLeft (Over.pullback b) (twoIso k t ht A' B' s').iso.hom

/-- Functorial local ringed relocalization along an arbitrary map into an inverse-image sheaf.

Source: Stacks Project, sites-modules.tex, Tags 04J8 and 04IH; sites.tex, Tag 04IV;
spaces-properties.tex, Tag 04M6 (blueprint: lem-sfb-ringed-topos-slice-functoriality).

Proof.
1. The inverse-image adjunction and finite-limit preservation of
   def-weil-pbc-ringed-topos-morphism induce the arrowwise adjunction on slices, using
   lem-sfb-left-exact-left-adjoint-slices. Finite limits of sheaves are sectionwise by
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Use the element-site models from
   lem-weil-pbc-ringed-sheaf-slice-adjunction.
2. Localize the slice over g⁻¹B at s:A→g⁻¹B. The iterated-slice clause of
   lem-weil-pbc-ringed-sheaf-slice-adjunction gives E/A; composing inverse images gives
   H↦g⁻¹H×[g⁻¹B]A and a left exact left adjoint.
3. In the element site the restricted ring has sections R(U). At the structure ring
   the product comparison gives g⁻¹S×A, and its structural map is g♯×id. The same
   calculation gives the projection comparison on every sheaf, naturally in that sheaf.
4. Lift each local unit cover to the element site. The equalizer of zero and one is
   the inverse image of the initial equalizer, and remains initial by adjunction.
   This proves local ringedness of both slices, including empty slices.
5. Units are the finite-limit object of pairs (x,y) with xy=yx=1, since inverses are
   unique. Left exact inverse image preserves this description. The slice unit square
   is therefore the inverse image of the original cartesian unit square and is cartesian.
6. In a compatible restriction square both inverse images have coordinates (x,a') with
   g⁻¹p(x)=s(a(a')); the B' coordinate is forced to be s'(a'). The comparisons retain
   those coordinates, so are natural and ring compatible. Identities and successive
   restrictions agree on both pullback projections, proving the two coherence equations.
7. For t:g⁻¹≅k⁻¹ use (x,a)↦(t_H(x),a). Naturality of t makes it a well-defined
   pullback map; its inverse uses t⁻¹. At S the equation k♯t_S=g♯ gives ring compatibility.
   Its maps commute with restriction because one changes x and the other retains x.
-/
theorem ringedTopos_slice_functoriality
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (g : RingedToposMorphism R S) :
    Nonempty (RingedToposSliceFunctorialityData g) := by
  sorry

end CategoryTheory
