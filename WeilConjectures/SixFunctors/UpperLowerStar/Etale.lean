/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.UpperLowerStar.Defs

/-!

# The pushforward `g_*` and the pullback `g^*` on small étale sites

For a morphism of schemes `g : Z ⟶ Y`, the pushforward and the pullback of
`WeilConjectures.SixFunctors.UpperLowerStar.Defs` (with `P = Q = @Etale`) specialize to the
small étale sites. This file records the resulting functors
`g_* : Sheaf Z.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A` and
`g^* : Sheaf Y.smallEtaleTopology A ⥤ Sheaf Z.smallEtaleTopology A`.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
Grothendieck abelian category with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes.
The site-theoretic inputs of the general definitions are discharged here:

- The base change functor `MorphismProperty.Over.pullback @Etale ⊤ g` along an *arbitrary*
  morphism `g` is continuous for the small étale topologies
  (`Etale.isContinuous_overPullback`): it preserves covers since étale covers are stable
  under base change, and it preserves compatible families since it is representably flat,
  being a finite-limit-preserving functor on the finitely complete étale slice. This is
  the `P = Q = @Etale` case of `AlgebraicGeometry.Scheme.isContinuous_overPullback` of
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`. Hence `Etale.lowerStar`
  carries no hypotheses at all.
- Sheafification on the small étale sites and the left Kan extensions along the
  opposites of base change (together with their left
  exactness) exist since `A` is Grothendieck abelian and the small étale sites are
  essentially small; the latter are the sorried instances of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension` and
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. Hence
  `Etale.upperStar` and the adjunction
  `g^* ⊣ g_*` carry no hypotheses either.
- For `g` étale, no smallness or exactness argument is needed: base change is right
  adjoint to the localization functor `MorphismProperty.Over.map ⊤ ‹Etale g›`, so its
  opposite is a *left* adjoint (`Etale.isLeftAdjoint_op_overPullback`), all pointwise
  left Kan extensions along it exist
  (`Etale.hasPointwiseLeftKanExtension_op_overPullback`), and that left Kan extension is
  precomposition with a functor, hence left exact
  (`Etale.preservesFiniteLimits_op_lan_overPullback`); these instances are proved, not
  sorried.

## Main definitions

- `AlgebraicGeometry.Etale.isContinuous_overPullback`: base change along an arbitrary
  morphism is continuous for the small étale topologies.
- `AlgebraicGeometry.Etale.isLeftAdjoint_op_overPullback` and
  `AlgebraicGeometry.Etale.hasPointwiseLeftKanExtension_op_overPullback`: the opposite of
  base change by an étale morphism is a left adjoint, and all pointwise left Kan extensions
  along it exist.
- `AlgebraicGeometry.Etale.lowerStar`: the pushforward `g_*` on étale sheaves, with scoped
  notation `(g)_*[A]`.
- `AlgebraicGeometry.Etale.upperStar`: the pullback `g^*` on étale sheaves, with scoped
  notation `(g)^*[A]`.
- `AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.Etale.lowerStarComp` and `AlgebraicGeometry.Etale.upperStarComp`:
  the composition isomorphisms `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and
  `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`.
- `AlgebraicGeometry.Etale.upperStarId`: the pullback along the identity is the identity
  functor, and `AlgebraicGeometry.Etale.upperStarComp_assoc`,
  `AlgebraicGeometry.Etale.upperStarComp_id_left` and
  `AlgebraicGeometry.Etale.upperStarComp_id_right`: the coherence of `upperStarComp`.
- `AlgebraicGeometry.Etale.preservesLimitsOfShape_lowerStar` and
  `AlgebraicGeometry.Etale.preservesFiniteLimits_lowerStar`: the pushforward `g_*`
  preserves every limit that exists in the coefficient category; in particular it is left
  exact for values in an abelian category.
- `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` and
  `AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar`: the pullback `g^*` is left
  exact, hence exact, being also a left adjoint. For an étale `g` the left exactness of
  the Kan extension is proved; for a general `g` it is the sorried instance
  `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section Continuity

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Base change along an arbitrary morphism `g : Z ⟶ Y` is continuous for the small étale
topologies. This is the `P = Q = @Etale` case of
`AlgebraicGeometry.Scheme.isContinuous_overPullback`. -/
instance Etale.isContinuous_overPullback :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale) :=
  Scheme.isContinuous_overPullback @Etale @Etale le_rfl g

end Continuity

section KanExtension

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [Etale g]

/-- For an étale morphism `g`, base change is right adjoint to the localization functor
`MorphismProperty.Over.map ⊤ ‹Etale g›`, hence its opposite is a left adjoint. -/
instance Etale.isLeftAdjoint_op_overPullback :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.IsLeftAdjoint :=
  ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g ‹Etale g› _root_.trivial).op).isLeftAdjoint

/-- For an étale morphism `g`, the opposite of base change is a left adjoint by
`Etale.isLeftAdjoint_op_overPullback`, so the indexing comma categories of the pointwise
left Kan extensions along it have terminal objects. In particular all pointwise left Kan
extensions along it exist. -/
instance Etale.hasPointwiseLeftKanExtension_op_overPullback (F : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasPointwiseLeftKanExtension F := by
  intro V
  have : HasTerminal (CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ g).op V) :=
    (mkTerminalOfRightAdjoint _
      (Adjunction.ofIsLeftAdjoint (MorphismProperty.Over.pullback @Etale ⊤ g).op) V).hasTerminal
  infer_instance

/-- For an étale morphism `g`, the left Kan extension along the opposite of base change is
precomposition with the opposite of the localization functor `MorphismProperty.Over.map ⊤
‹Etale g›`, hence preserves all limits that exist in the coefficient category. This is what
makes the pullback `g^*` left exact without any smallness or concreteness assumption on `A`;
compare `CategoryTheory.lan_preservesFiniteLimits_of_flat`. -/
instance Etale.preservesFiniteLimits_op_lan_overPullback :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  inferInstance

end KanExtension

section Star

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

namespace Etale

/-- The pushforward `g_*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
étale sites, given objectwise by `(g_* G)(V → Y) = G(V ×_Y Z → Z)`. -/
noncomputable def lowerStar :
    Sheaf Z.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  GrothendieckTopology.lowerStar A @Etale @Etale le_rfl g

@[inherit_doc Etale.lowerStar]
scoped notation "(" g ")_*[" A "]" =>
  lowerStar A g

end Etale

open Etale

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `g_* G` over `V → Y` are the sections of `G` over `V ×_Y Z → Z`. -/
lemma Etale.lowerStar_obj_val_obj (G : Sheaf Z.smallEtaleTopology A) (b : Y.Etale) :
    ((g)_*[A].obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along `(MorphismProperty.Over.pullback @Etale ⊤ g).op`. -/
lemma Etale.lowerStar_map_hom_app {G G' : Sheaf Z.smallEtaleTopology A} (φ : G ⟶ G')
    (b : Y.Etale) :
    (((g)_*[A].map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) :=
  rfl

/-- The pushforward `g_*` on étale sheaves with values in a preadditive category is
additive: it acts on morphisms by whiskering, which is compatible with the objectwise
addition. -/
instance Etale.lowerStar_additive : (g)_*[A].Additive where

/-- The pushforward `g_*` on étale sheaves preserves limits of any shape that exists in the
coefficient category. -/
instance Etale.preservesLimitsOfShape_lowerStar (E : Type*) [Category E]
    [HasLimitsOfShape E A] : PreservesLimitsOfShape E (g)_*[A] :=
  GrothendieckTopology.preservesLimitsOfShape_lowerStar A @Etale @Etale le_rfl g E

/-- The pushforward `g_*` on étale sheaves with values in an abelian category is left
exact. -/
instance Etale.preservesFiniteLimits_lowerStar : PreservesFiniteLimits (g)_*[A] :=
  GrothendieckTopology.preservesFiniteLimits_lowerStar A @Etale @Etale le_rfl g

section Adjunction

namespace Etale

/-- The pullback `g^*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
étale sites: left Kan extension on presheaves followed by sheafification. For `g` étale the
Kan extension hypothesis is automatic by
`Etale.hasPointwiseLeftKanExtension_op_overPullback`, and `g^*` is computed by restriction,
see `Etale.upperStarIsoOpenImmersionRestriction`. -/
noncomputable def upperStar :
    Sheaf Y.smallEtaleTopology A ⥤ Sheaf Z.smallEtaleTopology A :=
  GrothendieckTopology.upperStar A @Etale @Etale g

@[inherit_doc Etale.upperStar]
scoped notation "(" g ")^*[" A "]" =>
  upperStar A g

end Etale

/-- The adjunction `g^* ⊣ g_*` on sheaves for the small étale sites. -/
noncomputable def Etale.upperStarLowerStarAdjunction : (g)^*[A] ⊣ (g)_*[A] :=
  GrothendieckTopology.upperStarLowerStarAdjunction A @Etale @Etale le_rfl g

instance : (g)_*[A].IsRightAdjoint :=
  (Etale.upperStarLowerStarAdjunction A g).isRightAdjoint

instance : (g)^*[A].IsLeftAdjoint :=
  (Etale.upperStarLowerStarAdjunction A g).isLeftAdjoint

/-- The pullback `g^*` on étale sheaves is left exact, hence exact, being also a left
adjoint: sheafification on the small étale site of `Z` is left exact by the sorried
`HasSheafify` instance for the Grothendieck abelian `A`, and the left Kan
extension along the opposite of base change is left exact — for an étale `g` by
`Etale.preservesFiniteLimits_op_lan_overPullback`, in general by the sorried
`Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`, the Kan
extension being a filtered colimit and filtered colimits in the Grothendieck abelian `A`
being exact. -/
instance Etale.preservesFiniteLimits_upperStar :
    PreservesFiniteLimits (g)^*[A] :=
  inferInstanceAs (PreservesFiniteLimits (GrothendieckTopology.upperStar A @Etale @Etale g))

/-- The pullback `g^*` on étale sheaves is right exact, being a left adjoint. -/
example : PreservesFiniteColimits (g)^*[A] := inferInstance

end Adjunction

end Star

section Comp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

open Etale

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
étale sheaves. -/
noncomputable def Etale.lowerStarComp (h : T ⟶ R := h₁ ≫ h₂)
    (hh : h = h₁ ≫ h₂ := by cat_disch) : (h₁)_*[A] ⋙ (h₂)_*[A] ≅ (h)_*[A] :=
  GrothendieckTopology.lowerStarComp A @Etale @Etale le_rfl h₁ h₂ h hh

section UpperStar

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on étale
sheaves, obtained from `Etale.lowerStarComp` by uniqueness of left adjoints. -/
noncomputable def Etale.upperStarComp (h : T ⟶ R := h₁ ≫ h₂)
    (hh : h = h₁ ≫ h₂ := by cat_disch) : (h)^*[A] ≅ (h₂)^*[A] ⋙ (h₁)^*[A] :=
  GrothendieckTopology.upperStarComp A @Etale @Etale le_rfl h₁ h₂ h hh

end UpperStar

end Comp

section Coherence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Etale

/-- The pullback `(𝟙 Y)^*` along the identity is the identity functor. -/
noncomputable def Etale.upperStarId (Y : Scheme.{u}) :
    (𝟙 Y)^*[A] ≅ 𝟭 (Sheaf Y.smallEtaleTopology A) :=
  GrothendieckTopology.upperStarId A @Etale @Etale le_rfl Y

variable {R S T V : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₃ : R ⟶ V)

/-- Associativity of the composition isomorphism `Etale.upperStarComp`: the two ways of
decomposing `(h₁ ≫ h₂ ≫ h₃)^*` into `(h₃)^* ⋙ (h₂)^* ⋙ (h₁)^*` agree. -/
lemma Etale.upperStarComp_assoc (h₁₂ : T ⟶ R) (e₁₂ : h₁₂ = h₁ ≫ h₂) (h₂₃ : S ⟶ V)
    (e₂₃ : h₂₃ = h₂ ≫ h₃) (h : T ⟶ V) (e : h = h₁₂ ≫ h₃) (e' : h = h₁ ≫ h₂₃) :
    (upperStarComp A h₁₂ h₃ h e).hom ≫
        Functor.whiskerLeft ((h₃)^*[A]) (upperStarComp A h₁ h₂ h₁₂ e₁₂).hom =
      (upperStarComp A h₁ h₂₃ h e').hom ≫
        Functor.whiskerRight (upperStarComp A h₂ h₃ h₂₃ e₂₃).hom ((h₁)^*[A]) ≫
          (Functor.associator ((h₃)^*[A]) ((h₂)^*[A]) ((h₁)^*[A])).hom :=
  GrothendieckTopology.upperStarComp_assoc A @Etale @Etale le_rfl h₁ h₂ h₃ h₁₂ e₁₂ h₂₃ e₂₃ h e e'

/-- The associativity coherence `Etale.upperStarComp_assoc`, with the (identity) associator
of the triple composite left implicit. -/
lemma Etale.upperStarComp_assoc' (h₁₂ : T ⟶ R) (e₁₂ : h₁₂ = h₁ ≫ h₂) (h₂₃ : S ⟶ V)
    (e₂₃ : h₂₃ = h₂ ≫ h₃) (h : T ⟶ V) (e : h = h₁₂ ≫ h₃) (e' : h = h₁ ≫ h₂₃) :
    (upperStarComp A h₁₂ h₃ h e).hom ≫
        Functor.whiskerLeft ((h₃)^*[A]) (upperStarComp A h₁ h₂ h₁₂ e₁₂).hom =
      (upperStarComp A h₁ h₂₃ h e').hom ≫
        Functor.whiskerRight (upperStarComp A h₂ h₃ h₂₃ e₂₃).hom ((h₁)^*[A]) := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  simpa using congr_app (Etale.upperStarComp_assoc A h₁ h₂ h₃ h₁₂ e₁₂ h₂₃ e₂₃ h e e') M

/-- Unit coherence of `Etale.upperStarComp`: composing with the identity on the target. -/
lemma Etale.upperStarComp_id_right {Z Y : Scheme.{u}} (g : Z ⟶ Y) (e : g = g ≫ 𝟙 Y) :
    (upperStarComp A g (𝟙 Y) g e).hom =
      ((g)^*[A]).leftUnitor.inv ≫
        Functor.whiskerRight (Etale.upperStarId A Y).inv ((g)^*[A]) :=
  GrothendieckTopology.upperStarComp_id_right A @Etale @Etale le_rfl g e

/-- Unit coherence of `Etale.upperStarComp`: composing with the identity on the source. -/
lemma Etale.upperStarComp_id_left {Z Y : Scheme.{u}} (g : Z ⟶ Y) (e : g = 𝟙 Z ≫ g) :
    (upperStarComp A (𝟙 Z) g g e).hom =
      ((g)^*[A]).rightUnitor.inv ≫
        Functor.whiskerLeft ((g)^*[A]) (Etale.upperStarId A Z).inv :=
  GrothendieckTopology.upperStarComp_id_left A @Etale @Etale le_rfl g e

/-- The composition isomorphism `Etale.upperStarComp` is the conjugate, under the
adjunctions `g^* ⊣ g_*`, of the composition isomorphism `Etale.lowerStarComp`. -/
lemma Etale.conjugateEquiv_upperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h : T ⟶ R) (hh : h = h₁ ≫ h₂) :
    conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
        (upperStarLowerStarAdjunction A h) (upperStarComp A h₁ h₂ h hh).hom =
      (lowerStarComp A h₁ h₂ h hh).hom :=
  GrothendieckTopology.conjugateEquiv_upperStarComp_hom A @Etale @Etale le_rfl h₁ h₂ h hh

@[inherit_doc Etale.conjugateEquiv_upperStarComp_hom]
lemma Etale.conjugateEquiv_upperStarComp_inv {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h : T ⟶ R) (hh : h = h₁ ≫ h₂) :
    conjugateEquiv (upperStarLowerStarAdjunction A h)
        ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
        (upperStarComp A h₁ h₂ h hh).inv =
      (lowerStarComp A h₁ h₂ h hh).inv :=
  GrothendieckTopology.conjugateEquiv_upperStarComp_inv A @Etale @Etale le_rfl h₁ h₂ h hh

end Coherence

end AlgebraicGeometry
