# AlgebraicGeometry.ProEtale.upperStar

## Reason

Importing the assigned finite-coefficient realization together with the supplied ordinary constructible-origin or direct-image theorem fails with duplicate declarations, initially the generated notation term(_)_*[_]. Six old modules duplicate the canonical FiniteCoefficient modules. Replace their copied declarations by public re-exports of those modules. The definition bodies are identical (the canonical Defs merely adds overPullbackId). Coherence needs special care: the new canonical module used lowerStarComp_assoc and lowerStarComp_id_left for morphism equations, whereas the old API used those names for isomorphism equations. Rename the two canonical morphism equations to coefficient_lowerStarComp_assoc and coefficient_lowerStarComp_id_left and adapt their two internal proof references. Derive the renamed associativity morphism equality from the already proved legacy iso equality by taking homs and canceling the associator. Make the associator/whiskering component proof use an explicit simp-only list. Keep the composition proof under its original transparency behavior; other eta helpers can keep pullbacks irreducible during matching. These are proof optimizations, with unchanged statements and no additional holes. Restore the old isomorphism equations as aliases of the already proved legacy isomorphism equations in the canonical finite-coefficient module; the compatibility re-export must not redeclare those names. Thus both APIs can coexist and all old signatures remain available. All seven adapted modules were unclaimed when checked. No external use of the two renamed canonical morphism equations was found; their only uses are the two adapted proof lines in the canonical module.

## Old

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!

# The pushforward `g_*` and the pullback `g^*` on small pro-étale sites

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, for mathlib's pro-étale site
`AlgebraicGeometry.Scheme.ProEt.topology`: the topology on the category `X.ProEt` of
weakly étale schemes over `X` whose covers are the pro-étale covers of
[Bhatt–Scholze, Definition 4.1.1], that is, the fpqc covers by weakly étale morphisms.

For an *arbitrary* morphism of schemes `g : Z ⟶ Y`, base change induces the functor
`MorphismProperty.Over.pullback @WeaklyEtale ⊤ g : Y.ProEt ⥤ Z.ProEt` between the small
pro-étale sites, and composition with it defines the pushforward `g_*` on `A`-valued
pro-étale sheaves. Its left adjoint `g^*` is the left Kan extension on presheaves followed
by sheafification.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStar`: the pushforward `g_*`, given by composition with
  the base change functor, with scoped notation `(g)_*[A]`.
- `AlgebraicGeometry.ProEtale.upperStar`: the pullback `g^*`, given by left Kan extension
  on presheaves followed by sheafification, with scoped notation `(g)^*[A]`.
- `AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.ProEtale.lowerStarId` and `AlgebraicGeometry.ProEtale.upperStarId`: the
  identity isomorphisms `(𝟙 X)_* ≅ 𝟭` and `(𝟙 X)^* ≅ 𝟭`, the latter obtained from the former
  by uniqueness of left adjoints.
- `AlgebraicGeometry.ProEtale.lowerStarComp` and
  `AlgebraicGeometry.ProEtale.upperStarComp`: the composition isomorphisms
  `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, the latter
  obtained from the former by uniqueness of left adjoints.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback`: base change along an
  arbitrary morphism is continuous for the pro-étale topologies. It preserves covers since
  pro-étale covers are stable under base change, and it preserves compatible families since
  it is representably flat, being a finite-limit-preserving functor on the finitely
  complete pro-étale slice. It is proved in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`, and it is what makes
  `ProEtale.lowerStar` carry no hypotheses at all.
- `AlgebraicGeometry.ProEtale.isLeftAdjoint_op_overPullback` and
  `AlgebraicGeometry.ProEtale.hasPointwiseLeftKanExtension_op_overPullback`: for `g` weakly
  étale, the opposite of base change is a left adjoint — base change is right adjoint to
  the localization functor `MorphismProperty.Over.map ⊤ ‹WeaklyEtale g›` — and all pointwise
  left Kan extensions along it exist. For a general `g` the pointwise left Kan extensions
  instead exist by essential `u + 1`-smallness of the indexing comma categories,
  `CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
  `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, with no smallness of
  the small pro-étale site itself.
- `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_lowerStar` and
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_lowerStar`: the pushforward `g_*`
  preserves every limit that exists in the coefficient category. This needs no hypothesis
  beyond the continuity of the base change functor, in particular it does not use the
  adjunction `g^* ⊣ g_*`.
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overPullback` and
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar`: the pullback `g^*` is left
  exact, hence exact, being also a left adjoint. In contrast to `g_*` this is not
  automatic: it needs sheafification to be left exact and the left Kan extension along the
  opposite of base change to be so as well. For a weakly étale `g` the latter is proved
  here, the Kan extension being precomposition with a right adjoint; for a general `g` it is
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`.

## Implementation notes

- The coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
  universe `u + 1`, one above the universe `u` of the base schemes, following the
  convention of the `SixFunctors` folder.
- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`, which requires
  `WeaklyEtale g`. This is essential for compactifications, whose structure morphism is
  proper and in general is not weakly étale.
- Sheafification on the small pro-étale sites and the left Kan extensions along the
  opposite of base change both hold for every Grothendieck abelian `A`, so
  `ProEtale.upperStar` and the adjunction `g^* ⊣ g_*` carry no hypotheses either.
  Sheafification is
  `CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, still sorried through
  `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` there, and it does
  use essential smallness of the site. The Kan extensions are proved and use no smallness
  of the site at all, only of the indexing comma categories, see
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

section KanExtension

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]

/-- For a weakly étale morphism `g`, base change is right adjoint to the localization
functor `MorphismProperty.Over.map ⊤ ‹WeaklyEtale g›`, hence its opposite is a left
adjoint. -/
instance ProEtale.isLeftAdjoint_op_overPullback :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.IsLeftAdjoint :=
  ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g ‹WeaklyEtale g›
    _root_.trivial).op).isLeftAdjoint

/-- For a weakly étale morphism `g`, the opposite of base change is a left adjoint by
`ProEtale.isLeftAdjoint_op_overPullback`, so the indexing comma categories of the pointwise
left Kan extensions along it have terminal objects. In particular all pointwise left Kan
extensions along it exist. -/
instance ProEtale.hasPointwiseLeftKanExtension_op_overPullback (F : Y.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.HasPointwiseLeftKanExtension F := by
  intro V
  have : HasTerminal
      (CostructuredArrow (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op V) :=
    (mkTerminalOfRightAdjoint _
      (Adjunction.ofIsLeftAdjoint
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op) V).hasTerminal
  infer_instance

/-- For a weakly étale morphism `g`, the left Kan extension along the opposite of base
change is precomposition with the opposite of the localization functor
`MorphismProperty.Over.map ⊤ ‹WeaklyEtale g›`, hence preserves all limits that exist in the
coefficient category. This is what makes the pullback `g^*` left exact without any
smallness or concreteness assumption on `A`; compare
`CategoryTheory.lan_preservesFiniteLimits_of_flat`. -/
instance ProEtale.preservesFiniteLimits_op_lan_overPullback :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan :
      (Y.ProEtᵒᵖ ⥤ A) ⥤ Z.ProEtᵒᵖ ⥤ A) :=
  inferInstance

end KanExtension

section Star

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

namespace ProEtale

/-- The pushforward `g_*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
pro-étale sites, given objectwise by `(g_* G)(V → Y) = G(V ×_Y Z → Z)`. The continuity of
the base change functor is `AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback`. -/
noncomputable def lowerStar :
    Sheaf (Scheme.ProEt.topology Z) A ⥤ Sheaf (Scheme.ProEt.topology Y) A :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

@[inherit_doc ProEtale.lowerStar]
scoped notation "(" g ")_*[" A "]" =>
  lowerStar A g

end ProEtale

open ProEtale

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `g_* G` over `V → Y` are the sections of `G` over `V ×_Y Z → Z`. -/
lemma ProEtale.lowerStar_obj_val_obj (G : Sheaf (Scheme.ProEt.topology Z) A) (b : Y.ProEt) :
    ((g)_*[A].obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along
`(MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op`. -/
lemma ProEtale.lowerStar_map_hom_app {G G' : Sheaf (Scheme.ProEt.topology Z) A} (φ : G ⟶ G')
    (b : Y.ProEt) :
    (((g)_*[A].map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj b)) :=
  rfl

/-- The pushforward `g_*` on pro-étale sheaves with values in a preadditive category is
additive: it acts on morphisms by whiskering, which is compatible with the objectwise
addition. -/
instance ProEtale.lowerStar_additive : (g)_*[A].Additive where

/-- `g_*` preserves limits of any shape that exists in the coefficient category: it is
given by restriction along the base change functor, and limits of sheaves are computed
pointwise on the underlying presheaves. -/
instance ProEtale.preservesLimitsOfShape_lowerStar (E : Type*) [Category E]
    [HasLimitsOfShape E A] : PreservesLimitsOfShape E (g)_*[A] :=
  inferInstanceAs (PreservesLimitsOfShape E
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)))

/-- `g_*` is left exact. Note that this does not use the adjunction `g^* ⊣ g_*`. -/
instance ProEtale.preservesFiniteLimits_lowerStar : PreservesFiniteLimits (g)_*[A] :=
  inferInstanceAs (PreservesFiniteLimits
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).sheafPushforwardContinuous A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)))

section Adjunction

namespace ProEtale

/-- The pullback `g^*` along an arbitrary morphism `g : Z ⟶ Y` on sheaves for the small
pro-étale sites: left Kan extension on presheaves followed by sheafification, left adjoint
to `ProEtale.lowerStar`. The Kan extensions are provided by
`CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
`WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, and the sheafification by
`CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, which is still sorried
through `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall`. For `g`
weakly étale the Kan extension hypothesis is automatic by
`ProEtale.hasPointwiseLeftKanExtension_op_overPullback`, and `g^*` is computed by
restriction, see `ProEtale.upperStarIsoOpenImmersionRestriction`. -/
noncomputable def upperStar :
    Sheaf (Scheme.ProEt.topology Y) A ⥤ Sheaf (Scheme.ProEt.topology Z) A :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

@[inherit_doc ProEtale.upperStar]
scoped notation "(" g ")^*[" A "]" =>
  upperStar A g

end ProEtale

/-- The adjunction `g^* ⊣ g_*` on sheaves for the small pro-étale sites. -/
noncomputable def ProEtale.upperStarLowerStarAdjunction : (g)^*[A] ⊣ (g)_*[A] :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) A
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

instance : (g)_*[A].IsRightAdjoint :=
  (ProEtale.upperStarLowerStarAdjunction A g).isRightAdjoint

instance : (g)^*[A].IsLeftAdjoint :=
  (ProEtale.upperStarLowerStarAdjunction A g).isLeftAdjoint

/-- The pullback `g^*` on pro-étale sheaves is left exact, hence exact, being also a left
adjoint: `g^*` is the composite of the inclusion of sheaves into presheaves, which preserves
finite limits, the left Kan extension along the opposite of base change, and sheafification,
which is left exact by `HasSheafify`. The left exactness of the Kan extension is
`ProEtale.preservesFiniteLimits_op_lan_overPullback` for a weakly étale `g`, and in general
`ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`, the Kan
extension being a filtered colimit and filtered colimits in the Grothendieck abelian `A`
being exact. -/
instance ProEtale.preservesFiniteLimits_upperStar
    [PreservesFiniteLimits ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan :
      (Y.ProEtᵒᵖ ⥤ A) ⥤ Z.ProEtᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (g)^*[A] := by
  unfold ProEtale.upperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

/-- The pullback `g^*` on pro-étale sheaves is right exact, being a left adjoint. -/
example : PreservesFiniteColimits (g)^*[A] := inferInstance

/-- The pullback `g^*` on pro-étale sheaves is additive, being a left adjoint. -/
instance ProEtale.additive_upperStar : (g)^*[A].Additive :=
  (ProEtale.upperStarLowerStarAdjunction A g).left_adjoint_additive

/-- The pullback `g^*` on pro-étale sheaves preserves homology, being exact: it preserves
finite limits by `ProEtale.preservesFiniteLimits_upperStar` and all colimits of size `0`,
being a left adjoint. -/
instance ProEtale.preservesHomology_upperStar : (g)^*[A].PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} (g)^*[A] :=
    (ProEtale.upperStarLowerStarAdjunction A g).leftAdjoint_preservesColimits
  -- the two fields of `PreservesHomology` are `autoParam`s, found by instance synthesis
  -- from `ProEtale.preservesFiniteLimits_upperStar` and from `this`
  exact {}

end Adjunction

end Star

section Id

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

open ProEtale

/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭` of the pushforward on pro-étale sheaves: base
change along `𝟙 X` is the identity functor by `MorphismProperty.Over.pullbackId`. This is
the pro-étale counterpart of `AlgebraicGeometry.Etale.lowerStarId`. -/
noncomputable def ProEtale.lowerStarId : (𝟙 X)_*[A] ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) A
    (Scheme.ProEt.topology X)

/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the pullback on pro-étale sheaves, obtained
from `ProEtale.lowerStarId` by uniqueness of left adjoints: both sides are left adjoint to
`(𝟙 X)_*`. This is the pro-étale counterpart of `AlgebraicGeometry.Etale.upperStarId`. -/
noncomputable def ProEtale.upperStarId : (𝟙 X)^*[A] ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A (𝟙 X))).symm
    (lowerStarId A X).symm

/-- Under the conjugation bijection between the adjunctions `𝟭 ⊣ 𝟭` and `(𝟙 X)^* ⊣ (𝟙 X)_*`,
the identity isomorphism of the pullback corresponds to the inverse of the identity
isomorphism of the pushforward:

```
  (𝟙 X)^* ⊣ (𝟙 X)_*        upperStarId : (𝟙 X)^* ≅ 𝟭
      ↕ conjugate                  ↦
      𝟭 ⊣ 𝟭               lowerStarId.symm : 𝟭 ≅ (𝟙 X)_*
```

This is the pro-étale counterpart of `AlgebraicGeometry.Etale.conjugateIsoEquiv_upperStarId`. -/
lemma ProEtale.conjugateIsoEquiv_upperStarId :
    conjugateIsoEquiv Adjunction.id (upperStarLowerStarAdjunction A (𝟙 X))
        (upperStarId A X) = (lowerStarId A X).symm :=
  Equiv.apply_symm_apply _ _

end Id

section Comp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

open ProEtale

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
pro-étale sheaves: both sides send a sheaf `G` to the sheaf `(V → R) ↦ G(V ×_R T → T)`, up
to the pullback pasting isomorphism `(V ×_R S) ×_S T ≅ V ×_R T` of
`MorphismProperty.Over.pullbackComp`. -/
noncomputable def ProEtale.lowerStarComp : (h₁)_*[A] ⋙ (h₂)_*[A] ≅ (h₁ ≫ h₂)_*[A] :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).symm) A
    (Scheme.ProEt.topology R) (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)

section UpperStar

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on pro-étale
sheaves, obtained from `ProEtale.lowerStarComp` by uniqueness of left adjoints: both sides
are left adjoint to `(h₁)_* ⋙ (h₂)_*`. -/
noncomputable def ProEtale.upperStarComp : (h₁ ≫ h₂)^*[A] ≅ (h₂)^*[A] ⋙ (h₁)^*[A] :=
  ((conjugateIsoEquiv (ProEtale.upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((ProEtale.upperStarLowerStarAdjunction A h₂).comp
        (ProEtale.upperStarLowerStarAdjunction A h₁))).symm
    (ProEtale.lowerStarComp A h₁ h₂).symm).symm

end UpperStar

end Comp

end AlgebraicGeometry
```

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

```lean
/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Equivalence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# Pushforward and pullback of pro-étale sheaves along an isomorphism

For an isomorphism of schemes `e : X ≅ Y`, the pushforwards `(e.hom)_*` and `(e.inv)_*` on
pro-étale sheaves are mutually inverse equivalences, by the identity and composition
isomorphisms `ProEtale.lowerStarId` and `ProEtale.lowerStarComp`. Consequently the pullback
`(e.hom)^*`, the left adjoint of `(e.hom)_*`, is the pushforward `(e.inv)_*` along the inverse.

Pushforwards are given by an explicit formula, `(g_* G)(V) = G(V ×_Y Z)`, and they are lax
monoidal; pullbacks are only characterised by their universal property. This is why the
Frobenius pullbacks of Weil sheaves (`WeilConjectures.WeilSheaf.Category`) are realised as
pushforwards along the inverse Frobenius.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStarCongr`: `g_* ≅ g'_*` for `g = g'`.
- `AlgebraicGeometry.ProEtale.upperStarCompIso`: `a^* ∘ b^* ≅ c^* ∘ d^*` for `a ≫ b = c ≫ d`.
- `AlgebraicGeometry.ProEtale.lowerStarEquivalence`: the equivalence `(e.hom)_*` with inverse
  `(e.inv)_*`.
- `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`: `(e.hom)^* ≅ (e.inv)_*`.

## Main results

- `AlgebraicGeometry.ProEtale.lowerStarEquivalence_symm_symm_toAdjunction`: the adjunctions
  `(e.hom)_* ⊣ (e.inv)_*` obtained from `lowerStarEquivalence e` and from
  `lowerStarEquivalence e.symm` agree. This rests on the triangle identity
  `AlgebraicGeometry.ProEtale.lowerStar_map_unit_comp_counit` for the identity and composition
  isomorphisms of pushforwards.
- `AlgebraicGeometry.ProEtale.conjugateEquiv_upperStarComp_hom`,
  `AlgebraicGeometry.ProEtale.conjugateEquiv_upperStarComp_inv` and
  `AlgebraicGeometry.ProEtale.conjugateEquiv_upperStarCongr_inv`: the composition and congruence
  isomorphisms of pullbacks are conjugate to those of pushforwards.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

/-- The pushforwards along equal morphisms are isomorphic. -/
noncomputable def lowerStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)_*[A] ≅ (g')_*[A] :=
  eqToIso (by rw [h])

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarCongr_rfl {Z Y : Scheme.{u}} {g : Z ⟶ Y} :
    lowerStarCongr A (rfl : g = g) = Iso.refl _ :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along the opposite of base change; the form of
`ProEtale.lowerStar_map_hom_app` at an object of the opposite site. -/
lemma lowerStar_map_hom_app' {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {G G' : Sheaf (ProEt.topology Z) A} (φ : G ⟶ G') (V : Y.ProEtᵒᵖ) :
    ((g)_*[A].map φ).hom.app V =
      φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` are the
restriction maps along the pullback pasting isomorphisms. -/
lemma lowerStarComp_hom_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (ProEt.topology T) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop).op := by
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.id_comp _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_inv_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (G : Sheaf (ProEt.topology T) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).inv.app V.unop).op := by
  simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of `g_* ≅ g'_*` for `g = g'` are the restriction maps along the canonical
isomorphisms `V ×_{Y,g'} Z ≅ V ×_{Y,g} Z`. -/
lemma lowerStarCongr_hom_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A h).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).inv.app V.unop).op := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app]
  rw [show (MorphismProperty.Over.pullbackCongr (rfl : g = g)).inv.app V.unop = 𝟙 _ from
    MorphismProperty.Over.Hom.ext (by simp [MorphismProperty.Over.pullbackCongr]; rfl), op_id,
    G.obj.map_id]
  rfl

/-- The pullbacks along equal morphisms are isomorphic. -/
noncomputable def upperStarCongr {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    (g)^*[A] ≅ (g')^*[A] :=
  eqToIso (by rw [h])

/-- The pullbacks along the two sides of a commutative square `a ≫ b = c ≫ d` agree:
`a^* ∘ b^* ≅ (a ≫ b)^* = (c ≫ d)^* ≅ c^* ∘ d^*`. -/
noncomputable def upperStarCompIso {Y Z₁ Z₂ T : Scheme.{u}} {a : Y ⟶ Z₁} {b : Z₁ ⟶ T}
    {c : Y ⟶ Z₂} {d : Z₂ ⟶ T} (h : a ≫ b = c ≫ d) :
    (b)^*[A] ⋙ (a)^*[A] ≅ (d)^*[A] ⋙ (c)^*[A] :=
  (upperStarComp A a b).symm ≪≫ upperStarCongr A h ≪≫ upperStarComp A c d

variable {X Y : Scheme.{u}}

/-- The pushforward along an isomorphism `e : X ≅ Y` is an equivalence of categories of
pro-étale sheaves, with inverse the pushforward along `e.inv`. -/
noncomputable def lowerStarEquivalence (e : X ≅ Y) :
    Sheaf (ProEt.topology X) A ≌ Sheaf (ProEt.topology Y) A :=
  CategoryTheory.Equivalence.mk (e.hom)_*[A] (e.inv)_*[A]
    ((lowerStarId A X).symm ≪≫ lowerStarCongr A e.hom_inv_id.symm ≪≫
      (lowerStarComp A e.hom e.inv).symm)
    (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarEquivalence_functor (e : X ≅ Y) :
    (lowerStarEquivalence A e).functor = (e.hom)_*[A] :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
@[simp]
lemma lowerStarEquivalence_inverse (e : X ≅ Y) :
    (lowerStarEquivalence A e).inverse = (e.inv)_*[A] :=
  rfl

/-- The pullback along an isomorphism `e` is the pushforward along its inverse: both are left
adjoint to the pushforward `(e.hom)_*`. -/
noncomputable def upperStarIsoLowerStarInv (e : X ≅ Y) : (e.hom)^*[A] ≅ (e.inv)_*[A] :=
  (upperStarLowerStarAdjunction A e.hom).leftAdjointUniq
    (lowerStarEquivalence A e).symm.toAdjunction


section Coherence

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The pushforwards along equal morphisms are identified through the base change functors:
`lowerStarCongr` is induced by `MorphismProperty.Over.pullbackCongr`. -/
lemma lowerStarCongr_eq {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g') :
    lowerStarCongr A h = Functor.sheafPushforwardContinuousIso
      (MorphismProperty.Over.pullbackCongr h) A _ _ := by
  subst h
  ext M V
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, MorphismProperty.Over.pullbackCongr_refl,
    Functor.sheafPushforwardContinuousIso_hom, Functor.sheafPushforwardContinuousNatTrans_app_hom,
    Functor.whiskerRight_app, NatTrans.op_app, Iso.refl_inv, op_id]
  exact (((sheafToPresheaf (ProEt.topology Z) A).obj M).map_id _).symm

/-- The triangle identity for base change along an isomorphism `e : X ≅ Y` on the small
pro-étale sites, built from `MorphismProperty.Over.pullbackId`,
`MorphismProperty.Over.pullbackCongr` and `MorphismProperty.Over.pullbackComp`. -/
lemma overPullback_triangle {X Y : Scheme.{u}} (e : X ≅ Y) (V : Y.ProEt) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).inv.app V) ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).map
        ((MorphismProperty.Over.pullbackCongr e.inv_hom_id).inv.app V) ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).map
        ((MorphismProperty.Over.pullbackComp e.inv e.hom).hom.app V) ≫
      (MorphismProperty.Over.pullbackComp e.hom e.inv).inv.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj V) ≫
      (MorphismProperty.Over.pullbackCongr e.hom_inv_id.symm).inv.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj V) ≫
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ e.hom).obj V) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, pullback.condition_assoc]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The triangle identity `(e.hom)_* η ≫ ε (e.hom)_* = 𝟙` for the unit and counit of
`lowerStarEquivalence e` before adjointification. It is the image under pushforward of the
triangle identity `overPullback_triangle` on the sites. -/
lemma lowerStar_map_unit_comp_counit {X Y : Scheme.{u}} (e : X ≅ Y)
    (S : Sheaf (ProEt.topology X) A) :
    (e.hom)_*[A].map (((lowerStarId A X).symm ≪≫ lowerStarCongr A e.hom_inv_id.symm ≪≫
      (lowerStarComp A e.hom e.inv).symm).hom.app S) ≫
      (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y).hom.app
        ((e.hom)_*[A].obj S) = 𝟙 _ := by
  have := Functor.sheafPushforwardContinuous_triangle (A := A)
    (J := ProEt.topology X) (K := ProEt.topology Y)
    (MorphismProperty.Over.pullbackComp e.hom e.inv).symm
    (MorphismProperty.Over.pullbackComp e.inv e.hom).symm
    (MorphismProperty.Over.pullbackCongr e.hom_inv_id.symm)
    (MorphismProperty.Over.pullbackCongr e.inv_hom_id)
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X)
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y) (overPullback_triangle e) S
    (hP := ProEt.isContinuous_overPullback _) (hQ := ProEt.isContinuous_overPullback _)
    (hRX := ProEt.isContinuous_overPullback _) (hR'X := ProEt.isContinuous_overPullback _)
    (hRY := ProEt.isContinuous_overPullback _) (hR'Y := ProEt.isContinuous_overPullback _)
  rw [lowerStarCongr_eq, lowerStarCongr_eq]
  exact this

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The adjunctions `(e.hom)_* ⊣ (e.inv)_*` given by `lowerStarEquivalence e` and by
`lowerStarEquivalence e.symm` agree: the unit of the first is the adjointification of a unit
which already satisfies the triangle identity `lowerStar_map_unit_comp_counit`, and the unit of
the second is the inverse of the counit of `lowerStarEquivalence e.symm`, which is the same
composite of identity, congruence and composition isomorphisms. -/
lemma lowerStarEquivalence_symm_symm_toAdjunction (e : X ≅ Y) :
    (lowerStarEquivalence A e.symm).symm.toAdjunction =
      (lowerStarEquivalence A e).toAdjunction := by
  apply Adjunction.ext
  have := Equivalence.adjointifyη_eq _ _ (lowerStar_map_unit_comp_counit A e)
  change (lowerStarComp A e.hom e.inv ≪≫ lowerStarCongr A e.symm.inv_hom_id ≪≫
    lowerStarId A X).inv = (Equivalence.adjointifyη _ _).hom
  rw [this]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

/-- The congruence isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_upperStarCongr_inv {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    conjugateEquiv (upperStarLowerStarAdjunction A g) (upperStarLowerStarAdjunction A g')
      (upperStarCongr A h).inv = (lowerStarCongr A h).hom := by
  subst h
  simp [upperStarCongr, lowerStarCongr]

/-- The composition isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_upperStarComp_hom {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
      (upperStarLowerStarAdjunction A (h₁ ≫ h₂)) (upperStarComp A h₁ h₂).hom =
        (lowerStarComp A h₁ h₂).hom := by
  have := conjugateEquiv_comm (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
    ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
    (α := (upperStarComp A h₁ h₂).inv) (β := (upperStarComp A h₁ h₂).hom) (by simp)
  have h : conjugateEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
      (upperStarComp A h₁ h₂).inv = (lowerStarComp A h₁ h₂).inv :=
    congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (lowerStarComp A h₁ h₂).symm)
  rw [h] at this
  rw [← cancel_epi (lowerStarComp A h₁ h₂).inv, this, Iso.inv_hom_id]

/-- The inverse composition isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateEquiv_upperStarComp_inv {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
      (upperStarComp A h₁ h₂).inv = (lowerStarComp A h₁ h₂).inv :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (lowerStarComp A h₁ h₂).symm)

end Coherence

variable {Z W : Scheme.{u}} (g : Z ⟶ W) [IsIso g]

instance isEquivalence_lowerStar : (g)_*[A].IsEquivalence :=
  (lowerStarEquivalence A (asIso g)).isEquivalence_functor

instance isEquivalence_upperStar : (g)^*[A].IsEquivalence :=
  Functor.isEquivalence_of_iso (upperStarIsoLowerStarInv A (asIso g)).symm

end ProEtale

end AlgebraicGeometry
```

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!

# The pushforward `g_*` is lax symmetric monoidal and the pullback `g^*` is monoidal

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`.

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued pro-étale sheaves is lax braided. This is the general
statement for the pushforward along a continuous functor of sites, applied to the base
change functor; when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

The pullback `g^*`, the left adjoint of `g_*`, is oplax monoidal and the adjunction
`g^* ⊣ g_*` is monoidal. Base change is representably flat, so if tensoring in `A` commutes
with filtered colimits, `g^*` is strong monoidal. If `g` is an isomorphism, the adjunction is
an equivalence, and then the pushforward `g_*` is strong monoidal as well.

## Main results

- `AlgebraicGeometry.ProEtale.laxBraided_lowerStar`: the pushforward `g_*` is lax braided.
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarLowerStarAdjunction`: the adjunction
  `g^* ⊣ g_*` is monoidal.
- `AlgebraicGeometry.ProEtale.monoidal_upperStar`: if tensoring in `A` commutes with filtered
  colimits, the pullback `g^*` is strong monoidal.
- `AlgebraicGeometry.ProEtale.isIso_lowerStar_μ` and `AlgebraicGeometry.ProEtale.isIso_lowerStar_ε`:
  the comparison maps of the pushforward along an isomorphism are invertible.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology Z).W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pushforward `g_*` on pro-étale sheaves is lax monoidal, being the pushforward along
the continuous base change functor. -/
noncomputable instance ProEtale.laxMonoidal_lowerStar : (g)_*[A].LaxMonoidal := by
  unfold ProEtale.lowerStar
  infer_instance

/-- The pushforward `g_*` on pro-étale sheaves is lax braided. When `A` is symmetric, this
says that `g_*` is lax symmetric monoidal. -/
noncomputable instance ProEtale.laxBraided_lowerStar : (g)_*[A].LaxBraided := by
  unfold ProEtale.lowerStar
  infer_instance

/-- The pullback `g^*` on pro-étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal pushforward `g_*`. -/
noncomputable instance ProEtale.oplaxMonoidal_upperStar : (g)^*[A].OplaxMonoidal :=
  (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal

/-- The adjunction `g^* ⊣ g_*` on pro-étale sheaves is monoidal, for the oplax structure
`ProEtale.oplaxMonoidal_upperStar` on `g^*` and the lax structure `ProEtale.laxMonoidal_lowerStar`
on `g_*`. -/
instance ProEtale.isMonoidal_upperStarLowerStarAdjunction :
    (ProEtale.upperStarLowerStarAdjunction A g).IsMonoidal := by
  let := (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal
  infer_instance

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The comparison map `η : g^*𝟙 ⟶ 𝟙` of the oplax monoidal pullback is an isomorphism. This is
`CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback` for the base change
functor, whose comma categories are connected, being filtered: base change is representably
flat by `CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`. -/
instance ProEtale.isIso_upperStar_η : IsIso (η (g)^*[A]) := by
  unfold ProEtale.upperStar
  infer_instance

section FilteredColimits

/- Tensoring in `A` on the left commutes with filtered colimits of the size of the comma
categories `CostructuredArrow` of base change, e.g. if `A` is closed. Via the braiding, so does
tensoring on the right. -/
variable [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

/-- If tensoring in `A` commutes with filtered colimits (e.g. if `A` is closed), the comparison
map `δ : g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` of the oplax monoidal pullback is an isomorphism. This is
`CategoryTheory.Functor.sheafPullbackConstruction.isIso_δ_sheafPullback` for the base change
functor, whose comma categories are filtered since base change is representably flat. -/
instance ProEtale.isIso_upperStar_δ (F G : Sheaf (Scheme.ProEt.topology Y) A) :
    IsIso (δ (g)^*[A] F G) := by
  unfold ProEtale.upperStar
  infer_instance

/-- If tensoring in `A` commutes with filtered colimits (e.g. if `A` is closed), the pullback
`g^*` on pro-étale sheaves is strong monoidal, its oplax structure being
`ProEtale.oplaxMonoidal_upperStar` by definition. -/
noncomputable instance ProEtale.monoidal_upperStar : (g)^*[A].Monoidal :=
  .ofOplaxMonoidal _

/-- The tensor comparison map `μ : g_*F ⊗ g_*G ⟶ g_*(F ⊗ G)` of the pushforward along an
isomorphism `g` is invertible: `g^* ⊣ g_*` is then a monoidal adjoint equivalence whose left
adjoint is strong monoidal (`CategoryTheory.Adjunction.isIso_μ_of_isIso_δ`). -/
instance ProEtale.isIso_lowerStar_μ [IsIso g] (F G : Sheaf (Scheme.ProEt.topology Z) A) :
    IsIso (μ (g)_*[A] F G) :=
  (ProEtale.upperStarLowerStarAdjunction A g).isIso_μ_of_isIso_δ F G

end FilteredColimits

/-- The unit comparison map `ε : 𝟙 ⟶ g_*𝟙` of the pushforward along an isomorphism `g` is
invertible: `g^* ⊣ g_*` is then a monoidal adjoint equivalence and `η : g^*𝟙 ⟶ 𝟙` is
invertible (`CategoryTheory.Adjunction.isIso_ε_of_isIso_η`). -/
instance ProEtale.isIso_lowerStar_ε [IsIso g] : IsIso (ε (g)_*[A]) :=
  (ProEtale.upperStarLowerStarAdjunction A g).isIso_ε_of_isIso_η

end AlgebraicGeometry
```

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

```lean
/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!
# Coherence of the pushforwards and pullbacks on the small pro-étale sites

The composition isomorphisms `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*`
(`AlgebraicGeometry.ProEtale.lowerStarComp`) and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`
(`AlgebraicGeometry.ProEtale.upperStarComp`) satisfy the associativity law: the two ways of
identifying the pushforward (resp. pullback) along `f ≫ g ≫ h` with the composite of the three
pushforwards (resp. pullbacks) agree, up to the identification `(f ≫ g) ≫ h = f ≫ (g ≫ h)`.
For the pushforwards this is the associativity of base change
(`CategoryTheory.MorphismProperty.Over.pullbackComp_assoc`); it passes to the pullbacks by
conjugation along the adjunctions `g^* ⊣ g_*`.

This is the pro-étale counterpart of `CategoryTheory.GrothendieckTopology.upperStarComp_assoc`.

## Main results

- `AlgebraicGeometry.ProEtale.lowerStarComp_assoc` and
  `AlgebraicGeometry.ProEtale.upperStarComp_assoc`: the associativity laws.
- `AlgebraicGeometry.ProEtale.upperStarComp_hom_app_assoc`: the associativity law for the
  pullbacks, evaluated at a sheaf.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Conjugate

variable {R S T : Scheme.{u}}

/-- The composition isomorphism of the pullbacks is conjugate to that of the pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁)) (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      (upperStarComp A h₁ h₂) = lowerStarComp A h₁ h₂ := by
  ext : 1
  exact conjugateEquiv_upperStarComp_hom A h₁ h₂

/-- The congruence isomorphism of the pullbacks is conjugate to the inverse of that of the
pushforwards. -/
lemma conjugateIsoEquiv_upperStarCongr {g g' : S ⟶ R} (h : g = g') :
    conjugateIsoEquiv (upperStarLowerStarAdjunction A g') (upperStarLowerStarAdjunction A g)
      (upperStarCongr A h) = (lowerStarCongr A h).symm := by
  subst h
  ext : 1
  simp [upperStarCongr, lowerStarCongr]

end Conjugate

section Components

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction maps of `g_* G` are those of `G` along the base changes. -/
lemma lowerStar_obj_obj_map' {Z W : Scheme.{u}} (g : Z ⟶ W) (G : Sheaf (ProEt.topology Z) A)
    {V V' : W.ProEtᵒᵖ} (φ : V ⟶ V') :
    ((g)_*[A].obj G).obj.map φ =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map φ.unop).op :=
  rfl

end Components

section Assoc

variable {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)

set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for the composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_assoc :
    (f)_*[A].associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫ lowerStarComp A f (g ≫ h) =
      Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h ≪≫
        lowerStarCongr A (Category.assoc f g h) := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [Quiver.Hom.unop_op]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
    · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]

/-- The associativity law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.lowerStarComp_assoc` by conjugation. -/
lemma upperStarComp_assoc :
    upperStarComp A f (g ≫ h) ≪≫ Functor.isoWhiskerRight (upperStarComp A g h) (f)^*[A] ≪≫
        (h)^*[A].associator (g)^*[A] (f)^*[A] =
      upperStarCongr A (Category.assoc f g h).symm ≪≫ upperStarComp A (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (h)^*[A] (upperStarComp A f g) := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A h).comp
    ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f)))
    (upperStarLowerStarAdjunction A (f ≫ g ≫ h))).injective ?_
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A (g ≫ h)).comp
      (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A g)).comp (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A ((f ≫ g) ≫ h)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A (f ≫ g))) _]
  simp only [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_upperStarCongr, Iso.trans_assoc]
  rw [lowerStarComp_assoc]
  congr 2

/-- The associativity law for the composition isomorphisms of the pullbacks, evaluated at a
sheaf. -/
lemma upperStarComp_hom_app_comp_upperStarComp_hom_app (M : Sheaf (ProEt.topology V) A) :
    (upperStarComp A (f ≫ g) h).hom.app M ≫ (upperStarComp A f g).hom.app ((h)^*[A].obj M) =
      (upperStarCongr A (Category.assoc f g h)).hom.app M ≫
        (upperStarComp A f (g ≫ h)).hom.app M ≫ (f)^*[A].map ((upperStarComp A g h).hom.app M) := by
  have := congrArg (fun e ↦ e.hom.app M) (upperStarComp_assoc A f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id] at this
  rw [this, ← Category.assoc, ← NatTrans.comp_app, ← Iso.trans_hom]
  simp [upperStarCongr]

end Assoc


section Paste

variable {P P' P'' Y Y' Y'' Z : Scheme.{u}}

/-- The composition isomorphism `a^* ≅ c^* ⋙ b^*` of pullbacks along a factorisation
`b ≫ c = a`. -/
noncomputable def upperStarFactor {a : P ⟶ Y} {b : P ⟶ Z} {c : Z ⟶ Y} (e : b ≫ c = a) :
    (a)^*[A] ≅ (c)^*[A] ⋙ (b)^*[A] :=
  upperStarCongr A e.symm ≪≫ upperStarComp A b c

/-- The factorisation isomorphism of the trivial factorisation is the composition isomorphism. -/
lemma upperStarFactor_rfl (b : P ⟶ Z) (c : Z ⟶ Y) :
    upperStarFactor A (rfl : b ≫ c = b ≫ c) = upperStarComp A b c := by
  simp only [upperStarFactor, upperStarCongr, eqToIso_refl, Iso.refl_trans]

/-- The isomorphism of a commutative square `a ≫ b = c ≫ d` in terms of factorisations of a
common composite `k`. -/
lemma upperStarCompIso_eq_upperStarFactor {Z₁ Z₂ : Scheme.{u}} {a : P ⟶ Z₁} {b : Z₁ ⟶ Y}
    {c : P ⟶ Z₂} {d : Z₂ ⟶ Y} (h : a ≫ b = c ≫ d) {k : P ⟶ Y} (e₁ : a ≫ b = k)
    (e₂ : c ≫ d = k) :
    upperStarCompIso A h = (upperStarFactor A e₁).symm ≪≫ upperStarFactor A e₂ := by
  subst e₁
  rw [upperStarFactor_rfl]
  rfl

/-- The associativity law for the factorisation isomorphisms. -/
lemma upperStarFactor_hom_app_assoc {a : P'' ⟶ Y} {x : P'' ⟶ P'} {y : P' ⟶ Z} {z : Z ⟶ Y}
    {b : P' ⟶ Y} {c : P'' ⟶ Z} (e_b : y ≫ z = b) (e_a : x ≫ b = a) (e_c : x ≫ y = c)
    (e_a' : c ≫ z = a) (M : Sheaf (ProEt.topology Y) A) :
    (upperStarFactor A e_a).hom.app M ≫ (x)^*[A].map ((upperStarFactor A e_b).hom.app M) =
      (upperStarFactor A e_a').hom.app M ≫ (upperStarFactor A e_c).hom.app ((z)^*[A].obj M) := by
  subst e_b e_c e_a
  simp only [upperStarFactor, upperStarCongr, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.id_comp]
  rw [upperStarComp_hom_app_comp_upperStarComp_hom_app]
  simp only [upperStarCongr, eqToIso.hom, eqToHom_refl, NatTrans.id_app, Category.id_comp]

/-- Factorisations through equal morphisms give the same isomorphism. -/
lemma upperStarFactor_hom_app_comp_congr {a : P'' ⟶ Y} {g : Y' ⟶ Y} {c₁ c₂ : P'' ⟶ Y'}
    {t'' : P'' ⟶ Y''} {g' : Y'' ⟶ Y'} (p : c₁ = c₂) (e₁ : c₁ ≫ g = a) (e₂ : c₂ ≫ g = a)
    (f₁ : t'' ≫ g' = c₁) (f₂ : t'' ≫ g' = c₂) (M : Sheaf (ProEt.topology Y) A) :
    (upperStarFactor A e₁).hom.app M ≫ (upperStarFactor A f₁).hom.app ((g)^*[A].obj M) =
      (upperStarFactor A e₂).hom.app M ≫ (upperStarFactor A f₂).hom.app ((g)^*[A].obj M) := by
  subst p
  have : e₁ = e₂ := rfl
  have : f₁ = f₂ := rfl
  subst_vars
  rfl

/-- The pasting law for the isomorphisms `b^* ⋙ a^* ≅ d^* ⋙ c^*` attached to commutative
squares: the isomorphisms of two squares `τ ≫ t = t' ≫ g` and `τ' ≫ t' = t'' ≫ g'` paste to the
isomorphism of the composite square `(τ' ≫ τ) ≫ t = t'' ≫ (g' ≫ g)`. -/
lemma upperStarCompIso_hom_app_paste {τ : P' ⟶ P} {τ' : P'' ⟶ P'} {t : P ⟶ Y} {t' : P' ⟶ Y'}
    {t'' : P'' ⟶ Y''} {g : Y' ⟶ Y} {g' : Y'' ⟶ Y'}
    (h : τ ≫ t = t' ≫ g) (h' : τ' ≫ t' = t'' ≫ g') (h'' : (τ' ≫ τ) ≫ t = t'' ≫ (g' ≫ g))
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarComp A τ' τ).hom.app ((t)^*[A].obj M) ≫
        (τ')^*[A].map ((upperStarCompIso A h).hom.app M) ≫
        (upperStarCompIso A h').hom.app ((g)^*[A].obj M) =
      (upperStarCompIso A h'').hom.app M ≫ (t'')^*[A].map ((upperStarComp A g' g).hom.app M) := by
  have ea : (τ' ≫ t') ≫ g = (τ' ≫ τ) ≫ t := by simp only [Category.assoc, h]
  have ea' : (t'' ≫ g') ≫ g = (τ' ≫ τ) ≫ t := by simp only [Category.assoc, h'']
  have e₁ := upperStarFactor_hom_app_assoc A (rfl : τ ≫ t = τ ≫ t)
    (Category.assoc τ' τ t).symm (rfl : τ' ≫ τ = τ' ≫ τ) (rfl : (τ' ≫ τ) ≫ t = (τ' ≫ τ) ≫ t) M
  have e₂ := upperStarFactor_hom_app_assoc A h.symm (Category.assoc τ' τ t).symm
    (rfl : τ' ≫ t' = τ' ≫ t') ea M
  have e₃ := upperStarFactor_hom_app_assoc A (rfl : g' ≫ g = g' ≫ g) h''.symm
    (rfl : t'' ≫ g' = t'' ≫ g') ea' M
  have e₄ := upperStarFactor_hom_app_comp_congr A h' ea ea' h'.symm rfl M
  rw [upperStarCompIso_eq_upperStarFactor A h rfl h.symm,
    upperStarCompIso_eq_upperStarFactor A h' rfl h'.symm,
    upperStarCompIso_eq_upperStarFactor A h'' rfl h''.symm,
    ← upperStarFactor_rfl A τ' τ, ← upperStarFactor_rfl A g' g,
    ← cancel_epi ((upperStarFactor A (rfl : (τ' ≫ τ) ≫ t = (τ' ≫ τ) ≫ t)).hom.app M)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [reassoc_of% e₁.symm]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% e₂, e₃]
  simp only [Iso.hom_inv_id_app_assoc]
  exact e₄

end Paste


section Factor

variable {X Y Z : Scheme.{u}}

/-- The composition isomorphism `b_* ⋙ c_* ≅ a_*` of pushforwards along a factorisation
`b ≫ c = a`. -/
noncomputable def lowerStarFactor {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X} (e : b ≫ c = a) :
    (b)_*[A] ⋙ (c)_*[A] ≅ (a)_*[A] :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) b c a e.symm).symm) A
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Z)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarFactor_hom_app_hom_app {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X} (e : b ≫ c = a)
    (G : Sheaf (ProEt.topology Z) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarFactor A e).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp b c a e.symm).hom.app V.unop).op := by
  simp only [lowerStarFactor, Functor.sheafPushforwardContinuousComp']
  exact Category.id_comp _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarFactor_inv_app_hom_app {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X} (e : b ≫ c = a)
    (G : Sheaf (ProEt.topology Z) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarFactor A e).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp b c a e.symm).inv.app V.unop).op := by
  simp only [lowerStarFactor, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism followed by a congruence is a factorisation isomorphism. -/
lemma lowerStarComp_trans_lowerStarCongr {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X}
    (e : b ≫ c = a) : lowerStarComp A b c ≪≫ lowerStarCongr A e = lowerStarFactor A e := by
  subst e
  rw [lowerStarCongr_rfl, Iso.trans_refl]
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option backward.isDefEq.respectTransparency.types false in
lemma lowerStarId_hom_app_hom_app (G : Sheaf (ProEt.topology X) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).hom.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op := by
  simp [lowerStarId]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option backward.isDefEq.respectTransparency.types false in
lemma lowerStarId_inv_app_hom_app (G : Sheaf (ProEt.topology X) A) (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V.unop).op := by
  simp [lowerStarId]

/-- The unit `M ⟶ f_* i_* M` of pushforwards along morphisms with `i ≫ f = 𝟙`. -/
noncomputable def lowerStarUnit {i : X ⟶ Y} {f : Y ⟶ X} (h : i ≫ f = 𝟙 X) :
    𝟭 (Sheaf (ProEt.topology X) A) ⟶ (i)_*[A] ⋙ (f)_*[A] :=
  (lowerStarFactor A h ≪≫ lowerStarId A X).inv

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The units of pushforwards along inverse morphisms are compatible with composition. -/
lemma lowerStarUnit_app_comp_map_lowerStarFactor_inv {W : Scheme.{u}} {a : X ⟶ Y} {ai : Y ⟶ X}
    {b : Y ⟶ W} {bi : W ⟶ Y} {ab : X ⟶ W} {abi : W ⟶ X} (ha : ai ≫ a = 𝟙 Y)
    (hb : bi ≫ b = 𝟙 W) (hab : abi ≫ ab = 𝟙 W) (e₁ : a ≫ b = ab) (e₂ : bi ≫ ai = abi)
    (M : Sheaf (ProEt.topology W) A) :
    (lowerStarUnit A hab).app M ≫ (ab)_*[A].map ((lowerStarFactor A e₂).inv.app M) =
      (lowerStarUnit A hb).app M ≫ (b)_*[A].map ((lowerStarUnit A ha).app ((bi)_*[A].obj M)) ≫
        (lowerStarFactor A e₁).hom.app _ := by
  ext V
  simp only [lowerStarUnit, Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarFactor_hom_app_hom_app,
    lowerStarFactor_inv_app_hom_app, lowerStarId_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId]


omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The units of the pushforwards along inverse automorphisms `e_U` of `U` and `e_X` of `X`
are compatible with the pushforward along `j : U ⟶ X` when `j ≫ e_X = e_U ≫ j`. -/
lemma lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor_hom_app {U X : Scheme.{u}}
    (j : U ⟶ X) (eU : U ≅ U) (eX : X ≅ X) (e : j ≫ eX.hom = eU.hom ≫ j)
    (e' : j ≫ eX.inv = eU.inv ≫ j) (M : Sheaf (ProEt.topology U) A) :
    (j)_*[A].map ((lowerStarUnit A eU.inv_hom_id).app M) ≫
        (lowerStarFactor A (rfl : eU.hom ≫ j = eU.hom ≫ j)).hom.app ((eU.inv)_*[A].obj M) =
      (lowerStarUnit A eX.inv_hom_id).app ((j)_*[A].obj M) ≫
        (eX.hom)_*[A].map ((lowerStarFactor A e').hom.app M ≫
          (lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M) ≫
        (lowerStarFactor A e).hom.app ((eU.inv)_*[A].obj M) := by
  ext V
  simp only [lowerStarUnit, Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarFactor_hom_app_hom_app,
    lowerStarFactor_inv_app_hom_app, lowerStarId_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId,
      pullback.condition_assoc]

end Factor


section IsoTrans

variable {P X Y Z W : Scheme.{u}}

/-- The adjoint transpose of the identification `e^* ≅ (e⁻¹)_*` is the unit of the
pushforwards along `e⁻¹` and `e`. -/
lemma upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv (e : X ≅ Y)
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarLowerStarAdjunction A e.hom).unit.app M ≫
        (e.hom)_*[A].map ((upperStarIsoLowerStarInv A e).hom.app M) =
      (lowerStarUnit A e.inv_hom_id).app M := by
  rw [upperStarIsoLowerStarInv, Adjunction.unit_leftAdjointUniq_hom_app, lowerStarUnit,
    ← lowerStarComp_trans_lowerStarCongr, Iso.trans_assoc]
  rfl

/-- The adjoint transpose of a factorisation isomorphism of pullbacks is the corresponding
factorisation isomorphism of pushforwards, applied to the composite of the units. -/
lemma upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor {a : P ⟶ Y} {b : P ⟶ Z}
    {c : Z ⟶ Y} (e : b ≫ c = a) (M : Sheaf (ProEt.topology Y) A) :
    (upperStarLowerStarAdjunction A a).unit.app M ≫
        (a)_*[A].map ((upperStarFactor A e).hom.app M) =
      (upperStarLowerStarAdjunction A c).unit.app M ≫
        (c)_*[A].map ((upperStarLowerStarAdjunction A b).unit.app ((c)^*[A].obj M)) ≫
        (lowerStarFactor A e).hom.app ((b)^*[A].obj ((c)^*[A].obj M)) := by
  subst e
  have h := unit_conjugateEquiv ((upperStarLowerStarAdjunction A c).comp
    (upperStarLowerStarAdjunction A b)) (upperStarLowerStarAdjunction A (b ≫ c))
    (upperStarComp A b c).hom M
  rw [conjugateEquiv_upperStarComp_hom, Adjunction.comp_unit_app] at h
  rw [upperStarFactor_rfl, ← h, ← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl,
    Iso.trans_refl, Category.assoc]
  rfl

/-- The identifications `e^* ≅ (e⁻¹)_*` are compatible with composition of isomorphisms. -/
lemma upperStarIsoLowerStarInv_hom_app_trans (e₁ : X ≅ Y) (e₂ : Y ≅ W) (E : X ≅ W)
    (hE : e₁.hom ≫ e₂.hom = E.hom) (hEi : e₂.inv ≫ e₁.inv = E.inv)
    (M : Sheaf (ProEt.topology W) A) :
    (upperStarIsoLowerStarInv A E).hom.app M ≫ (lowerStarFactor A hEi).inv.app M =
      (upperStarFactor A hE).hom.app M ≫
        (e₁.hom)^*[A].map ((upperStarIsoLowerStarInv A e₂).hom.app M) ≫
        (upperStarIsoLowerStarInv A e₁).hom.app ((e₂.inv)_*[A].obj M) := by
  apply ((upperStarLowerStarAdjunction A E.hom).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor,
    lowerStarUnit_app_comp_map_lowerStarFactor_inv A e₁.inv_hom_id e₂.inv_hom_id E.inv_hom_id hE
      hEi]
  have n₁ := (lowerStarFactor A hE).hom.naturality
    ((e₁.hom)^*[A].map ((upperStarIsoLowerStarInv A e₂).hom.app M) ≫
      (upperStarIsoLowerStarInv A e₁).hom.app ((e₂.inv)_*[A].obj M))
  have n₂ := (upperStarLowerStarAdjunction A e₁.hom).unit_naturality
    ((upperStarIsoLowerStarInv A e₂).hom.app M)
  simp only [Functor.comp_map] at n₁
  rw [← Functor.map_comp (E.hom)_*[A], ← n₁, ← Functor.map_comp_assoc,
    Functor.map_comp (e₁.hom)_*[A], reassoc_of% n₂,
    upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv, Functor.map_comp,
    Category.assoc,
    reassoc_of% upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv]


/-- The counit of `j^* ⊣ j_*` is compatible with the identifications `e^* ≅ (e⁻¹)_*` for
automorphisms `e_U` of `U` and `e_X` of `X` with `j ≫ e_X = e_U ≫ j`: the two ways of going from
`(e_U ≫ j)^* j_* M` to `(e_U⁻¹)_* M` agree, the second one through
`(e_X⁻¹)_* j_* ≅ j_* (e_U⁻¹)_*`. -/
lemma upperStarComp_hom_app_comp_map_counit_comp_upperStarIsoLowerStarInv {U X : Scheme.{u}}
    (j : U ⟶ X) (eU : U ≅ U) (eX : X ≅ X) (e : j ≫ eX.hom = eU.hom ≫ j)
    (e' : j ≫ eX.inv = eU.inv ≫ j) (M : Sheaf (ProEt.topology U) A) :
    (upperStarComp A eU.hom j).hom.app ((j)_*[A].obj M) ≫
        (eU.hom)^*[A].map ((upperStarLowerStarAdjunction A j).counit.app M) ≫
        (upperStarIsoLowerStarInv A eU).hom.app M =
      (upperStarFactor A e).hom.app ((j)_*[A].obj M) ≫
        (j)^*[A].map ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M) ≫
          (lowerStarFactor A e').hom.app M ≫
          (lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M) ≫
        (upperStarLowerStarAdjunction A j).counit.app ((eU.inv)_*[A].obj M) := by
  have h₁ := upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor A
    (rfl : eU.hom ≫ j = eU.hom ≫ j) ((j)_*[A].obj M)
  rw [upperStarFactor_rfl] at h₁
  have h₂ := upperStarLowerStarAdjunction_unit_app_comp_map_upperStarFactor A e
    ((j)_*[A].obj M)
  have n₁ := (lowerStarFactor A (rfl : eU.hom ≫ j = eU.hom ≫ j)).hom.naturality
    ((eU.hom)^*[A].map ((upperStarLowerStarAdjunction A j).counit.app M) ≫
      (upperStarIsoLowerStarInv A eU).hom.app M)
  have n₂ := (lowerStarFactor A e).hom.naturality
    ((j)^*[A].map ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M) ≫
      (lowerStarFactor A e').hom.app M ≫
        (lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M) ≫
      (upperStarLowerStarAdjunction A j).counit.app ((eU.inv)_*[A].obj M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp,
    Category.assoc] at n₁ n₂
  have u₁ := congrArg (j)_*[A].map
    ((upperStarLowerStarAdjunction A eU.hom).unit_naturality
      ((upperStarLowerStarAdjunction A j).counit.app M))
  have i₁ := congrArg (j)_*[A].map
    (upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv A eU M)
  have t₁ := (upperStarLowerStarAdjunction A j).right_triangle_components M
  have t₂ := congrArg (eX.hom)_*[A].map
    ((upperStarLowerStarAdjunction A j).right_triangle_components ((eU.inv)_*[A].obj M))
  have w₁ := congrArg (eX.hom)_*[A].map ((upperStarLowerStarAdjunction A j).unit_naturality
    ((upperStarIsoLowerStarInv A eX).hom.app ((j)_*[A].obj M)))
  have w₂ := congrArg (eX.hom)_*[A].map ((upperStarLowerStarAdjunction A j).unit_naturality
    ((lowerStarFactor A e').hom.app M))
  have w₃ := congrArg (eX.hom)_*[A].map ((upperStarLowerStarAdjunction A j).unit_naturality
    ((lowerStarFactor A (rfl : eU.inv ≫ j = eU.inv ≫ j)).inv.app M))
  have i₂ := upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv A eX
    ((j)_*[A].obj M)
  have P := lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor_hom_app A j eU eX e e' M
  simp only [Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc]
    at u₁ i₁ t₂ w₁ w₂ w₃ P
  apply ((upperStarLowerStarAdjunction A (eU.hom ≫ j)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← n₁, ← n₂, reassoc_of% u₁, reassoc_of% i₁,
    reassoc_of% t₁, reassoc_of% w₁, reassoc_of% w₂, reassoc_of% w₃, reassoc_of% t₂,
    reassoc_of% i₂]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact P
end IsoTrans


section Misc

variable {X Y Z : Scheme.{u}}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarCongr_hom_app_comp_lowerStarComp_inv_app {a : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X}
    (h : a = b ≫ c) (M : Sheaf (ProEt.topology Z) A) :
    (lowerStarCongr A h).hom.app M ≫ (lowerStarComp A b c).inv.app M =
      (lowerStarFactor A h.symm).inv.app M := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl, Iso.trans_refl]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Pushing forward along `i = 𝟙` and then along `f` is pushing forward along `f`. -/
lemma lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_comp_map_lowerStarId {i : Z ⟶ Z}
    {f a : Z ⟶ Y} (h₀ : i = 𝟙 Z) (h₁ : a = i ≫ f) (h : a = f)
    (M : Sheaf (ProEt.topology Z) A) :
    (lowerStarCongr A h₁).hom.app M ≫ (lowerStarComp A i f).inv.app M ≫
        (f)_*[A].map ((lowerStarCongr A h₀).hom.app M ≫ (lowerStarId A Z).hom.app M) =
      (lowerStarCongr A h).hom.app M := by
  subst h₀ h₁
  ext V
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, lowerStarComp_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStarId_hom_app_hom_app, ← Functor.map_comp, ← op_comp]
  refine (congrArg M.obj.map ?_).trans (M.obj.map_id _)
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId] <;> rfl

/-- The identifications `e^* ≅ (e⁻¹)_*` along equal isomorphisms. -/
lemma upperStarIsoLowerStarInv_hom_app_congr {e e' : X ≅ Y} (p : e = e')
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarIsoLowerStarInv A e).hom.app M ≫
        (lowerStarCongr A (congrArg Iso.inv p)).hom.app M =
      (upperStarCongr A (congrArg Iso.hom p)).hom.app M ≫
        (upperStarIsoLowerStarInv A e').hom.app M := by
  subst p
  simp [upperStarCongr]

variable {P : Scheme.{u}}

/-- A factorisation isomorphism followed by a congruence in the first factor. -/
lemma upperStarFactor_hom_app_comp_upperStarCongr_hom_app {a : P ⟶ Y} {b b' : P ⟶ Z}
    {c : Z ⟶ Y} (e : b ≫ c = a) (p : b = b') (e' : b' ≫ c = a)
    (M : Sheaf (ProEt.topology Y) A) :
    (upperStarFactor A e).hom.app M ≫ (upperStarCongr A p).hom.app ((c)^*[A].obj M) =
      (upperStarFactor A e').hom.app M := by
  subst p
  have : e = e' := rfl
  subst this
  simp [upperStarCongr]

end Misc


section Congr

variable {P Q R : Scheme.{u}}

/-- The congruence isomorphisms of the pullbacks compose. -/
lemma upperStarCongr_trans {g g' g'' : P ⟶ Q} (h : g = g') (h' : g' = g'') :
    upperStarCongr A h ≪≫ upperStarCongr A h' = upperStarCongr A (h.trans h') := by
  subst h h'
  simp [upperStarCongr]

/-- The composition isomorphism of the pullbacks is natural in the first morphism. -/
lemma upperStarCongr_hom_app_comp_upperStarComp_hom_app {x y : P ⟶ Q} (p : x = y) (g : Q ⟶ R)
    (M : Sheaf (ProEt.topology R) A) :
    (upperStarCongr A (congrArg (· ≫ g) p)).hom.app M ≫ (upperStarComp A y g).hom.app M =
      (upperStarComp A x g).hom.app M ≫ (upperStarCongr A p).hom.app ((g)^*[A].obj M) := by
  subst p
  simp [upperStarCongr]

/-- The composition isomorphism of the pullbacks is natural in the second morphism. -/
lemma upperStarCongr_hom_app_comp_upperStarComp_hom_app' (g : P ⟶ Q) {x y : Q ⟶ R} (p : x = y)
    (M : Sheaf (ProEt.topology R) A) :
    (upperStarCongr A (congrArg (g ≫ ·) p)).hom.app M ≫ (upperStarComp A g y).hom.app M =
      (upperStarComp A g x).hom.app M ≫ (g)^*[A].map ((upperStarCongr A p).hom.app M) := by
  subst p
  simp [upperStarCongr]

end Congr

section UnitLaws

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
lemma _root_.CategoryTheory.MorphismProperty.Over.pullbackCongr_hom_app_eq {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (h' : g = f) (V : Y.ProEt) :
    (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h).hom.app V =
      (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) h').inv.app V := by
  subst h
  simp [MorphismProperty.Over.pullbackCongr_refl]

set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_id_right_hom_app (t : X ⟶ Y) (M : Sheaf (Scheme.ProEt.topology X) A) :
    (lowerStarComp A t (𝟙 Y)).hom.app M = (lowerStarId A Y).hom.app ((t)_*[A].obj M) ≫
      (lowerStarCongr A (Category.comp_id t).symm).hom.app M := by
  ext V
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStar_obj_obj_map', lowerStarId_hom_app_hom_app]
  rw [MorphismProperty.Over.pullbackComp_id_right t (t ≫ 𝟙 Y) rfl]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
    MorphismProperty.Over.pullbackCongr_hom_app_eq _ (Category.comp_id t).symm]
  exact (congrArg M.obj.map op_comp).trans (M.obj.map_comp _ _)


omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The right unit law for the composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_id_right (t : X ⟶ Y) :
    lowerStarComp A t (𝟙 Y) = Functor.isoWhiskerLeft (t)_*[A] (lowerStarId A Y) ≪≫
      (t)_*[A].rightUnitor ≪≫ (lowerStarCongr A (Category.comp_id t)).symm := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp only [lowerStarComp_id_right_hom_app, Functor.comp_obj, lowerStarCongr_rfl, Iso.refl_symm,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.refl_hom, NatTrans.comp_app, Functor.id_obj,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, NatTrans.id_app, Category.id_comp]
  rfl

/-- The right unit law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.lowerStarComp_id_right` by conjugation. -/
lemma upperStarComp_id_right (t : X ⟶ Y) :
    upperStarComp A t (𝟙 Y) = upperStarCongr A (Category.comp_id t) ≪≫
      (t)^*[A].leftUnitor.symm ≪≫ Functor.isoWhiskerRight (upperStarId A Y).symm (t)^*[A] := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A (𝟙 Y)).comp
    (upperStarLowerStarAdjunction A t)) (upperStarLowerStarAdjunction A (t ≫ 𝟙 Y))).injective ?_
  rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A t) _,
    conjugateIsoEquiv_trans _ (Adjunction.id.comp (upperStarLowerStarAdjunction A t)) _]
  rw [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_leftUnitor, lowerStarComp_id_right]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp


set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_id_left_hom_app (t : X ⟶ Y) (M : Sheaf (Scheme.ProEt.topology X) A) :
    (lowerStarComp A (𝟙 X) t).hom.app M = (t)_*[A].map ((lowerStarId A X).hom.app M) ≫
      (lowerStarCongr A (Category.id_comp t).symm).hom.app M := by
  ext V
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStar_map_hom_app', lowerStarId_hom_app_hom_app]
  rw [MorphismProperty.Over.pullbackComp_id_left t (𝟙 X ≫ t) rfl]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp,
    MorphismProperty.Over.pullbackCongr_hom_app_eq _ (Category.id_comp t).symm]
  exact (congrArg M.obj.map op_comp).trans (M.obj.map_comp _ _)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The left unit law for the composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_id_left (t : X ⟶ Y) :
    lowerStarComp A (𝟙 X) t = Functor.isoWhiskerRight (lowerStarId A X) (t)_*[A] ≪≫
      (t)_*[A].leftUnitor ≪≫ (lowerStarCongr A (Category.id_comp t)).symm := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp only [lowerStarComp_id_left_hom_app, Functor.comp_obj, lowerStarCongr_rfl, Iso.refl_symm,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app, Functor.id_obj,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, NatTrans.id_app, Category.id_comp]
  rfl

/-- The left unit law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.lowerStarComp_id_left` by conjugation. -/
lemma upperStarComp_id_left (t : X ⟶ Y) :
    upperStarComp A (𝟙 X) t = upperStarCongr A (Category.id_comp t) ≪≫
      (t)^*[A].rightUnitor.symm ≪≫ Functor.isoWhiskerLeft (t)^*[A] (upperStarId A X).symm := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A t).comp
    (upperStarLowerStarAdjunction A (𝟙 X))) (upperStarLowerStarAdjunction A (𝟙 X ≫ t))).injective ?_
  rw [conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A t) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A t).comp Adjunction.id) _]
  rw [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarId,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_rightUnitor, lowerStarComp_id_left]
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp

end UnitLaws

end AlgebraicGeometry.ProEtale
```

### WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Triple
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!

# Lower shriek along a localization of small pro-étale sites

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

Let `f : V ⟶ U` be a weakly étale morphism. Composition with `f` induces the localization
functor `MorphismProperty.Over.map ⊤ h : V.ProEt ⥤ U.ProEt` between the small pro-étale
sites, and this file defines the lower shriek functor `j_{f!}` on `A`-valued pro-étale
sheaves along this localization functor, together with its right adjoint, the restriction
functor `j_f^*`.

When `f` is moreover an open immersion (in particular a monomorphism), `j_{f!}` is the
*extension by zero* functor. It is then exact and fully faithful; fully faithfulness is
`AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek` in
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful`, proved from
the adjoint triple `ProEtale.localizationAdjunctionTriple` below.

## Main definitions

- `AlgebraicGeometry.ProEtale.localizationLowerShriek`: the lower shriek `j_{f!}`.
- `AlgebraicGeometry.ProEtale.localizationRestriction`: the restriction `j_f^*`.
- `AlgebraicGeometry.ProEtale.localizationLowerShriekAdjunction`: the adjunction
  `j_{f!} ⊣ j_f^*`.
- `AlgebraicGeometry.ProEtale.localizationRestrictionLowerStarAdjunction`: the adjunction
  `j_f^* ⊣ f_*`, completing the triple `j_{f!} ⊣ j_f^* ⊣ f_*`.
- `AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`: for `f` weakly étale the
  pullback `f^*` of `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` is computed
  by restriction, both being left adjoint to `f_*`.
- `AlgebraicGeometry.ProEtale.localizationLowerShriekUpperStarAdjunction`: the adjunction
  `j_{f!} ⊣ f^*`.
- `AlgebraicGeometry.ProEtale.localizationAdjunctionTriple`: the triple
  `j_{f!} ⊣ j_f^* ⊣ f_*` as a `CategoryTheory.Adjunction.Triple`. Via
  `CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit` this is what makes `j_{f!}`
  fully faithful as soon as `f_*` is.
- `AlgebraicGeometry.ProEtale.localizationLowerShriekPresheaf` and
  `AlgebraicGeometry.ProEtale.localizationLowerShriekPresheafAdjunction`: the presheaf-level
  Kan extension `j_{f,!}^{pre}` and its adjunction with restriction.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriek`: the lower shriek `j_!` along an
  open immersion `j`, with scoped notation `(j)_!open[A]`, whose `open` keeps it apart from
  `AlgebraicGeometry.ProEtale.lowerShriek` along a morphism admitting a compactification.
- `AlgebraicGeometry.ProEtale.openImmersionRestriction`: the restriction `j^*` along an open
  immersion `j`, given objectwise by `(j^* G)(T → U) = G(T → U → X)`.
- `AlgebraicGeometry.ProEtale.upperStarIsoOpenImmersionRestriction`: the pullback `j^*` of
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` is computed by restriction.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction`: the adjunction
  `j_! ⊣ j^*` between the lower shriek and the pullback `ProEtale.upperStar`.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek` and
  `AlgebraicGeometry.ProEtale.preservesFiniteColimits_openImmersionLowerShriek`: the lower
  shriek `j_!` is exact when `j` is an open immersion. The left exactness of the
  presheaf-level lower shriek is
  `AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overMap` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.

## Implementation notes

- `j_{f!}` is defined as the left Kan extension along `(MorphismProperty.Over.map ⊤ h).op`
  on presheaves followed by sheafification; this holds definitionally, see
  `localizationLowerShriek_eq`. For a monomorphism `f` — in particular for an open
  immersion — no Kan extension existence hypothesis is needed: the indexing comma
  categories are either empty or admit a terminal object, so both the existence and the
  left exactness of the presheaf-level left Kan extension are provided by the instances of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`.
- `j_f^*` restricts along the localization functor, so it requires `WeaklyEtale f`, but it
  needs neither Kan extensions nor sheafification. The pullback `ProEtale.upperStar` of
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` is defined for an arbitrary
  morphism at the cost of both; the two agree for a weakly étale `f`, by
  `upperStarIsoLocalizationRestriction`.
- The continuity and cocontinuity of the localization functor are
  `AlgebraicGeometry.Scheme.ProEt.isContinuous_overMap` and
  `AlgebraicGeometry.Scheme.ProEt.isCocontinuous_overMap` of
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`.
-/

@[expose] public section

universe w u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : WeaklyEtale f)

section LowerShriek

variable [Mono f]

/-- The lower shriek `j_{f!}` along a weakly étale `f : V ⟶ U`: left Kan extension on
presheaves followed by sheafification, left adjoint to
`ProEtale.localizationRestriction`. -/
noncomputable def ProEtale.localizationLowerShriek :
    Sheaf (Scheme.ProEt.topology V) A ⥤ Sheaf (Scheme.ProEt.topology U) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h) A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

end LowerShriek

section Restriction

/-- The restriction functor `j_f^*` along a weakly étale `f : V ⟶ U`, given objectwise by
`(j_f^* G)(T → V) = G(T → V → U)`. The continuity of the localization functor is
`AlgebraicGeometry.Scheme.ProEt.isContinuous_overMap`. -/
def ProEtale.localizationRestriction :
    Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology V) A :=
  (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `j_f^* G` over `T → V` are the sections of `G` over `T → V → U`. -/
lemma ProEtale.localizationRestriction_obj_val_obj (G : Sheaf (Scheme.ProEt.topology U) A)
    (b : V.ProEt) :
    ((ProEtale.localizationRestriction A f h).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `j_f^*` acts on morphisms by whiskering along `(MorphismProperty.Over.map ⊤ h).op`. -/
lemma ProEtale.localizationRestriction_map_hom_app
    {G G' : Sheaf (Scheme.ProEt.topology U) A} (φ : G ⟶ G') (b : V.ProEt) :
    (((ProEtale.localizationRestriction A f h).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.map ⊤ h).obj b)) :=
  rfl

section Adjunction

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ j_f^*`. -/
noncomputable def ProEtale.localizationLowerShriekAdjunction :
    ProEtale.localizationLowerShriek A f h ⊣ ProEtale.localizationRestriction A f h :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    A (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

instance : (ProEtale.localizationLowerShriek A f h).IsLeftAdjoint :=
  (ProEtale.localizationLowerShriekAdjunction A f h).isLeftAdjoint

instance : (ProEtale.localizationRestriction A f h).IsRightAdjoint :=
  (ProEtale.localizationLowerShriekAdjunction A f h).isRightAdjoint

/-- The lower shriek agrees with mathlib's abstract left adjoint
`(MorphismProperty.Over.map ⊤ h).sheafPullback` of the restriction functor. -/
noncomputable def ProEtale.localizationLowerShriekIsoSheafPullback :
    (MorphismProperty.Over.map ⊤ h).sheafPullback A
        (Scheme.ProEt.topology V) (Scheme.ProEt.topology U) ≅
      ProEtale.localizationLowerShriek A f h :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (MorphismProperty.Over.map ⊤ h) A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

end Adjunction

/-! ### Comparison with the pullback `f^*` -/

section UpperStar

open ProEtale

/-- Restriction along the localization functor is left adjoint to the pushforward `f_*`:
this is the right half of the triple `j_{f!} ⊣ j_f^* ⊣ f_*`. It is induced by the
adjunction `MorphismProperty.Over.mapPullbackAdj` between the two site functors, and in
particular requires neither Kan extensions nor sheafification. -/
noncomputable def ProEtale.localizationRestrictionLowerStarAdjunction :
    ProEtale.localizationRestriction A f h ⊣ (f)_*[A] :=
  (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f h
    _root_.trivial).sheafPushforwardContinuous
      (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

/-- For a weakly étale `f`, the pullback `f^*` is computed by restriction along the
localization functor: both are left adjoint to `f_*`. In particular `f^*` needs no
sheafification in this case, and its sections are given by
`ProEtale.localizationRestriction_obj_val_obj`. -/
noncomputable def ProEtale.upperStarIsoLocalizationRestriction :
    (f)^*[A] ≅ ProEtale.localizationRestriction A f h :=
  (ProEtale.upperStarLowerStarAdjunction A f).leftAdjointUniq
    (ProEtale.localizationRestrictionLowerStarAdjunction A f h)

variable [Mono f]

/-- The adjunction `j_{f!} ⊣ f^*` between the lower shriek and the pullback, obtained from
`localizationLowerShriekAdjunction` by transporting along
`upperStarIsoLocalizationRestriction`. -/
noncomputable def ProEtale.localizationLowerShriekUpperStarAdjunction :
    ProEtale.localizationLowerShriek A f h ⊣ (f)^*[A] :=
  (ProEtale.localizationLowerShriekAdjunction A f h).ofNatIsoRight
    (ProEtale.upperStarIsoLocalizationRestriction A f h).symm

/-- The adjoint triple `j_{f!} ⊣ j_f^* ⊣ f_*` on pro-étale sheaves, bundling
`localizationLowerShriekAdjunction` and `localizationRestrictionLowerStarAdjunction`. -/
noncomputable def ProEtale.localizationAdjunctionTriple :
    Adjunction.Triple (ProEtale.localizationLowerShriek A f h)
      (ProEtale.localizationRestriction A f h) (f)_*[A] where
  adj₁ := ProEtale.localizationLowerShriekAdjunction A f h
  adj₂ := ProEtale.localizationRestrictionLowerStarAdjunction A f h

end UpperStar

end Restriction

/-! ### The presheaf-level lower shriek -/

section Presheaf

variable [Mono f]

/-- The presheaf-level lower shriek `j_{f,!}^{pre}`: left Kan extension along
`(MorphismProperty.Over.map ⊤ h).op`. -/
noncomputable def ProEtale.localizationLowerShriekPresheaf :
    (V.ProEtᵒᵖ ⥤ A) ⥤ (U.ProEtᵒᵖ ⥤ A) :=
  (MorphismProperty.Over.map ⊤ h).op.lan

/-- The presheaf-level adjunction between `j_{f,!}^{pre}` and restriction. -/
noncomputable def ProEtale.localizationLowerShriekPresheafAdjunction :
    ProEtale.localizationLowerShriekPresheaf A f h ⊣
      (Functor.whiskeringLeft V.ProEtᵒᵖ U.ProEtᵒᵖ A).obj (MorphismProperty.Over.map ⊤ h).op :=
  (MorphismProperty.Over.map ⊤ h).op.lanAdjunction A

/-- The lower shriek is definitionally the left Kan extension on presheaves followed by
sheafification. -/
lemma ProEtale.localizationLowerShriek_eq :
    ProEtale.localizationLowerShriek A f h =
      sheafToPresheaf (Scheme.ProEt.topology V) A ⋙
        ProEtale.localizationLowerShriekPresheaf A f h ⋙
          presheafToSheaf (Scheme.ProEt.topology U) A :=
  rfl

end Presheaf

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open ProEtale

/-- The restriction `j^*` along an open immersion `j : U ⟶ X` on sheaves for the small
pro-étale sites, given objectwise by `(j^* G)(T → U) = G(T → U → X)`. In contrast to
`ProEtale.upperStar` it requires neither Kan extensions nor sheafification. -/
def ProEtale.openImmersionRestriction :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology U) A :=
  ProEtale.localizationRestriction A j inferInstance

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `j^* G` over `T → U` are the sections of `G` over `T → U → X`. -/
lemma ProEtale.openImmersionRestriction_obj_val_obj (G : Sheaf (Scheme.ProEt.topology X) A)
    (b : U.ProEt) :
    ((ProEtale.openImmersionRestriction A j).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.map ⊤
        (inferInstance : @WeaklyEtale _ _ j)).obj b)) :=
  rfl

/-- Restriction along an open immersion is left adjoint to the pushforward `j_*`: this is
the right half of the triple `j_! ⊣ j^* ⊣ j_*`. -/
noncomputable def ProEtale.openImmersionRestrictionLowerStarAdjunction :
    ProEtale.openImmersionRestriction A j ⊣ (j)_*[A] :=
  ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance

/-- The counit of the adjunction `j^* ⊣ j_*` along an open immersion `j` is an
isomorphism: the restriction of a pushforward along an open immersion is the original
sheaf. This holds since `j` is a monomorphism, so the unit of the site-level adjunction
`MorphismProperty.Over.mapPullbackAdj` is an isomorphism. -/
instance ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit :
    IsIso (ProEtale.openImmersionRestrictionLowerStarAdjunction A j).counit :=
  Adjunction.isIso_sheafPushforwardContinuous_counit A
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial)
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The restriction `j^*` along an open immersion on pro-étale sheaves is additive. -/
instance ProEtale.openImmersionRestriction_additive :
    (ProEtale.openImmersionRestriction A j).Additive where

namespace ProEtale

/-- The lower shriek `j_!` along an open immersion `j : U ⟶ X` on sheaves for the small
pro-étale sites. -/
noncomputable def openImmersionLowerShriek :
    Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A :=
  ProEtale.localizationLowerShriek A j inferInstance

@[inherit_doc openImmersionLowerShriek]
scoped notation "(" j ")_!open[" A "]" =>
  openImmersionLowerShriek A j

end ProEtale

/-- The adjunction `j_! ⊣ j^*` between the extension by zero and the restriction along an
open immersion. -/
noncomputable def ProEtale.openImmersionLowerShriekAdjunction :
    (j)_!open[A] ⊣ ProEtale.openImmersionRestriction A j :=
  ProEtale.localizationLowerShriekAdjunction A j inferInstance

instance : (j)_!open[A].IsLeftAdjoint :=
  (ProEtale.openImmersionLowerShriekAdjunction A j).isLeftAdjoint

instance : (ProEtale.openImmersionRestriction A j).IsRightAdjoint :=
  (ProEtale.openImmersionLowerShriekAdjunction A j).isRightAdjoint

/-- The extension by zero `j_!` along an open immersion on pro-étale sheaves with values in
a preadditive category is additive, being left adjoint to the additive restriction `j^*`. -/
instance ProEtale.openImmersionLowerShriek_additive : (j)_!open[A].Additive :=
  (ProEtale.openImmersionLowerShriekAdjunction A j).left_adjoint_additive

/-- The extension by zero `j_!` along an open immersion on pro-étale sheaves with values in
an abelian category is exact. This is the left exactness half.

`j_!` is the presheaf-level left Kan extension followed by sheafification, and both factors
are left exact: the first by
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_op_lan_overMap`, the second by
the left exactness of sheafification, which is the content of `HasSheafify` beyond the
`HasWeakSheafify` needed to define `j_!`; both are provided for the Grothendieck abelian
coefficient category `A`, the second by the sorried instance of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. -/
instance ProEtale.preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (j)_!open[A] := by
  have heq : (j)_!open[A] =
      sheafToPresheaf (Scheme.ProEt.topology U) A ⋙
        ProEtale.localizationLowerShriekPresheaf A j inferInstance ⋙
          presheafToSheaf (Scheme.ProEt.topology X) A :=
    rfl
  have hlan : PreservesFiniteLimits
      (ProEtale.localizationLowerShriekPresheaf A j inferInstance) :=
    ProEtale.preservesFiniteLimits_op_lan_overMap A inferInstance
  rw [heq]
  exact comp_preservesFiniteLimits _ _

/-- Together with `ProEtale.preservesFiniteLimits_openImmersionLowerShriek` this
makes `j_!` exact. -/
example : PreservesFiniteColimits (j)_!open[A] :=
  inferInstance

/-- For an open immersion `j`, the pullback `j^*` of
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` is computed by restriction along
the localization functor: both are left adjoint to `j_*`. In particular its sections are
given by `ProEtale.openImmersionRestriction_obj_val_obj`. -/
noncomputable def ProEtale.upperStarIsoOpenImmersionRestriction :
    (j)^*[A] ≅ ProEtale.openImmersionRestriction A j :=
  ProEtale.upperStarIsoLocalizationRestriction A j inferInstance

/-- The adjunction `j_! ⊣ j^*` between the lower shriek along an open immersion and the
pullback `ProEtale.upperStar`. -/
noncomputable def ProEtale.openImmersionLowerShriekUpperStarAdjunction :
    (j)_!open[A] ⊣ (j)^*[A] :=
  ProEtale.localizationLowerShriekUpperStarAdjunction A j inferInstance

/-- The adjoint triple `j_! ⊣ j^* ⊣ j_*` on small pro-étale sites along an open
immersion. -/
noncomputable def ProEtale.openImmersionAdjunctionTriple :
    Adjunction.Triple (j)_!open[A] (ProEtale.openImmersionRestriction A j) (j)_*[A] :=
  ProEtale.localizationAdjunctionTriple A j inferInstance

end OpenImmersion

end AlgebraicGeometry
```

### WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

/-!

# Lower shriek along a morphism admitting a compactification

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.Defs`.

For a morphism `f : X ⟶ Y` together with a compactification `X ⟶[i] Z ⟶[g] Y` (`i` an
open immersion, `g` proper), the lower shriek on small pro-étale sites is the composition
`f_! := i_! ⋙ g_*` of the extension by zero along `i` with the pushforward
`AlgebraicGeometry.ProEtale.lowerStar` along `g`.

## Main definitions

- `AlgebraicGeometry.ProEtale.Compactification.lowerShriek`: the lower shriek `i_! ⋙ g_*`
  associated with a compactification `X ⟶[i] Z ⟶[g] Y` of `f`.
- `AlgebraicGeometry.ProEtale.lowerShriek`: the lower shriek `f_!` of a morphism `f`
  satisfying `HasCompactification f`, *definitionally* equal to the composition associated
  with the chosen compactification `HasCompactification.compactification f`, see
  `ProEtale.lowerShriek_eq`.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_lowerShriek`: the lower shriek `f_!`
  with values in an abelian category is left exact. This one needs sheafification to be
  *exact*, not merely to exist.

## Implementation notes

- The pushforward `g_*` of `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` is
  defined along the base change functor, which exists for an *arbitrary* morphism `g` — in
  contrast to the localization functor `MorphismProperty.Over.map ⊤ h` of
  `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`, which requires
  `WeaklyEtale g`. This is essential for compactifications, whose structure morphism is
  proper and in general is not weakly étale.
- The open immersion of a compactification is weakly étale, being étale, so the extension
  by zero along it is available; the Kan extension it needs exists because an open immersion
  is a monomorphism. Hence `f_!` carries no hypotheses beyond the standing assumptions
  on `A`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}}

namespace ProEtale

namespace Compactification

variable {f : X ⟶ Y} (c : Compactification f)

/-- The lower shriek associated with a compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
extension by zero `i_!` followed by the pushforward `g_*`. -/
noncomputable def lowerShriek :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology Y) A :=
  (c.i)_!open[A] ⋙ (c.g)_*[A]

end Compactification

variable (f : X ⟶ Y) [HasCompactification f]

/-- The lower shriek `f_!` along a morphism `f : X ⟶ Y` admitting a compactification, on
sheaves for the small pro-étale sites: the composition `i_! ⋙ g_*` associated with the
chosen compactification `HasCompactification.compactification f`. -/
noncomputable def lowerShriek :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology Y) A :=
  Compactification.lowerShriek A (HasCompactification.compactification f)

/-- The lower shriek `f_!` on pro-étale sheaves is the extension by zero along the open
immersion of the chosen compactification followed by the pushforward `ProEtale.lowerStar`
along its proper structure morphism. -/
lemma lowerShriek_eq :
    lowerShriek A f =
      ((HasCompactification.compactification f).i)_!open[A] ⋙
        ((HasCompactification.compactification f).g)_*[A] :=
  rfl

/-- The lower shriek `f_!` on pro-étale sheaves with values in a preadditive category is
additive, being the composition of the extension by zero along the open immersion of the
chosen compactification with the pushforward along its proper structure morphism. -/
instance lowerShriek_additive : (lowerShriek A f).Additive := by
  rw [lowerShriek_eq]
  infer_instance

/-- The lower shriek `f_!` on pro-étale sheaves with values in an abelian category is left
exact, being the composition of the exact extension by zero along the open immersion of
the chosen compactification with the left exact pushforward along its proper structure
morphism.

The extension by zero is sheafification composed with a left Kan extension, so left
exactness of sheafification is needed here; see
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_openImmersionLowerShriek`. This is why
`HasSheafify` appears in addition to the `HasWeakSheafify` that defines `f_!`. -/
instance preservesFiniteLimits_lowerShriek :
    PreservesFiniteLimits (lowerShriek A f) := by
  rw [lowerShriek_eq]
  exact comp_preservesFiniteLimits _ _

end ProEtale

--TODO: the composition isomorphism : `(fg)_! ≅ f_! g_!`

--TODO: invarience with choice of compcatification

end AlgebraicGeometry
```

### WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!

# Coherence of the composition isomorphisms of `g^*` and `g_*` on pro-étale sheaves

The composition isomorphisms `ProEtale.lowerStarComp : f_* ⋙ g_* ≅ (f ≫ g)_*` and
`ProEtale.upperStarComp : (f ≫ g)^* ≅ g^* ⋙ f^*` of pushforwards and pullbacks on pro-étale
sheaves with values in a Grothendieck abelian category `A`, and the identity isomorphisms
`ProEtale.lowerStarId` and `ProEtale.upperStarId`, satisfy the coherences of a pseudofunctor.
This file proves those that compare pullbacks along morphisms over a fixed base.

## The morphisms `η`

Let `k_X : X ⟶ W` and `k_Y : Y ⟶ W` be morphisms of schemes and `f : X ⟶ Y` with
`f ≫ k_Y = k_X`. For a sheaf `F` on `W_proét`, the composition isomorphism of the pullbacks gives
`f^* k_Y^* F ≅ (f ≫ k_Y)^* F = k_X^* F`, and its mate under `f^* ⊣ f_*` is a morphism
```
η_f(F) : k_Y^* F ⟶ f_* k_X^* F,
```
the unit of `f^* ⊣ f_*` followed by `f_*` of that isomorphism. For the coefficient rings pulled
back from the pro-étale site of a point, `k_X` is the structure morphism `X ⟶ Spec ℤ`, and
`η_f(F)` is the canonical coefficient morphism `Λ_Y ⟶ f_* Λ_X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

The morphisms `η` are compatible with identities and compositions
(`ProEtale.unitCompUpperStarComp_id` and `ProEtale.unitCompUpperStarComp_comp`):
```
η_{𝟙 X}(F) = (𝟙 X)_* ≅ 𝟭 at k_X^* F,
η_{f ≫ g}(F) = η_g(F) ≫ g_* η_f(F) ≫ (g_* f_* ≅ (f ≫ g)_*) at k_X^* F.
```

## Proof

Under the adjunction `k^* ⊣ k_*`, the morphism `η_f(F)` corresponds to the unit of
`k_X^* ⊣ k_X_*` followed by the composition isomorphism `k_X_* ≅ k_Y_* ∘ f_*` of the
pushforwards (`ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`), the composition
isomorphism of the pullbacks being by definition conjugate to that of the pushforwards. The two
compatibilities are thus reduced to the associativity and the left unit law of the composition
isomorphisms of the pushforwards (`ProEtale.lowerStarComp_assoc` and
`ProEtale.lowerStarComp_id_left`). These hold on sections, the pushforwards being restrictions
along the base change functors of the pro-étale sites: both sides are the restriction maps along
the canonical isomorphisms between iterated fibre products, which agree, maps into a fibre
product being determined by their projections.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-! ### Base change along the identity -/

section Site

/-- The structure morphism of the base change of `V` along `k` is the second projection. -/
lemma ProEt.overPullback_obj_hom {X Y : Scheme.{u}} (k : X ⟶ Y) (V : Y.ProEt) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).obj V).hom = pullback.snd V.hom k :=
  rfl

/-- The identification of base change along the identity with the identity is the first
projection. -/
lemma ProEt.overPullbackId_hom_app_left (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).hom.app W).left = pullback.fst W.hom (𝟙 X) := by
  simp [ProEt.overPullbackId, conjugateEquiv_apply_app]

/-- The inverse of `ProEt.overPullbackId` is a section of the first projection. -/
@[reassoc (attr := simp)]
lemma ProEt.overPullbackId_inv_app_left_fst (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left ≫ pullback.fst W.hom (𝟙 X) = 𝟙 _ := by
  rw [← ProEt.overPullbackId_hom_app_left, ← MorphismProperty.Comma.comp_left,
    Iso.inv_hom_id_app]
  rfl

/-- The inverse of `ProEt.overPullbackId` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma ProEt.overPullbackId_inv_app_left_snd (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left ≫ pullback.snd W.hom (𝟙 X) = W.hom :=
  MorphismProperty.Over.w ((ProEt.overPullbackId X).inv.app W)

/-- The inverse of `ProEt.overPullbackId`, explicitly. -/
lemma ProEt.overPullbackId_inv_app_left (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left =
      pullback.lift (𝟙 W.left) W.hom (by simp) := by
  apply pullback.hom_ext
  · rw [ProEt.overPullbackId_inv_app_left_fst, pullback.lift_fst]
    rfl
  · rw [ProEt.overPullbackId_inv_app_left_snd, pullback.lift_snd]

end Site

/-! ### The composition isomorphisms of the pushforwards -/

section LowerStar

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of `eqToHom` between pushforwards along equal morphisms are the restriction
maps along the base change isomorphisms `MorphismProperty.Over.pullbackCongr`. -/
lemma ProEtale.eqToHom_lowerStar_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (e : g = g')
    (p : (g)_*[A] = (g')_*[A]) (G : Sheaf (Scheme.ProEt.topology Z) A) (V : Y.ProEt) :
    ((eqToHom p).app G).hom.app (op V) =
      G.obj.map ((MorphismProperty.Over.pullbackCongr e.symm).hom.app V).op := by
  cases e
  rw [eqToHom_refl, NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  erw [← G.obj.map_id]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [Functor.op_obj, Functor.id_obj, Functor.const_obj_obj, unop_id,
      MorphismProperty.Comma.id_hom, Comma.id_left, Category.id_comp, Quiver.Hom.unop_op,
      MorphismProperty.Over.pullbackCongr_hom_app_left_fst]
  · rw [MorphismProperty.Over.pullbackCongr_refl]
    simp

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` are the restriction
maps along the base change isomorphisms `MorphismProperty.Over.pullbackComp`. -/
lemma ProEtale.coefficient_lowerStarComp_hom_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R)
    (G : Sheaf (Scheme.ProEt.topology T) A) (V : R.ProEt) :
    ((lowerStarComp A h₁ h₂).hom.app G).hom.app (op V) =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V).op := by
  simp [lowerStarComp]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphisms of pushforwards are associative, up to `eqToHom` along
`(h₁ ≫ h₂) ≫ h₃ = h₁ ≫ h₂ ≫ h₃`: on sections, both sides are the restriction maps along the
canonical isomorphisms of iterated fibre products. -/
lemma ProEtale.lowerStarComp_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}} (h₁ : X₀ ⟶ X₁) (h₂ : X₁ ⟶ X₂)
    (h₃ : X₂ ⟶ X₃) :
    Functor.whiskerLeft (h₁)_*[A] (lowerStarComp A h₂ h₃).hom ≫
        (lowerStarComp A h₁ (h₂ ≫ h₃)).hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (lowerStarComp A h₁ h₂).hom (h₃)_*[A] ≫
        (lowerStarComp A (h₁ ≫ h₂) h₃).hom ≫ eqToHom (by rw [Category.assoc]) := by
  ext G : 2
  apply Sheaf.hom_ext
  ext ⟨V⟩
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    eqToHom_lowerStar_app_hom_app A (Category.assoc h₁ h₂ h₃), lowerStar_map_hom_app,
    coefficient_lowerStarComp_hom_app_hom_app]
  erw [show ∀ x, ((h₁)_*[A].obj G).obj.map x =
    G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h₁).map x.unop).op from fun _ ↦ rfl]
  simp only [← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  dsimp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk, MorphismProperty.Comma.mk]
  apply pullback.hom_ext <;> (try apply pullback.hom_ext) <;> (try apply pullback.hom_ext) <;>
    simp [pullback.condition, MorphismProperty.Over.pullbackCongr]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism `(𝟙 X)_* ⋙ k_* ≅ (𝟙 X ≫ k)_*` is induced by the identity
isomorphism `(𝟙 X)_* ≅ 𝟭`, up to `eqToHom` along `𝟙 X ≫ k = k`. -/
lemma ProEtale.lowerStarComp_id_left {X Y : Scheme.{u}} (k : X ⟶ Y) :
    (lowerStarComp A (𝟙 X) k).hom =
      Functor.whiskerRight (lowerStarId A X).hom (k)_*[A] ≫ (Functor.leftUnitor _).hom ≫
        eqToHom (by rw [Category.id_comp]) := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    lowerStarCongr, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv] using congrArg Iso.hom (ProEtale.legacy_lowerStarComp_id_left A k)

end LowerStar

/-! ### The morphisms `η` -/

section Eta

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Composition with the identity transformation of a functor between sheaf categories, stated
with the instances as they occur after `eqToHom_refl`. -/
lemma ProEtale.id_app_comp {Y₁ Y₂ : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology Y₁) A ⥤
    Sheaf (Scheme.ProEt.topology Y₂) A) (G : Sheaf (Scheme.ProEt.topology Y₁) A)
    {M : Sheaf (Scheme.ProEt.topology Y₂) A} (h : F.obj G ⟶ M) : NatTrans.app (𝟙 F) G ≫ h = h :=
  Category.id_comp h

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Composition with the identity transformation of a functor between sheaf categories, stated
with the instances as they occur after `eqToHom_refl`. -/
lemma ProEtale.comp_id_app {Y₁ Y₂ : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology Y₁) A ⥤
    Sheaf (Scheme.ProEt.topology Y₂) A) (G : Sheaf (Scheme.ProEt.topology Y₁) A)
    {M : Sheaf (Scheme.ProEt.topology Y₂) A} (h : M ⟶ F.obj G) : h ≫ NatTrans.app (𝟙 F) G = h :=
  Category.comp_id h

/-- For a functor `G` with values in sheaves on `W_proét`, the components of the isomorphism
`(G ⋙ k_Y^*) ⋙ f^* ≅ G ⋙ k_X^*` induced by the composition isomorphism of the pullbacks and
`f ≫ k_Y = k_X` are those of the composition isomorphism followed by `eqToHom`. -/
lemma ProEtale.associator_isoWhiskerLeft_upperStarComp_hom_app {W X Y : Scheme.{u}}
    {D : Type*} [Category* D] (G : D ⥤ Sheaf (Scheme.ProEt.topology W) A) (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (h : f ≫ kY = kX) (c : D) :
    (Functor.associator G (kY)^*[A] (f)^*[A] ≪≫ Functor.isoWhiskerLeft G
        ((upperStarComp A f kY).symm ≪≫ eqToIso (congrArg (upperStar A) h))).hom.app c =
      (upperStarComp A f kY).inv.app (G.obj c) ≫
        (eqToHom (congrArg (upperStar A) h)).app (G.obj c) := by
  simp

/-- The composition isomorphism of the pullbacks is conjugate to that of the pushforwards. -/
lemma ProEtale.coefficient_conjugateEquiv_upperStarComp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    conjugateEquiv (upperStarLowerStarAdjunction A (f ≫ g))
        ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f))
        (upperStarComp A f g).inv = (lowerStarComp A f g).inv := by
  simp [upperStarComp]

/-- Let `f : X ⟶ Y`, `k_X : X ⟶ W`, `k_Y : Y ⟶ W` with `f ≫ k_Y = k_X`. The morphism
`η_f(F) : k_Y^* F ⟶ f_* k_X^* F` adjoint to the composition isomorphism `f^* k_Y^* F ≅ k_X^* F`
corresponds, under the adjunction `k_Y^* ⊣ k_Y_*`, to the unit of `k_X^* ⊣ k_X_*` followed by the
composition isomorphism `k_X_* ≅ k_Y_* ∘ f_*` of the pushforwards. -/
@[reassoc]
lemma ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX)
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A kY).unit.app F ≫
        (kY)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
          (f)_*[A].map ((upperStarComp A f kY).inv.app F ≫
            (eqToHom (congrArg (upperStar A) hf)).app F)) =
      (upperStarLowerStarAdjunction A kX).unit.app F ≫
        (eqToHom (congrArg (lowerStar A) hf.symm)).app _ ≫
          (lowerStarComp A f kY).inv.app ((kX)^*[A].obj F) := by
  subst hf
  have := unit_conjugateEquiv (upperStarLowerStarAdjunction A (f ≫ kY))
    ((upperStarLowerStarAdjunction A kY).comp (upperStarLowerStarAdjunction A f))
    (upperStarComp A f kY).inv F
  rw [coefficient_conjugateEquiv_upperStarComp_inv, Adjunction.comp_unit_app] at this
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id, Functor.map_comp]
  erw [Category.id_comp, this]
  simp only [Functor.comp_map, Category.assoc]

/-- The special case `k_X = f ≫ k_Y` of
`ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`. -/
@[reassoc]
lemma ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp' {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kY : Y ⟶ W) (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A kY).unit.app F ≫
        (kY)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
          (f)_*[A].map ((upperStarComp A f kY).inv.app F)) =
      (upperStarLowerStarAdjunction A (f ≫ kY)).unit.app F ≫
        (lowerStarComp A f kY).inv.app ((f ≫ kY)^*[A].obj F) := by
  simpa only [eqToHom_refl, id_app_comp, comp_id_app] using
    unit_comp_lowerStar_map_unit_comp_upperStarComp A f (f ≫ kY) kY rfl F

/-- **Compatibility of `η` with composition.** For `f : X ⟶ Y` and `g : Y ⟶ Z` over `W`, with
structure morphisms `k_X`, `k_Y`, `k_Z`, the morphism `η_{f ≫ g}(F) : k_Z^* F ⟶ (f ≫ g)_* k_X^* F`
adjoint to the composition isomorphism of the pullbacks is `η_g(F)`, followed by `g_* η_f(F)`,
followed by the composition isomorphism `g_* f_* ≅ (f ≫ g)_*`. -/
lemma ProEtale.unitCompUpperStarComp_comp {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (kX : X ⟶ W) (kY : Y ⟶ W) (kZ : Z ⟶ W) (hf : f ≫ kY = kX) (hg : g ≫ kZ = kY)
    (hfg : (f ≫ g) ≫ kZ = kX) (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A (f ≫ g)).unit.app ((kZ)^*[A].obj F) ≫
        (f ≫ g)_*[A].map ((upperStarComp A (f ≫ g) kZ).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hfg)).app F) =
      ((upperStarLowerStarAdjunction A g).unit.app ((kZ)^*[A].obj F) ≫
        (g)_*[A].map ((upperStarComp A g kZ).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hg)).app F)) ≫
      (g)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
        (f)_*[A].map ((upperStarComp A f kY).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hf)).app F)) ≫
      (lowerStarComp A f g).hom.app ((kX)^*[A].obj F) := by
  subst hf hg
  apply ((upperStarLowerStarAdjunction A kZ).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp A (f ≫ g) _ kZ hfg]
  rw [Functor.map_comp (kZ)_*[A],
    unit_comp_lowerStar_map_unit_comp_upperStarComp_assoc A g _ kZ rfl]
  simp only [eqToHom_refl, id_app_comp, comp_id_app]
  rw [Functor.map_comp (kZ)_*[A]]
  erw [← (lowerStarComp A g kZ).inv.naturality_assoc]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp'_assoc]
  congr 1
  have h := congr_app (lowerStarComp_assoc A f g kZ) ((f ≫ g ≫ kZ)^*[A].obj F)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, eqToHom_refl, comp_id_app] at h
  erw [Category.id_comp] at h
  rw [← cancel_mono ((lowerStarComp A (f ≫ g) kZ).hom.app _)]
  simp only [Category.assoc, ← h, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  rfl

/-- **Compatibility of `η` with identities.** The morphism
`η_{𝟙 X}(F) : k_X^* F ⟶ (𝟙 X)_* k_X^* F` adjoint to the composition isomorphism of the pullbacks
along `𝟙 X` and `k_X` is the identification `k_X^* F ≅ (𝟙 X)_* k_X^* F`. -/
lemma ProEtale.unitCompUpperStarComp_id {W X : Scheme.{u}} (kX : X ⟶ W) (h : 𝟙 X ≫ kX = kX)
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A (𝟙 X)).unit.app ((kX)^*[A].obj F) ≫
        (𝟙 X)_*[A].map ((upperStarComp A (𝟙 X) kX).inv.app F ≫
          (eqToHom (congrArg (upperStar A) h)).app F) =
      (lowerStarId A X).inv.app ((kX)^*[A].obj F) := by
  apply ((upperStarLowerStarAdjunction A kX).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp A (𝟙 X) kX kX h]
  congr 1
  have h' := congr_app (lowerStarComp_id_left A kX) ((kX)^*[A].obj F)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h'
  rw [← cancel_mono ((lowerStarComp A (𝟙 X) kX).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h']
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp

end Eta

end AlgebraicGeometry
```

## New

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-! Compatibility re-export of the canonical finite-coefficient implementation. -/
```

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-! Compatibility re-export of the canonical finite-coefficient implementation. -/
```

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-! Compatibility re-export of the canonical finite-coefficient implementation. -/
```

### WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-! Compatibility re-export of the canonical finite-coefficient implementation. -/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
```

### WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-! Compatibility re-export of the canonical finite-coefficient implementation. -/
```

### WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs

```lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs

/-! Compatibility re-export of the canonical finite-coefficient implementation. -/
```

### WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

```lean
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!

# Coherence of the composition isomorphisms of `g^*` and `g_*` on pro-étale sheaves

The composition isomorphisms `ProEtale.lowerStarComp : f_* ⋙ g_* ≅ (f ≫ g)_*` and
`ProEtale.upperStarComp : (f ≫ g)^* ≅ g^* ⋙ f^*` of pushforwards and pullbacks on pro-étale
sheaves with values in a Grothendieck abelian category `A`, and the identity isomorphisms
`ProEtale.lowerStarId` and `ProEtale.upperStarId`, satisfy the coherences of a pseudofunctor.
This file proves those that compare pullbacks along morphisms over a fixed base.

## The morphisms `η`

Let `k_X : X ⟶ W` and `k_Y : Y ⟶ W` be morphisms of schemes and `f : X ⟶ Y` with
`f ≫ k_Y = k_X`. For a sheaf `F` on `W_proét`, the composition isomorphism of the pullbacks gives
`f^* k_Y^* F ≅ (f ≫ k_Y)^* F = k_X^* F`, and its mate under `f^* ⊣ f_*` is a morphism
```
η_f(F) : k_Y^* F ⟶ f_* k_X^* F,
```
the unit of `f^* ⊣ f_*` followed by `f_*` of that isomorphism. For the coefficient rings pulled
back from the pro-étale site of a point, `k_X` is the structure morphism `X ⟶ Spec ℤ`, and
`η_f(F)` is the canonical coefficient morphism `Λ_Y ⟶ f_* Λ_X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.

The morphisms `η` are compatible with identities and compositions
(`ProEtale.unitCompUpperStarComp_id` and `ProEtale.unitCompUpperStarComp_comp`):
```
η_{𝟙 X}(F) = (𝟙 X)_* ≅ 𝟭 at k_X^* F,
η_{f ≫ g}(F) = η_g(F) ≫ g_* η_f(F) ≫ (g_* f_* ≅ (f ≫ g)_*) at k_X^* F.
```

## Proof

Under the adjunction `k^* ⊣ k_*`, the morphism `η_f(F)` corresponds to the unit of
`k_X^* ⊣ k_X_*` followed by the composition isomorphism `k_X_* ≅ k_Y_* ∘ f_*` of the
pushforwards (`ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`), the composition
isomorphism of the pullbacks being by definition conjugate to that of the pushforwards. The two
compatibilities are thus reduced to the associativity and the left unit law of the composition
isomorphisms of the pushforwards (`ProEtale.coefficient_lowerStarComp_assoc` and
`ProEtale.coefficient_lowerStarComp_id_left`). These hold on sections, the pushforwards
being restrictions
along the base change functors of the pro-étale sites: both sides are the restriction maps along
the canonical isomorphisms between iterated fibre products, which agree, maps into a fibre
product being determined by their projections.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-! ### Base change along the identity -/

section Site

/-- The structure morphism of the base change of `V` along `k` is the second projection. -/
lemma ProEt.overPullback_obj_hom {X Y : Scheme.{u}} (k : X ⟶ Y) (V : Y.ProEt) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).obj V).hom = pullback.snd V.hom k :=
  rfl

/-- The identification of base change along the identity with the identity is the first
projection. -/
lemma ProEt.overPullbackId_hom_app_left (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).hom.app W).left = pullback.fst W.hom (𝟙 X) := by
  simp [ProEt.overPullbackId, conjugateEquiv_apply_app]

/-- The inverse of `ProEt.overPullbackId` is a section of the first projection. -/
@[reassoc (attr := simp)]
lemma ProEt.overPullbackId_inv_app_left_fst (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left ≫ pullback.fst W.hom (𝟙 X) = 𝟙 _ := by
  rw [← ProEt.overPullbackId_hom_app_left, ← MorphismProperty.Comma.comp_left,
    Iso.inv_hom_id_app]
  rfl

/-- The inverse of `ProEt.overPullbackId` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma ProEt.overPullbackId_inv_app_left_snd (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left ≫ pullback.snd W.hom (𝟙 X) = W.hom :=
  MorphismProperty.Over.w ((ProEt.overPullbackId X).inv.app W)

/-- The inverse of `ProEt.overPullbackId`, explicitly. -/
lemma ProEt.overPullbackId_inv_app_left (X : Scheme.{u}) (W : X.ProEt) :
    ((ProEt.overPullbackId X).inv.app W).left =
      pullback.lift (𝟙 W.left) W.hom (by simp) := by
  apply pullback.hom_ext
  · rw [ProEt.overPullbackId_inv_app_left_fst, pullback.lift_fst]
    rfl
  · rw [ProEt.overPullbackId_inv_app_left_snd, pullback.lift_snd]

end Site

/-! ### The composition isomorphisms of the pushforwards -/

section LowerStar

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of `eqToHom` between pushforwards along equal morphisms are the restriction
maps along the base change isomorphisms `MorphismProperty.Over.pullbackCongr`. -/
lemma ProEtale.eqToHom_lowerStar_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (e : g = g')
    (p : (g)_*[A] = (g')_*[A]) (G : Sheaf (Scheme.ProEt.topology Z) A) (V : Y.ProEt) :
    ((eqToHom p).app G).hom.app (op V) =
      G.obj.map ((MorphismProperty.Over.pullbackCongr e.symm).hom.app V).op := by
  cases e
  rw [eqToHom_refl, NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  erw [← G.obj.map_id]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [Functor.op_obj, Functor.id_obj, Functor.const_obj_obj, unop_id,
      MorphismProperty.Comma.id_hom, Comma.id_left, Category.id_comp, Quiver.Hom.unop_op,
      MorphismProperty.Over.pullbackCongr_hom_app_left_fst]
  · rw [MorphismProperty.Over.pullbackCongr_refl]
    simp

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` are the restriction
maps along the base change isomorphisms `MorphismProperty.Over.pullbackComp`. -/
lemma ProEtale.coefficient_lowerStarComp_hom_app_hom_app {R S T : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R)
    (G : Sheaf (Scheme.ProEt.topology T) A) (V : R.ProEt) :
    ((lowerStarComp A h₁ h₂).hom.app G).hom.app (op V) =
      G.obj.map ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V).op := by
  simp [lowerStarComp]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphisms of pushforwards are associative, up to `eqToHom` along
`(h₁ ≫ h₂) ≫ h₃ = h₁ ≫ h₂ ≫ h₃`: on sections, both sides are the restriction maps along the
canonical isomorphisms of iterated fibre products. -/
lemma ProEtale.coefficient_lowerStarComp_assoc {X₀ X₁ X₂ X₃ : Scheme.{u}}
    (h₁ : X₀ ⟶ X₁) (h₂ : X₁ ⟶ X₂)
    (h₃ : X₂ ⟶ X₃) :
    Functor.whiskerLeft (h₁)_*[A] (lowerStarComp A h₂ h₃).hom ≫
        (lowerStarComp A h₁ (h₂ ≫ h₃)).hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (lowerStarComp A h₁ h₂).hom (h₃)_*[A] ≫
        (lowerStarComp A (h₁ ≫ h₂) h₃).hom ≫ eqToHom (by rw [Category.assoc]) := by
  apply (cancel_epi (Functor.associator (h₁)_*[A] (h₂)_*[A] (h₃)_*[A]).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    lowerStarCongr, eqToIso.hom] using
      congrArg Iso.hom (ProEtale.legacy_lowerStarComp_assoc A h₁ h₂ h₃)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism `(𝟙 X)_* ⋙ k_* ≅ (𝟙 X ≫ k)_*` is induced by the identity
isomorphism `(𝟙 X)_* ≅ 𝟭`, up to `eqToHom` along `𝟙 X ≫ k = k`. -/
lemma ProEtale.coefficient_lowerStarComp_id_left {X Y : Scheme.{u}} (k : X ⟶ Y) :
    (lowerStarComp A (𝟙 X) k).hom =
      Functor.whiskerRight (lowerStarId A X).hom (k)_*[A] ≫ (Functor.leftUnitor _).hom ≫
        eqToHom (by rw [Category.id_comp]) := by
  simpa only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    lowerStarCongr, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv] using congrArg Iso.hom (ProEtale.legacy_lowerStarComp_id_left A k)

/-! Compatibility names retained for consumers of the original implementation. -/

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Compatibility name for the associativity law as an equality of isomorphisms. -/
theorem ProEtale.lowerStarComp_assoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f)_*[A].associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫ lowerStarComp A f (g ≫ h) =
      Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h ≪≫
        lowerStarCongr A (Category.assoc f g h) :=
  ProEtale.legacy_lowerStarComp_assoc A f g h

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Compatibility name for the left unit law as an equality of isomorphisms. -/
theorem ProEtale.lowerStarComp_id_left {X Y : Scheme.{u}} (t : X ⟶ Y) :
    lowerStarComp A (𝟙 X) t = Functor.isoWhiskerRight (lowerStarId A X) (t)_*[A] ≪≫
      (t)_*[A].leftUnitor ≪≫ (lowerStarCongr A (Category.id_comp t)).symm :=
  ProEtale.legacy_lowerStarComp_id_left A t

end LowerStar

/-! ### The morphisms `η` -/

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] ProEtale.upperStar ProEtale.upperStarLowerStarAdjunction

section Eta

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Composition with the identity transformation of a functor between sheaf categories, stated
with the instances as they occur after `eqToHom_refl`. -/
lemma ProEtale.id_app_comp {Y₁ Y₂ : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology Y₁) A ⥤
    Sheaf (Scheme.ProEt.topology Y₂) A) (G : Sheaf (Scheme.ProEt.topology Y₁) A)
    {M : Sheaf (Scheme.ProEt.topology Y₂) A} (h : F.obj G ⟶ M) : NatTrans.app (𝟙 F) G ≫ h = h :=
  Category.id_comp h

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Composition with the identity transformation of a functor between sheaf categories, stated
with the instances as they occur after `eqToHom_refl`. -/
lemma ProEtale.comp_id_app {Y₁ Y₂ : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology Y₁) A ⥤
    Sheaf (Scheme.ProEt.topology Y₂) A) (G : Sheaf (Scheme.ProEt.topology Y₁) A)
    {M : Sheaf (Scheme.ProEt.topology Y₂) A} (h : M ⟶ F.obj G) : h ≫ NatTrans.app (𝟙 F) G = h :=
  Category.comp_id h

/-- For a functor `G` with values in sheaves on `W_proét`, the components of the isomorphism
`(G ⋙ k_Y^*) ⋙ f^* ≅ G ⋙ k_X^*` induced by the composition isomorphism of the pullbacks and
`f ≫ k_Y = k_X` are those of the composition isomorphism followed by `eqToHom`. -/
lemma ProEtale.associator_isoWhiskerLeft_upperStarComp_hom_app {W X Y : Scheme.{u}}
    {D : Type*} [Category* D] (G : D ⥤ Sheaf (Scheme.ProEt.topology W) A) (f : X ⟶ Y)
    (kX : X ⟶ W) (kY : Y ⟶ W) (h : f ≫ kY = kX) (c : D) :
    (Functor.associator G (kY)^*[A] (f)^*[A] ≪≫ Functor.isoWhiskerLeft G
        ((upperStarComp A f kY).symm ≪≫ eqToIso (congrArg (upperStar A) h))).hom.app c =
      (upperStarComp A f kY).inv.app (G.obj c) ≫
        (eqToHom (congrArg (upperStar A) h)).app (G.obj c) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Category.id_comp, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, eqToIso.hom]

/-- The composition isomorphism of the pullbacks is conjugate to that of the pushforwards. -/
lemma ProEtale.coefficient_conjugateEquiv_upperStarComp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    conjugateEquiv (upperStarLowerStarAdjunction A (f ≫ g))
        ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f))
        (upperStarComp A f g).inv = (lowerStarComp A f g).inv := by
  simp [upperStarComp]

/-- Let `f : X ⟶ Y`, `k_X : X ⟶ W`, `k_Y : Y ⟶ W` with `f ≫ k_Y = k_X`. The morphism
`η_f(F) : k_Y^* F ⟶ f_* k_X^* F` adjoint to the composition isomorphism `f^* k_Y^* F ≅ k_X^* F`
corresponds, under the adjunction `k_Y^* ⊣ k_Y_*`, to the unit of `k_X^* ⊣ k_X_*` followed by the
composition isomorphism `k_X_* ≅ k_Y_* ∘ f_*` of the pushforwards. -/
@[reassoc]
lemma ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kX : X ⟶ W) (kY : Y ⟶ W) (hf : f ≫ kY = kX)
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A kY).unit.app F ≫
        (kY)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
          (f)_*[A].map ((upperStarComp A f kY).inv.app F ≫
            (eqToHom (congrArg (upperStar A) hf)).app F)) =
      (upperStarLowerStarAdjunction A kX).unit.app F ≫
        (eqToHom (congrArg (lowerStar A) hf.symm)).app _ ≫
          (lowerStarComp A f kY).inv.app ((kX)^*[A].obj F) := by
  subst hf
  have := unit_conjugateEquiv (upperStarLowerStarAdjunction A (f ≫ kY))
    ((upperStarLowerStarAdjunction A kY).comp (upperStarLowerStarAdjunction A f))
    (upperStarComp A f kY).inv F
  rw [coefficient_conjugateEquiv_upperStarComp_inv, Adjunction.comp_unit_app] at this
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id, Functor.map_comp]
  erw [Category.id_comp, this]
  simp only [Functor.comp_map, Category.assoc]

/-- The special case `k_X = f ≫ k_Y` of
`ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`. -/
@[reassoc]
lemma ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp' {W X Y : Scheme.{u}}
    (f : X ⟶ Y) (kY : Y ⟶ W) (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A kY).unit.app F ≫
        (kY)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
          (f)_*[A].map ((upperStarComp A f kY).inv.app F)) =
      (upperStarLowerStarAdjunction A (f ≫ kY)).unit.app F ≫
        (lowerStarComp A f kY).inv.app ((f ≫ kY)^*[A].obj F) := by
  simpa only [eqToHom_refl, id_app_comp, comp_id_app] using
    unit_comp_lowerStar_map_unit_comp_upperStarComp A f (f ≫ kY) kY rfl F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Compatibility of `η` with composition.** For `f : X ⟶ Y` and `g : Y ⟶ Z` over `W`, with
structure morphisms `k_X`, `k_Y`, `k_Z`, the morphism `η_{f ≫ g}(F) : k_Z^* F ⟶ (f ≫ g)_* k_X^* F`
adjoint to the composition isomorphism of the pullbacks is `η_g(F)`, followed by `g_* η_f(F)`,
followed by the composition isomorphism `g_* f_* ≅ (f ≫ g)_*`. -/
lemma ProEtale.unitCompUpperStarComp_comp {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (kX : X ⟶ W) (kY : Y ⟶ W) (kZ : Z ⟶ W) (hf : f ≫ kY = kX) (hg : g ≫ kZ = kY)
    (hfg : (f ≫ g) ≫ kZ = kX) (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A (f ≫ g)).unit.app ((kZ)^*[A].obj F) ≫
        (f ≫ g)_*[A].map ((upperStarComp A (f ≫ g) kZ).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hfg)).app F) =
      ((upperStarLowerStarAdjunction A g).unit.app ((kZ)^*[A].obj F) ≫
        (g)_*[A].map ((upperStarComp A g kZ).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hg)).app F)) ≫
      (g)_*[A].map ((upperStarLowerStarAdjunction A f).unit.app ((kY)^*[A].obj F) ≫
        (f)_*[A].map ((upperStarComp A f kY).inv.app F ≫
          (eqToHom (congrArg (upperStar A) hf)).app F)) ≫
      (lowerStarComp A f g).hom.app ((kX)^*[A].obj F) := by
  subst hf hg
  apply ((upperStarLowerStarAdjunction A kZ).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp A (f ≫ g) _ kZ hfg]
  rw [Functor.map_comp (kZ)_*[A],
    unit_comp_lowerStar_map_unit_comp_upperStarComp_assoc A g _ kZ rfl]
  simp only [eqToHom_refl, id_app_comp, comp_id_app]
  rw [Functor.map_comp (kZ)_*[A]]
  erw [← (lowerStarComp A g kZ).inv.naturality_assoc]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp'_assoc]
  congr 1
  have h := congr_app (coefficient_lowerStarComp_assoc A f g kZ) ((f ≫ g ≫ kZ)^*[A].obj F)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, eqToHom_refl, comp_id_app] at h
  erw [Category.id_comp] at h
  rw [← cancel_mono ((lowerStarComp A (f ≫ g) kZ).hom.app _)]
  simp only [Category.assoc, ← h, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  rfl

/-- **Compatibility of `η` with identities.** The morphism
`η_{𝟙 X}(F) : k_X^* F ⟶ (𝟙 X)_* k_X^* F` adjoint to the composition isomorphism of the pullbacks
along `𝟙 X` and `k_X` is the identification `k_X^* F ≅ (𝟙 X)_* k_X^* F`. -/
lemma ProEtale.unitCompUpperStarComp_id {W X : Scheme.{u}} (kX : X ⟶ W) (h : 𝟙 X ≫ kX = kX)
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStarLowerStarAdjunction A (𝟙 X)).unit.app ((kX)^*[A].obj F) ≫
        (𝟙 X)_*[A].map ((upperStarComp A (𝟙 X) kX).inv.app F ≫
          (eqToHom (congrArg (upperStar A) h)).app F) =
      (lowerStarId A X).inv.app ((kX)^*[A].obj F) := by
  apply ((upperStarLowerStarAdjunction A kX).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [unit_comp_lowerStar_map_unit_comp_upperStarComp A (𝟙 X) kX kX h]
  congr 1
  have h' := congr_app (coefficient_lowerStarComp_id_left A kX) ((kX)^*[A].obj F)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h'
  rw [← cancel_mono ((lowerStarComp A (𝟙 X) kX).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h']
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp

end Eta

end AlgebraicGeometry
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AdicClosedImmersionFiniteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AffineComparisonCechCocycleDescent | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AffineComparisonEtaleCechPresentation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AffineComparisonEtaleCoverPresentation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing | H4 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionLocalVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CartesianHigherImageAffineSectionVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawClassVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CartesianHigherImageGermVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CartesianHigherImageSingleRawClassVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CartesianRawClassChartData | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CartesianRawClassChartRepresentative | R2 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | B4 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.FieldExtensionDerivedDirectImageExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.GeometricFiberFinite | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.LerayBounded | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.LimitDerivedDirectImageExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.LimitHigherDirectImageExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ModificationExtensionZero | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonSections | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionByZeroAdjunction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteGeometricPoint | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCopowers | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCoproducts | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.RawDerivedClassAffineDescent | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.RawFixedDerivedComparisonNaturality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SmoothLimitDerivedDirectImageExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeff | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffData | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedConstructibleGenericLfp | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedConstructiblePiece | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteFreeDerivedHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteFreeHomContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteFreeHomEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteFreeInternalHomColimits | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteFreeTensorExact | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteModelImmersionRestriction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedInternalHomSections | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLocalPresentationPullback | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedLocallyClosedPiece | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | H3 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQbarLfpCoverComposition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedSurjectiveClosedEquivalence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.CondensedSurjectiveClosedLocalPresentation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | B2 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | E2 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralCoefficientTelescope | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralCoefficients | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralDerivedUnit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousIntegralScalarExact | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | H2 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | New constructive consumer introduced in this delivery. |
| Sheaf.Paper.FiniteDiscreteEtaleRealizationFull | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.FiniteDiscreteSchemeRing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.GeometricFieldProfiniteDenseSubsite | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | E4 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralReductionScalar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralReductionTriangulatedProperty | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralResidueComparisonInterface | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralResiduePerfect | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | D3 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ModuleObjectFreeGenerators | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.PointLanAffineEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.PointLanFiniteProducts | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ProEtalePointComponentsMaps | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ProEtaleSheafificationWcontractibleSections | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ProfinitePointPullback | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.Paper.ProfiniteTestObjectFunctor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.RingTheory.HenselianSeparablyGeneratedResidueSection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| TargetsCheck | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Composition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Abelian | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AbelianIrreducible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafTransport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Constructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenFunctions | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Extension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleCounit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleLisse | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobeniusMate | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionsHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Hom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.HomCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseExtensionByZero | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseGerm | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalkPointwise | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Module | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Ring | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.StalkEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.StalkIhomDual | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TensorPowSection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TrivialRepresentation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Truncation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UnitSection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UpperStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Comparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.AlgClosedField | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClopenIdempotent | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Comparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Constructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ExtPullback | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ExtPullbackHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ExternalProduct | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.FlatModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Hom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Localization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekProjection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerStarProjectionComparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriekProjection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Shift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Tensor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TensorResolution | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitudeResidue | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarCompCoherence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Comparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Derived | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.KFlat | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal.Vanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.Derived.WeilComplex | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence | unclaimed | Adapted here; existing public mathematical statements retained. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.GenericPoint | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.GeometricFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.KummerCover | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.Comparison | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs | unclaimed | Adapted here; existing public mathematical statements retained. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.BaseChange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Complement | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs | unclaimed | Adapted here; existing public mathematical statements retained. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Injective | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.LocalVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Mono | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Projection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Stalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.LowerShriek.Proper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | F3 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A2 | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Braided | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence | unclaimed | Adapted here; existing public mathematical statements retained. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.CounitStructure | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs | unclaimed | Adapted here; existing public mathematical statements retained. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Detection | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.FlatModuleCat | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Germ | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GermComp | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GermMonoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSectionsMonoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.InternalHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso | unclaimed | Adapted here; existing public mathematical statements retained. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.KFlat | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.LocalVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal | unclaimed | Adapted here; existing public mathematical statements retained. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.MonoidalIso | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Restriction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.TopologicalInvariance | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.Statement | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Category | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Constant | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Dual | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.DualIrreducible | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FiniteLength | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LisseDuality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LisseFiltration | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LisseLocus | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LocalFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Stalk | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkCharpoly | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkConstantSheaf | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkFrobenius | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkFunctor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkIso | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkMonoidal | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkPairing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkUpperStar | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.StalkUpperStarCharpoly | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TraceFunctionVanishing | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.Triangle | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.UpperStarComp | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.UpperStarExact | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged; uses the same definitions and statements, with compatibility aliases for old coherence names. |

All listed users retain their mathematical statements. No target signature changes. The defining data in the re-exported implementation is the same; the target meaning is unchanged. Consumer compilation is recorded in report.md.

## Status

landed 20261016T093727-L-2050954 2026-10-16 (merge of deliver/H2/Sheaf.Paper.FiniteDiscreteCoefficientExchange)
