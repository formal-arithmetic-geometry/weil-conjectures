/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!

# The pushforward `g_*` and the pullback `g^*` on small sites of schemes

Let `P` and `Q` be morphism properties of schemes. For an *arbitrary* morphism of schemes
`g : W ⟶ U`, base change induces the functor
`MorphismProperty.Over.pullback P ⊤ g : P.Over ⊤ U ⥤ P.Over ⊤ W` between the small sites,
and composition with it defines the pushforward `g_*` on `A`-valued sheaves for the small
`Q`-topologies. Its left adjoint `g^*` is the left Kan extension on presheaves followed by
sheafification.

## Main definitions

- `CategoryTheory.GrothendieckTopology.lowerStar`: the pushforward `g_*`, given by
  composition with the base change functor.
- `CategoryTheory.GrothendieckTopology.upperStar`: the pullback `g^*`, given by left Kan
  extension on presheaves followed by sheafification.
- `CategoryTheory.GrothendieckTopology.upperStarLowerStarAdjunction`: the adjunction
  `g^* ⊣ g_*`.
- `CategoryTheory.GrothendieckTopology.lowerStarComp` and
  `CategoryTheory.GrothendieckTopology.upperStarComp`: the composition isomorphisms
  `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`, the latter
  obtained from the former by uniqueness of left adjoints. Both take the composite
  `h₁ ≫ h₂` as an optional argument, in the same way as
  `CategoryTheory.MorphismProperty.Over.pullbackComp`.
- `CategoryTheory.GrothendieckTopology.lowerStarId` and
  `CategoryTheory.GrothendieckTopology.upperStarId`: the pushforward and the pullback
  along the identity are the identity functor.

## Main results

- `CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_lowerStar` and
  `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_lowerStar`: the pushforward
  `g_*` preserves every limit that exists in the coefficient category. This needs no
  hypothesis beyond the continuity of the base change functor, in particular it does not
  use the adjunction `g^* ⊣ g_*`.
- `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_upperStar`: the pullback `g^*`
  is left exact, provided sheafification is and the left Kan extension along the opposite
  of the base change functor is. In contrast to `g_*` this is not automatic; see
  `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` for the case of an
  étale morphism, where the Kan extension is precomposition with a right adjoint.
- `CategoryTheory.GrothendieckTopology.lowerStarComp_assoc`,
  `CategoryTheory.GrothendieckTopology.lowerStarComp_id_left` and
  `CategoryTheory.GrothendieckTopology.lowerStarComp_id_right`, together with their
  counterparts `upperStarComp_assoc`, `upperStarComp_id_left` and
  `upperStarComp_id_right`: `g ↦ g_*` and `g ↦ g^*` are pseudofunctors. The `upperStar`
  statements are transported from the `lowerStar` ones along the conjugation bijection
  `CategoryTheory.conjugateEquiv`, which is how `upperStarComp` is defined in the first
  place.

## Implementation notes

- The coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
  universe `u + 1`, one above the universe `u` of the base schemes, following the
  convention of the `SixFunctors` folder.
- Both functors are defined along the base change functor, which exists for an *arbitrary*
  morphism `g` — in contrast to the localization functor `MorphismProperty.Over.map ⊤ h`
  of `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs`, which requires `P g`.
  This is essential for compactifications, whose structure morphism is proper and in
  general does not satisfy `P`.
- The continuity of the base change functor along an arbitrary morphism is proved, for
  `Q ≤ P`, as `AlgebraicGeometry.Scheme.isContinuous_overPullback` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`. The left Kan extensions on
  presheaves and the sheafification entering the definitions are provided, for `Q ≤ P`, by
  the sorried results of the folder `WeilConjectures.CategoryTheory.GrothendieckAbelian`,
  under the multiplicativity-type assumptions on `P` and `Q` assumed throughout; all of
  them hold for `P = Q = @Etale`. The inequality `hQP : Q ≤ P` is an explicit argument of
  the definitions using continuity.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace GrothendieckTopology

variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
variable (hQP : Q ≤ P)

variable {W U : Scheme.{u}} (g : W ⟶ U)

/-- The pushforward `g_*` along `g : W ⟶ U`, given objectwise by
`(g_* G)(V → U) = G(V ×_U W → W)`. The continuity of the base change functor is
`AlgebraicGeometry.Scheme.isContinuous_overPullback`. -/
noncomputable def lowerStar :
    Sheaf (W.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (U.smallGrothendieckTopology Q (Q := P)) A :=
  have := isContinuous_overPullback P Q hQP g
  (MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The sections of `g_* G` over `V → U` are the sections of `G` over `V ×_U W → W`. -/
lemma lowerStar_obj_val_obj
    (G : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ U) :
    ((lowerStar A P Q hQP g).obj G).obj.obj (op b) =
      G.obj.obj (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- `g_*` acts on morphisms by whiskering along `(MorphismProperty.Over.pullback P ⊤ g).op`. -/
lemma lowerStar_map_hom_app
    {G G' : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A} (φ : G ⟶ G') (b : P.Over ⊤ U) :
    (((lowerStar A P Q hQP g).map φ).hom).app (op b) =
      φ.hom.app (op ((MorphismProperty.Over.pullback P ⊤ g).obj b)) :=
  rfl

/-- `g_*` preserves limits of any shape that exists in the coefficient category: it is
given by restriction along the base change functor, and limits of sheaves are computed
pointwise on the underlying presheaves. -/
instance preservesLimitsOfShape_lowerStar (E : Type*) [Category E] [HasLimitsOfShape E A] :
    PreservesLimitsOfShape E (lowerStar A P Q hQP g) :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (PreservesLimitsOfShape E
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

/-- `g_*` is left exact. Note that this does not use the adjunction `g^* ⊣ g_*`, which is
only available under the extra hypotheses of the section below. -/
instance preservesFiniteLimits_lowerStar :
    PreservesFiniteLimits (lowerStar A P Q hQP g) :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (PreservesFiniteLimits
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

section Adjunction

/-- The pullback `g^*` along `g : W ⟶ U`: left Kan extension on presheaves followed by
sheafification, left adjoint to `lowerStar`. The Kan extensions and the sheafification
are provided by the sorried instances of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. -/
noncomputable def upperStar :
    Sheaf (U.smallGrothendieckTopology Q (Q := P)) A ⥤
      Sheaf (W.smallGrothendieckTopology Q (Q := P)) A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

/-- The adjunction `g^* ⊣ g_*`. -/
noncomputable def upperStarLowerStarAdjunction :
    upperStar A P Q g ⊣ lowerStar A P Q hQP g :=
  have := isContinuous_overPullback P Q hQP g
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback P ⊤ g) A
    (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))

instance : (lowerStar A P Q hQP g).IsRightAdjoint :=
  (upperStarLowerStarAdjunction A P Q hQP g).isRightAdjoint

include hQP in
/-- `g^*` is a left adjoint. Not an instance, since its statement does not determine the
inequality `hQP : Q ≤ P` entering the adjunction `g^* ⊣ g_*`; for the small étale sites
the corresponding instance is registered in
`WeilConjectures.SixFunctors.UpperLowerStar.Etale`. -/
lemma isLeftAdjoint_upperStar : (upperStar A P Q g).IsLeftAdjoint :=
  (upperStarLowerStarAdjunction A P Q hQP g).isLeftAdjoint

/-- `g^*` is left exact as soon as the left Kan extension along the base change functor is:
`g^*` is the composite of the inclusion of sheaves into presheaves, which preserves finite
limits, that left Kan extension, and sheafification, which is left exact by
`HasSheafify`. Unlike `preservesFiniteLimits_lowerStar` this is not automatic; see
`AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` for the case of an étale
morphism, where the Kan extension is precomposition with a right adjoint. -/
instance preservesFiniteLimits_upperStar
    [PreservesFiniteLimits ((MorphismProperty.Over.pullback P ⊤ g).op.lan :
      ((P.Over ⊤ U)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ W)ᵒᵖ ⥤ A)] :
    PreservesFiniteLimits (upperStar A P Q g) := by
  unfold upperStar Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

end Adjunction

section Comp

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*` of pushforwards on
sheaves for the small sites: both sides send a sheaf `G` to the sheaf
`(V → R) ↦ G(V ×_R T → T)`, up to the pullback pasting isomorphism
`(V ×_R S) ×_S T ≅ V ×_R T` of `MorphismProperty.Over.pullbackComp`. -/
noncomputable def lowerStarComp (h : T ⟶ R := h₁ ≫ h₂) (hh : h = h₁ ≫ h₂ := by cat_disch) :
    lowerStar A P Q hQP h₁ ⋙ lowerStar A P Q hQP h₂ ≅ lowerStar A P Q hQP h :=
  have := isContinuous_overPullback P Q hQP h₁
  have := isContinuous_overPullback P Q hQP h₂
  have := isContinuous_overPullback P Q hQP h
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h₁ h₂ h hh).symm) A
    (R.smallGrothendieckTopology Q (Q := P)) (S.smallGrothendieckTopology Q (Q := P))
    (T.smallGrothendieckTopology Q (Q := P))

section UpperStar

/-- The composition isomorphism `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks on sheaves
for the small sites, obtained from the composition isomorphism `lowerStarComp` of the
pushforwards by uniqueness of left adjoints: both sides are left adjoint to
`(h₁)_* ⋙ (h₂)_*`. -/
noncomputable def upperStarComp (h : T ⟶ R := h₁ ≫ h₂) (hh : h = h₁ ≫ h₂ := by cat_disch) :
    upperStar A P Q h ≅ upperStar A P Q h₂ ⋙ upperStar A P Q h₁ :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction A P Q hQP h)
      ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁))).symm
    (lowerStarComp A P Q hQP h₁ h₂ h hh).symm).symm

end UpperStar

end Comp

section Components

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h : T ⟶ R) (hh : h = h₁ ≫ h₂)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_hom_app_hom_app
    (M : Sheaf (T.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ R) :
    (((lowerStarComp A P Q hQP h₁ h₂ h hh).hom.app M).hom).app (op b) =
      M.obj.map
        ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h₁ h₂ h hh).hom.app b).op := by
  simp [lowerStarComp]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStar_obj_obj_map {W U : Scheme.{u}} (g : W ⟶ U)
    (M : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A) {b b' : P.Over ⊤ U} (φ : b ⟶ b') :
    ((lowerStar A P Q hQP g).obj M).obj.map φ.op =
      M.obj.map ((MorphismProperty.Over.pullback P ⊤ g).map φ).op :=
  rfl

/-- The pushforward along the identity is the identity functor. -/
noncomputable def lowerStarId (U : Scheme.{u}) :
    lowerStar A P Q hQP (𝟙 U) ≅ 𝟭 (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  have := isContinuous_overPullback P Q hQP (𝟙 U)
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId (P := P) (Q := ⊤) U) A
    (U.smallGrothendieckTopology Q (Q := P))

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarId_hom_app_hom_app (U : Scheme.{u})
    (M : Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ U) :
    (((lowerStarId A P Q hQP U).hom.app M).hom).app (op b) =
      M.obj.map ((MorphismProperty.Over.pullbackId (P := P) (Q := ⊤) U).inv.app b).op := by
  simp [lowerStarId]

end Components

section Coherence

variable {R S T V : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₃ : R ⟶ V)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Associativity coherence of the composition isomorphism of pushforwards. -/
lemma lowerStarComp_assoc (h₁₂ : T ⟶ R) (e₁₂ : h₁₂ = h₁ ≫ h₂) (h₂₃ : S ⟶ V)
    (e₂₃ : h₂₃ = h₂ ≫ h₃) (h : T ⟶ V) (e : h = h₁₂ ≫ h₃) (e' : h = h₁ ≫ h₂₃) :
    Functor.whiskerRight (lowerStarComp A P Q hQP h₁ h₂ h₁₂ e₁₂).hom
          (lowerStar A P Q hQP h₃) ≫
        (lowerStarComp A P Q hQP h₁₂ h₃ h e).hom =
      (Functor.associator (lowerStar A P Q hQP h₁) (lowerStar A P Q hQP h₂)
            (lowerStar A P Q hQP h₃)).hom ≫
        Functor.whiskerLeft (lowerStar A P Q hQP h₁)
            (lowerStarComp A P Q hQP h₂ h₃ h₂₃ e₂₃).hom ≫
          (lowerStarComp A P Q hQP h₁ h₂₃ h e').hom := by
  ext M b
  obtain ⟨b⟩ := b
  simp [lowerStarComp_hom_app_hom_app, lowerStar_map_hom_app, lowerStar_obj_obj_map,
    ← Functor.map_comp, ← op_comp]
  congr 2
  simpa using congr_app (MorphismProperty.Over.pullbackComp_hom_assoc (P := P) (Q := ⊤)
    h₁ h₂ h₃ h₁₂ e₁₂ h₂₃ e₂₃ h e e') b

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Unit coherence of the composition isomorphism of pushforwards: composing with the
identity on the target. -/
lemma lowerStarComp_id_right {W U : Scheme.{u}} (g : W ⟶ U) (e : g = g ≫ 𝟙 U) :
    (lowerStarComp A P Q hQP g (𝟙 U) g e).hom =
      Functor.whiskerLeft (lowerStar A P Q hQP g) (lowerStarId A P Q hQP U).hom ≫
        (lowerStar A P Q hQP g).rightUnitor.hom := by
  ext M b
  obtain ⟨b⟩ := b
  simp [lowerStarComp_hom_app_hom_app, lowerStarId_hom_app_hom_app, lowerStar_obj_obj_map]
  congr 2
  simpa using congr_app (MorphismProperty.Over.pullbackComp_id_right (P := P) (Q := ⊤) g) b

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Unit coherence of the composition isomorphism of pushforwards: composing with the
identity on the source. -/
lemma lowerStarComp_id_left {W U : Scheme.{u}} (g : W ⟶ U) (e : g = 𝟙 W ≫ g) :
    (lowerStarComp A P Q hQP (𝟙 W) g g e).hom =
      Functor.whiskerRight (lowerStarId A P Q hQP W).hom (lowerStar A P Q hQP g) ≫
        (lowerStar A P Q hQP g).leftUnitor.hom := by
  ext M b
  obtain ⟨b⟩ := b
  simp [lowerStarComp_hom_app_hom_app, lowerStarId_hom_app_hom_app, lowerStar_map_hom_app]
  congr 2
  simpa using congr_app (MorphismProperty.Over.pullbackComp_id_left (P := P) (Q := ⊤) g) b

end Coherence

section UpperStarCoherence

/-- The pullback along the identity is the identity functor. -/
noncomputable def upperStarId (U : Scheme.{u}) :
    upperStar A P Q (𝟙 U) ≅ 𝟭 (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction A P Q hQP (𝟙 U)) Adjunction.id).symm
    (lowerStarId A P Q hQP U)).symm

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h : T ⟶ R) (hh : h = h₁ ≫ h₂)

lemma conjugateEquiv_upperStarComp_hom :
    conjugateEquiv ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
          (upperStarLowerStarAdjunction A P Q hQP h₁))
        (upperStarLowerStarAdjunction A P Q hQP h)
        (upperStarComp A P Q hQP h₁ h₂ h hh).hom =
      (lowerStarComp A P Q hQP h₁ h₂ h hh).hom := by
  simp [upperStarComp]

lemma conjugateEquiv_upperStarComp_inv :
    conjugateEquiv (upperStarLowerStarAdjunction A P Q hQP h)
        ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
          (upperStarLowerStarAdjunction A P Q hQP h₁))
        (upperStarComp A P Q hQP h₁ h₂ h hh).inv =
      (lowerStarComp A P Q hQP h₁ h₂ h hh).inv := by
  simp [upperStarComp]

lemma conjugateEquiv_upperStarId_inv (U : Scheme.{u}) :
    conjugateEquiv (upperStarLowerStarAdjunction A P Q hQP (𝟙 U)) Adjunction.id
        (upperStarId A P Q hQP U).inv =
      (lowerStarId A P Q hQP U).hom := by
  simp [upperStarId]

variable {V : Scheme.{u}} (h₃ : R ⟶ V)

lemma upperStarComp_assoc (h₁₂ : T ⟶ R) (e₁₂ : h₁₂ = h₁ ≫ h₂) (h₂₃ : S ⟶ V)
    (e₂₃ : h₂₃ = h₂ ≫ h₃) (hh' : T ⟶ V) (e : hh' = h₁₂ ≫ h₃) (e' : hh' = h₁ ≫ h₂₃) :
    (upperStarComp A P Q hQP h₁₂ h₃ hh' e).hom ≫
        Functor.whiskerLeft (upperStar A P Q h₃) (upperStarComp A P Q hQP h₁ h₂ h₁₂ e₁₂).hom =
      (upperStarComp A P Q hQP h₁ h₂₃ hh' e').hom ≫
        Functor.whiskerRight (upperStarComp A P Q hQP h₂ h₃ h₂₃ e₂₃).hom (upperStar A P Q h₁) ≫
          (Functor.associator (upperStar A P Q h₃) (upperStar A P Q h₂)
            (upperStar A P Q h₁)).hom := by
  apply (conjugateEquiv
    ((upperStarLowerStarAdjunction A P Q hQP h₃).comp
      ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁)))
    (upperStarLowerStarAdjunction A P Q hQP hh')).injective
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A P Q hQP h₃).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁₂)) _,
      ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A P Q hQP h₂₃).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁)) _,
      ← conjugateEquiv_comp _ (((upperStarLowerStarAdjunction A P Q hQP h₃).comp
        (upperStarLowerStarAdjunction A P Q hQP h₂)).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁)) _,
      conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, conjugateEquiv_associator_hom,
      conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarComp_hom,
      conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarComp_hom]
  simpa using lowerStarComp_assoc A P Q hQP h₁ h₂ h₃ h₁₂ e₁₂ h₂₃ e₂₃ hh' e e'

lemma upperStarComp_id_right {W U : Scheme.{u}} (g : W ⟶ U) (e : g = g ≫ 𝟙 U) :
    (upperStarComp A P Q hQP g (𝟙 U) g e).hom =
      (upperStar A P Q g).leftUnitor.inv ≫
        Functor.whiskerRight (upperStarId A P Q hQP U).inv (upperStar A P Q g) := by
  apply (conjugateEquiv ((upperStarLowerStarAdjunction A P Q hQP (𝟙 U)).comp
    (upperStarLowerStarAdjunction A P Q hQP g))
    (upperStarLowerStarAdjunction A P Q hQP g)).injective
  rw [← conjugateEquiv_comp _ (Adjunction.id.comp (upperStarLowerStarAdjunction A P Q hQP g)) _,
    conjugateEquiv_whiskerRight, conjugateEquiv_leftUnitor_inv,
    conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarId_inv]
  exact lowerStarComp_id_right A P Q hQP g e

lemma upperStarComp_id_left {W U : Scheme.{u}} (g : W ⟶ U) (e : g = 𝟙 W ≫ g) :
    (upperStarComp A P Q hQP (𝟙 W) g g e).hom =
      (upperStar A P Q g).rightUnitor.inv ≫
        Functor.whiskerLeft (upperStar A P Q g) (upperStarId A P Q hQP W).inv := by
  apply (conjugateEquiv ((upperStarLowerStarAdjunction A P Q hQP g).comp
    (upperStarLowerStarAdjunction A P Q hQP (𝟙 W)))
    (upperStarLowerStarAdjunction A P Q hQP g)).injective
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A P Q hQP g).comp Adjunction.id) _,
    conjugateEquiv_whiskerLeft, conjugateEquiv_rightUnitor_inv,
    conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarId_inv]
  exact lowerStarComp_id_left A P Q hQP g e


end UpperStarCoherence

end GrothendieckTopology

end CategoryTheory
