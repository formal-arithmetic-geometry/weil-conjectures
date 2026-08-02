/-
Copyright (c) 2026 Wei Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Yang
-/
import WeilConjectures.CategoryTheory.Sites.LocalizationLowerShriek

/-!
# Open localizations and extension by zero

Let `(C, J)` be a site and `f : V ⟶ U` a morphism in `C`. The lower shriek
`j_{f!} : Sheaf (J.over V) A ⥤ Sheaf (J.over U) A` was constructed in
`WeilConjectures.CategoryTheory.Sites.LocalizationLowerShriek` for an *arbitrary* `f`.
This file treats the **open** case, in which `j_{f!}` deserves the name *extension by zero*.

## The open condition

The correct openness condition is *not* about `f` itself but about the morphism
`f̃ : Ṽ ⟶ Ũ` of sheafified representables: the induced geometric morphism of slice topoi is an
open immersion precisely when `f̃` is a monomorphism of sheaves. We record this as the class
`J.IsOpenLocalization f`, defined by `Mono (J.sheafifiedYonedaMap f)` where
`J.sheafifiedYonedaMap f = (presheafToSheaf J _).map (yoneda.map f)`.

- If `f` is a monomorphism in `C` and sheafification is exact (`HasSheafify`), then
  `J.IsOpenLocalization f` holds (`isOpenLocalization_of_mono`); no subcanonicity is needed
  because left exact sheafification preserves the monomorphism `yoneda.map f`.
- If moreover `J` is subcanonical, the two conditions agree
  (`isOpenLocalization_iff_mono`).

## Main results, proved under `Mono f`

The "strict" case where `f` is a monomorphism in `C` covers the geometric applications
(e.g. an open immersion `V ↪ U` inside a small étale site, open immersions being monomorphisms
of schemes). In this case `Over.map f` is fully faithful and we prove:

- `isIso_localizationLowerShriekAdjunction_unit_app` /
  `localizationLowerShriekUnitIso`: the unit `𝟭 ⟶ j_{f!} ⋙ j_f^*` of the adjunction
  `j_{f!} ⊣ j_f^*` is an isomorphism;
- `localizationLowerShriekCompRestrictionIso` : `j_{f!} ⋙ j_f^* ≅ 𝟭`;
- `localizationLowerShriekFullyFaithful`, and the instances
  `(J.localizationLowerShriek A f).Full`, `(J.localizationLowerShriek A f).Faithful`;
- for subcanonical `J`, the same results assuming `J.IsOpenLocalization f` instead of
  `Mono f` (`localizationLowerShriek_full_of_isOpenLocalization`, ...).

The proof of the unit isomorphism is by direct computation
(`localizationLowerShriekAdjunction_unit_app_hom`): the underlying presheaf morphism of the
unit is the composite of the left Kan extension unit (an isomorphism, since
`(Over.map f).op` is fully faithful) with the restriction to `C/V` of the sheafification unit
of the Kan extension; the latter is an isomorphism because restriction along the
continuous *and* cocontinuous functor `Over.map f` is compatible with sheafification
(`Functor.toSheafify_pullbackSheafificationCompatibility`) and the restricted presheaf is
already a sheaf.

## Extension by zero, pointwise

For `a : Over U` let `Over.LiftIndex f a := {α : a.left ⟶ V // α ≫ f = a.hom}` be the type of
lifts of `a` through `f`. At the presheaf level the value of the left Kan extension at `a` is
the coproduct over `Over.LiftIndex f a` of the values of `F`; when `f` is a monomorphism there
is *at most one* lift (`Over.LiftIndex.subsingleton`) and the formula degenerates to the
extension-by-zero shape:

- `localizationLowerShriekPresheafObjIsoOfLift`: if `α` is a lift of `a`, then
  `(j_{f,!}^{pre} P)(a) ≅ P(α)`;
- `isZero_localizationLowerShriekPresheafObj`: if `a` admits no lift and `A` has a zero
  object, then `(j_{f,!}^{pre} P)(a)` is zero (an `IsZero` statement).

Beware that these are statements about the presheaf-level Kan extension; the value of the
*sheaf-level* `j_{f!}` is obtained from it by `J.over U`-sheafification, which in general
changes sections (only the local behaviour is preserved).

## Not (yet) in this file

- The unit isomorphism under the general `IsOpenLocalization` hypothesis (mono of the
  *sheafified* Yoneda map, without `Mono f` or subcanonicity) requires a genuinely
  local argument (the equalizer sieves of two lifts of the same morphism are covering);
  it is left for future work.
- The general coproduct formula for arbitrary `f`, and the compatibility
  `j_{f!}(h^#_{T/V}) ≅ h^#_{T/U}` with sheafified representables (which needs the
  isomorphism `Lan_{L.op} ∘ yoneda ≅ yoneda ∘ L`, not yet in mathlib).
-/

universe v' v u' u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section OverMap

variable {V U : C} (f : V ⟶ U)

/-- The functor `Over.map f` is always faithful. -/
instance Over.map_faithful : (Over.map f).Faithful where
  map_injective {b b'} {g h} e := by
    have he := congrArg CommaMorphism.left e
    ext
    exact he

/-- If `f` is a monomorphism, the functor `Over.map f` is full (hence fully faithful). -/
instance Over.map_full [Mono f] : (Over.map f).Full where
  map_surjective {b b'} g :=
    ⟨Over.homMk g.left (by rw [← cancel_mono f, Category.assoc]; simpa using Over.w g), by
      ext; simp⟩

end OverMap

section LiftIndex

variable {V U : C} (f : V ⟶ U) (a : Over U)

/-- The type of lifts of an object `a : Over U` through `f : V ⟶ U`, i.e. of morphisms
`α : a.left ⟶ V` with `α ≫ f = a.hom`. The presheaf-level lower shriek of `P` at `a` is the
coproduct of the values of `P` at the lifts of `a`; for a monomorphism `f` there is at most
one lift, which produces the "extension by zero" shape of the formula. -/
def Over.LiftIndex : Type v :=
  {α : a.left ⟶ V // α ≫ f = a.hom}

namespace Over.LiftIndex

variable {f a}

/-- A monomorphism admits at most one lift through it. -/
instance subsingleton [Mono f] : Subsingleton (Over.LiftIndex f a) :=
  ⟨fun α β => Subtype.ext ((cancel_mono f).mp (α.2.trans β.2.symm))⟩

/-- The object of `Over V` determined by a lift of `a : Over U` through `f`. -/
def toOver (α : Over.LiftIndex f a) : Over V :=
  Over.mk α.1

@[simp]
lemma toOver_left (α : Over.LiftIndex f a) : α.toOver.left = a.left := rfl

@[simp]
lemma toOver_hom (α : Over.LiftIndex f a) : α.toOver.hom = α.1 := rfl

/-- The canonical comparison morphism `a ⟶ (Over.map f).obj α.toOver` in `Over U`
associated with a lift `α` of `a` (its underlying morphism is the identity). -/
def homToMap (α : Over.LiftIndex f a) : a ⟶ (Over.map f).obj α.toOver :=
  Over.homMk (𝟙 a.left) (by simpa using α.2)

@[simp]
lemma homToMap_left (α : Over.LiftIndex f a) : α.homToMap.left = 𝟙 a.left := rfl

/-- The object of the comma category `CostructuredArrow (Over.map f).op (op a)` associated
with a lift `α` of `a`; when `f` is a monomorphism it is a terminal object, see
`Over.LiftIndex.isTerminalCostructuredArrow`. -/
def costructuredArrow (α : Over.LiftIndex f a) :
    CostructuredArrow (Over.map f).op (op a) :=
  CostructuredArrow.mk α.homToMap.op

@[simp]
lemma costructuredArrow_left (α : Over.LiftIndex f a) :
    α.costructuredArrow.left = op α.toOver := rfl

@[simp]
lemma costructuredArrow_hom (α : Over.LiftIndex f a) :
    α.costructuredArrow.hom = α.homToMap.op := rfl

end Over.LiftIndex

/-- The lift of `a` extracted from an object of the comma category
`CostructuredArrow (Over.map f).op (op a)`. -/
def CostructuredArrow.toLiftIndex (s : CostructuredArrow (Over.map f).op (op a)) :
    Over.LiftIndex f a :=
  ⟨s.hom.unop.left ≫ s.left.unop.hom, by
    rw [Category.assoc]; exact Over.w s.hom.unop⟩

/-- If `a` has no lift through `f`, the comma category indexing the pointwise left Kan
extension at `a` is empty. -/
lemma isEmpty_costructuredArrow_of_isEmpty_liftIndex (h : IsEmpty (Over.LiftIndex f a)) :
    IsEmpty (CostructuredArrow (Over.map f).op (op a)) :=
  ⟨fun s => h.elim s.toLiftIndex⟩

namespace Over.LiftIndex

variable {f a}

/-- If `f` is a monomorphism, the comma object associated with a lift `α` of `a` is terminal
in `CostructuredArrow (Over.map f).op (op a)`; this is what makes the pointwise left Kan
extension formula collapse to a single value. -/
noncomputable def isTerminalCostructuredArrow [Mono f] (α : Over.LiftIndex f a) :
    IsTerminal α.costructuredArrow :=
  IsTerminal.ofUniqueHom
    (fun s =>
      CostructuredArrow.homMk
        (Quiver.Hom.op
          (Over.homMk s.hom.unop.left
            ((cancel_mono f).mp (by
              rw [Category.assoc]
              exact (Over.w s.hom.unop).trans α.2.symm)) :
            α.toOver ⟶ s.left.unop))
        (by
          apply Quiver.Hom.unop_inj
          ext
          exact Category.id_comp _))
    (fun s m => by
      ext
      apply Quiver.Hom.unop_inj
      ext
      have hw := m.w
      apply_fun (fun z => z.unop.left) at hw
      exact ((Category.id_comp _).symm.trans hw).trans (Category.id_comp _))

end Over.LiftIndex

end LiftIndex

section IsZeroHelper

open ZeroObject

variable {A : Type u'} [Category.{v'} A]

/-- The point of a colimit cocone over a diagram all of whose values are zero objects is a
zero object. Unlike `Limits.IsColimit.isZero_pt`, this does not assume that the ambient
category has zero morphisms. -/
theorem Limits.IsColimit.isZero_pt_of_forall_isZero [HasZeroObject A] {J' : Type*}
    [Category J'] {D : J' ⥤ A}
    {c : Cocone D} (hc : IsColimit c) (hD : ∀ j, IsZero (D.obj j)) : IsZero c.pt := by
  let zc : Cocone D := Cocone.mk (0 : A)
    ⟨fun j => (hD j).to_ (0 : A), fun _ _ _ => (hD _).eq_of_src _ _⟩
  have hz : IsColimit zc :=
    { desc := fun s => (isZero_zero A).to_ s.pt
      fac := fun s j => (hD j).eq_of_src _ _
      uniq := fun s m _ => (isZero_zero A).eq_of_src _ _ }
  exact (isZero_zero A).of_iso (hc.coconePointUniqueUpToIso hz)

end IsZeroHelper

section ExtensionByZeroPresheaf

variable (A : Type u') [Category.{v'} A]
variable {V U : C} (f : V ⟶ U)
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseLeftKanExtension P]
variable (P : (Over V)ᵒᵖ ⥤ A) {a : Over U}

/-- The pointwise description of the presheaf-level lower shriek at `a : Over U` when `f` is a
monomorphism and `a` admits a lift `α` through `f`: the value of `Lan_{(Over.map f).op} P` at
`a` is the value of `P` at the lift. This is the nontrivial half of the "extension by zero"
formula (at the presheaf level). -/
noncomputable def localizationLowerShriekPresheafObjIsoOfLift [Mono f]
    (α : Over.LiftIndex f a) :
    ((localizationLowerShriekPresheaf A f).obj P).obj (op a) ≅ P.obj (op α.toOver) :=
  ((Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _
        ((Over.map f).op.lanUnit.app P)) (op a)).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal α.isTerminalCostructuredArrow _)

/-- The vanishing half of the "extension by zero" formula at the presheaf level: if `a : Over U`
admits no lift through `f` and `A` has a zero object, then the presheaf-level lower shriek
vanishes at `a`. (No monomorphism hypothesis on `f` is needed for this half.) -/
theorem isZero_localizationLowerShriekPresheafObj [HasZeroObject A]
    (h : IsEmpty (Over.LiftIndex f a)) :
    IsZero (((localizationLowerShriekPresheaf A f).obj P).obj (op a)) := by
  have hempty := isEmpty_costructuredArrow_of_isEmpty_liftIndex f a h
  exact ((Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _
      ((Over.map f).op.lanUnit.app P)) (op a)).isZero_pt_of_forall_isZero
    (fun j => hempty.elim j)

end ExtensionByZeroPresheaf

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

section OpenLocalization

variable [HasWeakSheafify J (Type v)] {V U : C}

/-- The morphism of sheafified representables `Ṽ ⟶ Ũ` induced by a morphism `f : V ⟶ U` of
the underlying site. -/
noncomputable def sheafifiedYonedaMap (f : V ⟶ U) :
    (presheafToSheaf J (Type v)).obj (_root_.CategoryTheory.yoneda.obj V) ⟶
      (presheafToSheaf J (Type v)).obj (_root_.CategoryTheory.yoneda.obj U) :=
  (presheafToSheaf J (Type v)).map (_root_.CategoryTheory.yoneda.map f)

/-- A morphism `f : V ⟶ U` is an *open localization* for the topology `J` if the induced
morphism `f̃ : Ṽ ⟶ Ũ` of sheafified representables is a monomorphism. This is the condition
under which the induced geometric morphism of slice topoi is an open immersion and the lower
shriek `J.localizationLowerShriek A f` is an "extension by zero".

The condition is deliberately formulated via the *sheafified* Yoneda map rather than as
`Mono f`: for a non-subcanonical topology, sheafification may change the relevant condition.
`Mono f` is sufficient when sheafification is exact (`isOpenLocalization_of_mono`), and
equivalent when `J` is moreover subcanonical (`isOpenLocalization_iff_mono`). -/
class IsOpenLocalization (f : V ⟶ U) : Prop where
  mono_sheafifiedYonedaMap : Mono (J.sheafifiedYonedaMap f)

instance (f : V ⟶ U) [J.IsOpenLocalization f] : Mono (J.sheafifiedYonedaMap f) :=
  IsOpenLocalization.mono_sheafifiedYonedaMap

end OpenLocalization

section MonoCriteria

variable [HasSheafify J (Type v)] {V U : C}

/-- If sheafification is exact and `f` is a monomorphism in `C`, then `f` is an open
localization. (Subcanonicity is not needed: `yoneda` preserves monomorphisms, and so does the
left exact sheafification functor.) -/
theorem isOpenLocalization_of_mono (f : V ⟶ U) [Mono f] : J.IsOpenLocalization f :=
  ⟨inferInstanceAs (Mono ((presheafToSheaf J (Type v)).map
    (_root_.CategoryTheory.yoneda.map f)))⟩

/-- For a subcanonical topology with exact sheafification, `f : V ⟶ U` is an open localization
if and only if it is a monomorphism in the underlying category. -/
theorem isOpenLocalization_iff_mono [J.Subcanonical] (f : V ⟶ U) :
    J.IsOpenLocalization f ↔ Mono f := by
  refine ⟨fun h => ⟨fun {T} g₁ g₂ e => ?_⟩, fun h => J.isOpenLocalization_of_mono f⟩
  have e' : (presheafToSheaf J (Type v)).map (_root_.CategoryTheory.yoneda.map g₁) ≫
        J.sheafifiedYonedaMap f =
      (presheafToSheaf J (Type v)).map (_root_.CategoryTheory.yoneda.map g₂) ≫
        J.sheafifiedYonedaMap f := by
    simp only [sheafifiedYonedaMap, ← Functor.map_comp, e]
  have e'' := (cancel_mono (J.sheafifiedYonedaMap f)).mp e'
  have hV : IsIso (_root_.CategoryTheory.toSheafify J
      (_root_.CategoryTheory.yoneda.obj V)) :=
    _root_.CategoryTheory.isIso_toSheafify J
      ((isSheaf_iff_isSheaf_of_type J _).mpr (Subcanonical.isSheaf_of_isRepresentable _))
  have nat₁ := (sheafificationAdjunction J (Type v)).unit.naturality
    (_root_.CategoryTheory.yoneda.map g₁)
  have nat₂ := (sheafificationAdjunction J (Type v)).unit.naturality
    (_root_.CategoryTheory.yoneda.map g₂)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
    sheafificationAdjunction_unit_app] at nat₁ nat₂
  apply _root_.CategoryTheory.yoneda.map_injective
  have hM := congrArg (fun q => (sheafToPresheaf J (Type v)).map q) e''
  exact (cancel_mono (_root_.CategoryTheory.toSheafify J
    (_root_.CategoryTheory.yoneda.obj V))).mp
    (nat₁.trans ((congrArg (fun M => _root_.CategoryTheory.toSheafify J
      (_root_.CategoryTheory.yoneda.obj T) ≫ M) hM).trans nat₂.symm))

end MonoCriteria

section UnitIso

variable (A : Type u') [Category.{v'} A]
variable {V U : C} (f : V ⟶ U)
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (J.over V) A] [HasWeakSheafify (J.over U) A]

omit [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension P]
  [HasWeakSheafify (J.over V) A] in
/-- The underlying presheaf morphism of the unit of the adjunction `j_{f!} ⊣ j_f^*` at a sheaf
`F` is the composite of the left Kan extension unit with the restriction along
`(Over.map f).op` of the sheafification unit. -/
lemma localizationLowerShriekAdjunction_unit_app_hom (F : Sheaf (J.over V) A) :
    ((J.localizationLowerShriekAdjunction A f).unit.app F).hom =
      ((Over.map f).op.lanAdjunction A).unit.app F.obj ≫
        (Over.map f).op.whiskerLeft
          (_root_.CategoryTheory.toSheafify (J.over U)
            ((Over.map f).op.lan.obj F.obj)) := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
      (adj := (((Over.map f).op.lanAdjunction A).comp
        (sheafificationAdjunction (J.over U) A)))
      (hiC := fullyFaithfulSheafToPresheaf (J.over V) A)
      (hiD := Functor.FullyFaithful.id _)
      (L := Functor.sheafPullbackConstruction.sheafPullback (Over.map f) A
        (J.over V) (J.over U))
      (R := (Over.map f).sheafPushforwardContinuous A (J.over V) (J.over U))
      (comm1 := Iso.refl _) (comm2 := Iso.refl _) F).trans ?_
  dsimp
  change _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]
  rw [Adjunction.comp_unit_app]
  dsimp
  rfl

/-- **The unit isomorphism in the open case.** If `f` is a monomorphism, then the unit of the
adjunction `j_{f!} ⊣ j_f^*` is an isomorphism at every sheaf `F` on `C/V`: restricting the
extension of `F` back to `C/V` recovers `F`.

The two factors of the unit are isomorphisms for different reasons: the left Kan extension
unit because `(Over.map f).op` is fully faithful, and the restricted sheafification unit
because restriction along the continuous and cocontinuous functor `Over.map f` commutes with
sheafification while the restriction of the Kan extension is already a sheaf (being
isomorphic to `F`). -/
instance isIso_localizationLowerShriekAdjunction_unit_app [Mono f]
    (F : Sheaf (J.over V) A) :
    IsIso ((J.localizationLowerShriekAdjunction A f).unit.app F) := by
  have h₂ : IsIso ((Over.map f).op.whiskerLeft
      (_root_.CategoryTheory.toSheafify (J.over U)
        ((Over.map f).op.lan.obj F.obj))) := by
    rw [← Functor.toSheafify_pullbackSheafificationCompatibility (Over.map f) A
      (J.over V) (J.over U)]
    have h₀ : IsIso (_root_.CategoryTheory.toSheafify (J.over V)
        ((Over.map f).op ⋙ (Over.map f).op.lan.obj F.obj)) :=
      _root_.CategoryTheory.isIso_toSheafify (J.over V)
        ((Presheaf.isSheaf_of_iso_iff
          (asIso (((Over.map f).op.lanAdjunction A).unit.app F.obj))).mp F.property)
    have h₁ : IsIso (((Over.map f).pushforwardContinuousSheafificationCompatibility A
        (J.over V) (J.over U)).hom.app ((Over.map f).op.lan.obj F.obj)).hom :=
      inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
        (((Over.map f).pushforwardContinuousSheafificationCompatibility A
          (J.over V) (J.over U)).hom.app ((Over.map f).op.lan.obj F.obj))))
    exact IsIso.comp_isIso' h₀ h₁
  have hmap : IsIso ((J.localizationLowerShriekAdjunction A f).unit.app F).hom := by
    rw [localizationLowerShriekAdjunction_unit_app_hom]
    exact ((asIso (((Over.map f).op.lanAdjunction A).unit.app F.obj)) ≪≫
      @asIso _ _ _ _ _ h₂).isIso_hom
  have : IsIso ((sheafToPresheaf (J.over V) A).map
      ((J.localizationLowerShriekAdjunction A f).unit.app F)) := hmap
  exact isIso_of_reflects_iso _ (sheafToPresheaf (J.over V) A)

instance isIso_localizationLowerShriekUnit [Mono f] :
    IsIso (J.localizationLowerShriekUnit A f) :=
  NatIso.isIso_of_isIso_app _

/-- In the open case (`f` a monomorphism), the unit of `j_{f!} ⊣ j_f^*` is a natural
isomorphism `𝟭 ≅ j_{f!} ⋙ j_f^*`. -/
noncomputable def localizationLowerShriekUnitIso [Mono f] :
    𝟭 (Sheaf (J.over V) A) ≅
      J.localizationLowerShriek A f ⋙ J.localizationRestriction A f :=
  asIso ((J.localizationLowerShriekAdjunction A f).unit)

/-- In the open case (`f` a monomorphism), restricting the extension by zero back to `C/V`
recovers the original sheaf: `j_f^* ∘ j_{f!} ≅ 𝟭`, naturally. -/
noncomputable def localizationLowerShriekCompRestrictionIso [Mono f] :
    J.localizationLowerShriek A f ⋙ J.localizationRestriction A f ≅
      𝟭 (Sheaf (J.over V) A) :=
  (J.localizationLowerShriekUnitIso A f).symm

/-- In the open case (`f` a monomorphism), the lower shriek `j_{f!}` is fully faithful. -/
noncomputable def localizationLowerShriekFullyFaithful [Mono f] :
    (J.localizationLowerShriek A f).FullyFaithful :=
  (J.localizationLowerShriekAdjunction A f).fullyFaithfulLOfIsIsoUnit

instance localizationLowerShriekFull [Mono f] : (J.localizationLowerShriek A f).Full :=
  (J.localizationLowerShriekFullyFaithful A f).full

instance localizationLowerShriekFaithful [Mono f] :
    (J.localizationLowerShriek A f).Faithful :=
  (J.localizationLowerShriekFullyFaithful A f).faithful

end UnitIso

section SubcanonicalOpen

variable (A : Type u') [Category.{v'} A]
variable {V U : C} (f : V ⟶ U)
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (J.over V) A] [HasWeakSheafify (J.over U) A]
variable [HasSheafify J (Type v)] [J.Subcanonical]

/-- For a subcanonical topology, the lower shriek along an open localization is full. -/
theorem localizationLowerShriek_full_of_isOpenLocalization [J.IsOpenLocalization f] :
    (J.localizationLowerShriek A f).Full := by
  haveI : Mono f := (J.isOpenLocalization_iff_mono f).mp inferInstance
  infer_instance

/-- For a subcanonical topology, the lower shriek along an open localization is faithful. -/
theorem localizationLowerShriek_faithful_of_isOpenLocalization [J.IsOpenLocalization f] :
    (J.localizationLowerShriek A f).Faithful := by
  haveI : Mono f := (J.isOpenLocalization_iff_mono f).mp inferInstance
  infer_instance

/-- For a subcanonical topology, the unit of `j_{f!} ⊣ j_f^*` is an isomorphism along any open
localization. -/
theorem isIso_localizationLowerShriekUnit_of_isOpenLocalization [J.IsOpenLocalization f] :
    IsIso (J.localizationLowerShriekUnit A f) := by
  haveI : Mono f := (J.isOpenLocalization_iff_mono f).mp inferInstance
  infer_instance

end SubcanonicalOpen

end GrothendieckTopology

end CategoryTheory
