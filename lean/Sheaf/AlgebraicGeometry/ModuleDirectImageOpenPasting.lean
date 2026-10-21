/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-! # Sectionwise module direct-image and open-restriction pasting

Source: blueprint `sk-thm-sf-comp-composition`, Composition isomorphism and Canonicity
and associativity; Stacks Project, proetale.tex, Tag 09A5, section-morphism;
sites.tex, Tag 00XZ, section-localize; sites-modules.tex, Tags 03D3, 03D6, 03DH
(blueprint: lem-sfb-module-direct-image-open-pasting).

The helpers spell out the clauses of this single statement. Cartesian squares may use
any representative of the fibre product, so the two pasting laws have literally matching
vertices. The open-slice coordinates are the distinguished section coprojections of the
specified module adjunctions, including extension along the canonical coefficient map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Families of module open-slice comparisons, on cartesian squares with their actual maps.
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Comparisons :=
  ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i]
    (_sq : IsPullback i fU f j),
    lowerStar Λ f ⋙ upperStar Λ j ≅ upperStar Λ i ⋙ lowerStar Λ fU

/-- The specified module inverse image is sheaf inverse image with its action transported
along alpha inverse. This is the existing scalar-extension/comap-inverse isomorphism,
whiskered by the existing internal sheaf inverse image; no coefficient map is chosen.
Source: Stacks 03D3 and 03DH (blueprint: lem-sfb-module-direct-image-open-pasting). -/
noncomputable def inverseImageActionIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar Λ f ≅
      (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
        Mod.comap (inv (condensedPullbackHom Λ f)) :=
  Functor.isoWhiskerLeft
    ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))

/-- The distinguished section coprojection for open pullback. It first uses the module
adjunction unit (hence the scalar-extension unit), then restriction along the graph of the
site object. Thus it includes the specified coefficient action, rather than a freely
chosen identification. Source: Stacks 03D3 and 00XZ
(blueprint: lem-sfb-module-direct-image-open-pasting). -/
noncomputable def coprojection {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (E : X.ProEt)
    (s : M.X.obj.obj (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E))) :
    ((upperStar Λ j).obj M).X.obj.obj (op E) :=
  ((upperStar Λ j).obj M).X.obj.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial).unit.app E).op
      (((upperStarLowerStarAdjunction Λ j).unit.app M).hom.hom.app
        (op ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)) s)

/-- The projection-preserving fibre-product arrow for an open cartesian square. Its
restriction on sections is the comparison required in clause (a).
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
noncomputable def sectionArrow {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y)
    [IsOpenImmersion j] (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i]
    (sq : IsPullback i fU f j) (E : U.ProEt) :
    (Scheme.ProEtaleOpenRestriction.objectComposition i).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU).obj E) ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
        ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E) :=
  MorphismProperty.Over.homMk
    (pullback.map E.hom fU (E.hom ≫ j) f (𝟙 E.left) i j
      (Category.id_comp _).symm sq.w.symm)
    (pullback.lift_snd _ _ _)

/-- Clause (a), with the canonical open-slice coordinates explicitly normalized. All maps
are module maps for the existing scalar-extension functors. Bijectivity identifies the
open pullback with sheaf inverse image carrying the action transported by alpha inverse.
Source: Stacks 03D3, 03D6, 03DH (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Sectionwise (β : Comparisons Λ) : Prop :=
  (∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (E : X.ProEt), Function.Bijective (coprojection Λ j M E)) ∧
  ∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (E : U.ProEt)
    (s : M.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
      ((Scheme.ProEtaleOpenRestriction.objectComposition j).obj E)))),
    ((β f j fU i sq).hom.app M).hom.hom.app (op E)
        (coprojection Λ j ((lowerStar Λ f).obj M) E s) =
      coprojection Λ i M ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ fU).obj E)
        (M.X.obj.map (sectionArrow f j fU i sq E).op s)

/-- The underlying composition map and clause (b), with the associator and geometric
transport written out. The direction is c = lowerStarComp inverse.
Source: Stacks 09A5 (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Composition : Prop :=
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : Z.ProEt),
    ((lowerStarComp Λ f g).inv.app M).hom.hom.app (op V) =
      M.X.obj.map ((MorphismProperty.Over.pullbackComp f g).inv.app V).op) ∧
  ∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    (lowerStarComp Λ f (g ≫ h)).inv ≫
        Functor.whiskerLeft (lowerStar Λ f) (lowerStarComp Λ g h).inv ≫
        (Functor.associator (lowerStar Λ f) (lowerStar Λ g) (lowerStar Λ h)).inv =
      (lowerStarCongr Λ (Category.assoc f g h)).inv ≫
        (lowerStarComp Λ (f ≫ g) h).inv ≫
        Functor.whiskerRight (lowerStarComp Λ f g).inv (lowerStar Λ h)

/-- Clause (c): successive open restrictions, with both specified pullback compositors.
Source: Stacks 00XZ and 03DH (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def SuccessiveOpens (β : Comparisons Λ) : Prop :=
  ∀ {S T U SU W SW : Scheme.{u}} (f : S ⟶ T) (j : U ⟶ T) [IsOpenImmersion j]
    (fU : SU ⟶ U) (i : SU ⟶ S) [IsOpenImmersion i] (sq : IsPullback i fU f j)
    (v : W ⟶ U) [IsOpenImmersion v] (fW : SW ⟶ W) (k : SW ⟶ SU)
    [IsOpenImmersion k] (sqW : IsPullback k fW fU v),
    (β f (v ≫ j) fW (k ≫ i) (sqW.paste_horiz sq)).hom =
      Functor.whiskerLeft (lowerStar Λ f) (upperStarComp Λ v j).hom ≫
        (Functor.associator (lowerStar Λ f) (upperStar Λ j) (upperStar Λ v)).inv ≫
        Functor.whiskerRight (β f j fU i sq).hom (upperStar Λ v) ≫
        (Functor.associator (upperStar Λ i) (lowerStar Λ fU) (upperStar Λ v)).hom ≫
        Functor.whiskerLeft (upperStar Λ i) (β fU v fW k sqW).hom ≫
        (Functor.associator (upperStar Λ i) (upperStar Λ k) (lowerStar Λ fW)).inv ≫
        Functor.whiskerRight (upperStarComp Λ k i).inv (lowerStar Λ fW)

/-- Clause (d): mixed composition/open pasting, with its source and target compositors.
Cartesian-square representatives keep all fibre-product identifications explicit.
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def MixedPasting (β : Comparisons Λ) : Prop :=
  ∀ {X Y T U YU XU : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ T)
    (j : U ⟶ T) [IsOpenImmersion j] (gU : YU ⟶ U) (jY : YU ⟶ Y)
    [IsOpenImmersion jY] (sqG : IsPullback jY gU g j)
    (fU : XU ⟶ YU) (jX : XU ⟶ X) [IsOpenImmersion jX]
    (sqF : IsPullback jX fU f jY),
    Functor.whiskerRight (lowerStarComp Λ f g).inv (upperStar Λ j) ≫
        (Functor.associator (lowerStar Λ f) (lowerStar Λ g) (upperStar Λ j)).hom ≫
        Functor.whiskerLeft (lowerStar Λ f) (β g j gU jY sqG).hom ≫
        (Functor.associator (lowerStar Λ f) (upperStar Λ jY) (lowerStar Λ gU)).inv ≫
        Functor.whiskerRight (β f jY fU jX sqF).hom (lowerStar Λ gU) ≫
        (Functor.associator (upperStar Λ jX) (lowerStar Λ fU) (lowerStar Λ gU)).hom =
      (β (f ≫ g) j (fU ≫ gU) jX (sqF.paste_vert sqG)).hom ≫
        Functor.whiskerLeft (upperStar Λ jX) (lowerStarComp Λ fU gU).inv

/-- Identity-open, identity-morphism, and composition unit normalizations.
Source: Stacks 09A5 and 00XZ (blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Units (β : Comparisons Λ) : Prop :=
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (sq : IsPullback (𝟙 X) f f (𝟙 Y)),
    (β f (𝟙 Y) f (𝟙 X) sq).hom ≫
        Functor.whiskerRight (upperStarId Λ X).hom (lowerStar Λ f) ≫
        (Functor.leftUnitor (lowerStar Λ f)).hom =
      Functor.whiskerLeft (lowerStar Λ f) (upperStarId Λ Y).hom ≫
        (Functor.rightUnitor (lowerStar Λ f)).hom) ∧
  (∀ {Y U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (sq : IsPullback j (𝟙 U) (𝟙 Y) j),
    (β (𝟙 Y) j (𝟙 U) j sq).hom ≫
        Functor.whiskerLeft (upperStar Λ j) (lowerStarId Λ U).hom ≫
        (Functor.rightUnitor (upperStar Λ j)).hom =
      Functor.whiskerRight (lowerStarId Λ Y).hom (upperStar Λ j) ≫
        (Functor.leftUnitor (upperStar Λ j)).hom) ∧
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    lowerStarComp Λ (𝟙 X) f =
      Functor.isoWhiskerRight (lowerStarId Λ X) (lowerStar Λ f) ≪≫
        Functor.leftUnitor (lowerStar Λ f) ≪≫
        (lowerStarCongr Λ (Category.id_comp f)).symm) ∧
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    lowerStarComp Λ f (𝟙 Y) =
      Functor.isoWhiskerLeft (lowerStar Λ f) (lowerStarId Λ Y) ≪≫
        Functor.rightUnitor (lowerStar Λ f) ≪≫
        (lowerStarCongr Λ (Category.comp_id f)).symm

/-- The comparisons commute with every differential of every cochain complex. Since the
preceding equations quantify over every module, they also hold in every degree.
Source: blueprint Canonicity and associativity
(blueprint: lem-sfb-module-direct-image-open-pasting). -/
def Degreewise (β : Comparisons Λ) : Prop :=
  (∀ {X Y U P : Scheme.{u}} (f : X ⟶ Y) (j : U ⟶ Y) [IsOpenImmersion j]
    (fU : P ⟶ U) (i : P ⟶ X) [IsOpenImmersion i] (sq : IsPullback i fU f j)
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (n m : ℤ),
    (lowerStar Λ f ⋙ upperStar Λ j).map (K.d n m) ≫
        (β f j fU i sq).hom.app (K.X m) =
      (β f j fU i sq).hom.app (K.X n) ≫
        (upperStar Λ i ⋙ lowerStar Λ fU).map (K.d n m)) ∧
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    (n m : ℤ),
    (lowerStar Λ (f ≫ g)).map (K.d n m) ≫ (lowerStarComp Λ f g).inv.app (K.X m) =
      (lowerStarComp Λ f g).inv.app (K.X n) ≫
        (lowerStar Λ f ⋙ lowerStar Λ g).map (K.d n m)

/-- Sectionwise normalized module comparisons satisfy all direct-image/open pasting laws.
Source: blueprint `sk-thm-sf-comp-composition`, Composition isomorphism and Canonicity
and associativity; Stacks 09A5, 00XZ, 03D3, 03D6, 03DH
(blueprint: lem-sfb-module-direct-image-open-pasting).

Proof plan (the node's eleven steps):
1. Use sheaf tensor structure and section-ring lax-pushforward coherence to identify the
internal direct image with sectionwise restriction through eta. The faithful forgetful
functor checks equalities and uniqueness of module lifts on all sections.
2. Take the inverse of the specified module lowerStarComp; its underlying map is the
canonical fibre-product reindexing, natural in both the site object and module.
3. Identify open inverse image with slice restriction. The Lan/sheafification adjunction
unit at the distinguished graph object is identity in slice coordinates. Thus eta_j is
alpha_j; extension along alpha_j is action transport by its inverse.
4. Apply eta-comp to the open cartesian square. On sections b eta_f = eta_fU a, so
eta_f(a inverse(r)) = b inverse(eta_fU(r)); the canonical comparison is linear.
5. Apply proEtaleOpenRestrictionCounit over actual inverse-image rings and transport
coefficients. Step 4 makes its normalized section comparison a module isomorphism;
the inverse of a bijective linear map is linear too. This gives Sectionwise.
6. For Composition, both triple-composition maps have identical projections to X and
the test object, hence agree by the pullback universal property and sheaf functoriality.
7. The specified upperStarComp is identity in open-slice coordinates: eta-comp gives
alpha_jv = alpha_v alpha_j, and the scalar-extension comparison preserves tensor units;
the conjugation bijection fixes it uniquely.
8. For SuccessiveOpens, compare the direct fibre-product arrow with its two-step version.
Their two projections agree, so their section maps and module maps agree.
9. For MixedPasting, the two paths from the iterated pulled-back object have the same
projections to X and the test object; use the same uniqueness and faithfulness argument.
10. Eta-id gives the original action for identity pushforward. Steps 3 and 5 identify
the identity-open comparison with identity. The projection calculation also gives the
composition unit laws; empty opens and the empty scheme require no exception.
11. Apply naturality to each differential K.d n m. The resulting maps and their inverses
are cochain maps, and all equations hold in each degree. No localization is used. -/
theorem moduleDirectImageOpenPasting :
    ∃ β : Comparisons Λ, Sectionwise Λ β ∧ Composition Λ ∧ SuccessiveOpens Λ β ∧
      MixedPasting Λ β ∧ Units Λ β ∧ Degreewise Λ β := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting
