/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.TotallyDisconnectedCoefficientRealization
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Right torsors under continuous-function coefficients

Source: Bhatt--Scholze, Section 7.1 and proof of Lemma 7.4.7
(blueprint: def-sfb-continuous-right-torsor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite Topology
namespace AlgebraicGeometry.ProEtale

/-- A normal connected Noetherian pointed base, with a small fundamental-group model.
Source: Bhatt--Scholze, Lemma 7.4.10
(blueprint: def-sfb-continuous-right-torsor). -/
structure NormalTorsorBase where
  X : Scheme.{u}
  connected : ConnectedSpace X
  noetherian : IsLocallyNoetherian X
  compact : CompactSpace X
  normal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
    IsIntegrallyClosed (X.presheaf.stalk z)
  Ω : Type u
  field : Field Ω
  closed : IsAlgClosed Ω
  x : Spec (.of Ω) ⟶ X
  pi : ProfiniteGrp.{u}
  actions : ∀ V, MulAction pi ((Scheme.FiniteEtale.fiber x).obj V)
  fundamental : IsFundamentalGroup (Scheme.FiniteEtale.fiber x) pi

attribute [instance] NormalTorsorBase.connected NormalTorsorBase.noetherian
  NormalTorsorBase.compact NormalTorsorBase.field NormalTorsorBase.closed
  NormalTorsorBase.actions NormalTorsorBase.fundamental

/-- Hausdorff coefficients with open-subgroup basis, compact or two-sided complete.
The infimum is the two-sided uniformity, imposing both group differences.
Source: Bhatt--Scholze, Definition 7.1.3, Proposition 7.1.5 and Example 7.1.6
(blueprint: def-sfb-continuous-right-torsor). -/
structure TorsorCoefficientGroup where
  carrier : Type (u + 1)
  group : Group carrier
  topology : TopologicalSpace carrier
  hausdorff : T2Space carrier
  nonarchimedean : NonarchimedeanGroup carrier
  complete : CompactSpace carrier ∨
    @CompleteSpace carrier
      (IsTopologicalGroup.leftUniformSpace carrier ⊓ IsTopologicalGroup.rightUniformSpace carrier)


attribute [instance] TorsorCoefficientGroup.group TorsorCoefficientGroup.topology
  TorsorCoefficientGroup.hausdorff TorsorCoefficientGroup.nonarchimedean

/-- A sheaf with a right action, simply transitive wherever it has a section and
locally nonempty. These conditions mean locally equivariantly regular.
Source: Bhatt--Scholze, proof of Lemma 7.4.7
(blueprint: def-sfb-continuous-right-torsor). -/
structure ContinuousRightTorsor (X : Scheme.{u}) (G : TorsorCoefficientGroup.{u}) where
  sheaf : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))
  act (U : X.ProEtᵒᵖ) : sheaf.obj.obj U → C(U.unop.left, G.carrier) → sheaf.obj.obj U
  act_one : ∀ U p, act U p 1 = p
  act_mul : ∀ U p g h, act U (act U p g) h = act U p (g * h)
  natural : ∀ {U V} (f : U ⟶ V) p g,
    sheaf.obj.map f (act U p g) =
      act V (sheaf.obj.map f p) ((continuousSetPresheaf X G.carrier).map f g)
  simply_transitive : ∀ U p, Function.Bijective (act U p)
  locally_nonempty : ∀ U : X.ProEt,
    { arrows := fun V _ ↦ Nonempty (sheaf.obj.obj (op V))
      downward_closed := fun h f ↦ h.map (sheaf.obj.map f.op) } ∈ Scheme.ProEt.topology X U

namespace ContinuousRightTorsor
variable {X : Scheme.{u}} {G : TorsorCoefficientGroup.{u}}

/-- Constant right translation, a genuine natural endomorphism of the set sheaf.
Source: Bhatt--Scholze, right-torsor convention in Lemma 7.4.7
(blueprint: def-sfb-continuous-right-torsor). -/
def translate (P : ContinuousRightTorsor X G) (g : G.carrier) : P.sheaf ⟶ P.sheaf :=
  ⟨{ app := fun U ↦ ↾fun p ↦ P.act U p (ContinuousMap.const _ g)
     naturality := fun _ _ f ↦ by ext p; exact (P.natural f p (ContinuousMap.const _ g)).symm }⟩

/-- Sections after geometric inverse image, exactly the fibre used here.
Source: Bhatt--Scholze, Section 7.4 (blueprint: def-sfb-continuous-right-torsor). -/
abbrev fibre (P : ContinuousRightTorsor X G) {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ X) : Type (u + 1) :=
  ((Scheme.proEtaleSheafInverseImage x (Type (u + 1))).obj P.sheaf).obj.obj
    (op (Scheme.ProEt.mk (𝟙 _)))

/-- Right translation on the actual fibre, obtained by inverse image of translation.
Source: Bhatt--Scholze, Section 7.4 (blueprint: def-sfb-continuous-right-torsor). -/
def fibreAct (P : ContinuousRightTorsor X G) {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ X) (p : P.fibre x) (g : G.carrier) : P.fibre x :=
  (((Scheme.proEtaleSheafInverseImage x (Type (u + 1))).map (P.translate g)).hom.app
    (op (Scheme.ProEt.mk (𝟙 _)))) p

/-- An equivariant isomorphism of right torsors.
Source: Bhatt--Scholze, groupoid convention before Lemma 7.4.3
(blueprint: def-sfb-continuous-right-torsor). -/
structure Equiv (P Q : ContinuousRightTorsor X G) where
  iso : P.sheaf ≅ Q.sheaf
  equivariant : ∀ U p g, iso.hom.hom.app U (P.act U p g) =
    Q.act U (iso.hom.hom.app U p) g

/-- The induced map on sections of the geometric inverse image.
Source: Bhatt--Scholze, Section 7.4 (blueprint: def-sfb-continuous-right-torsor). -/
def Equiv.fibreMap {P Q : ContinuousRightTorsor X G} (e : P.Equiv Q)
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ X) : P.fibre x → Q.fibre x :=
  ((Scheme.proEtaleSheafInverseImage x (Type (u + 1))).map e.iso.hom).hom.app
    (op (Scheme.ProEt.mk (𝟙 _)))

/-- Restriction of a section along a field-valued point, using the inverse-image unit.
Source: Bhatt--Scholze, Section 7.4 (blueprint: def-sfb-continuous-right-torsor). -/
def sectionToFibre (P : ContinuousRightTorsor X G) {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ X) (U : X.ProEt) (t : Spec (.of K) ⟶ U.left)
    (ht : t ≫ U.hom = x) : P.sheaf.obj.obj (op U) → P.fibre x :=
  fun s ↦ ((Scheme.proEtaleSheafInverseImage x (Type (u + 1))).obj P.sheaf).obj.map
    (MorphismProperty.Over.homMk (pullback.lift t (𝟙 _) (ht.trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)).op
    (((Scheme.proEtaleSheafAdjunction x (Type (u + 1))).unit.app P.sheaf).hom.app (op U) s)

/-- A map to a torsor after base and coefficient change, written by adjunction.
Locally a section p maps to a section q and p g maps to q u(g).
Source: Bhatt--Scholze, proof of Lemma 7.4.7
(blueprint: def-sfb-continuous-right-torsor). -/
structure Along {Y : Scheme.{u}} {H : TorsorCoefficientGroup.{u}} (f : Y ⟶ X)
    (v : G.carrier →ₜ* H.carrier) (P : ContinuousRightTorsor X G)
    (Q : ContinuousRightTorsor Y H) where
  hom : P.sheaf ⟶ (Scheme.proEtaleSheafDirectImage f (Type (u + 1))).obj Q.sheaf
  equivariant : ∀ U p g, hom.hom.app U (P.act U p g) =
    Q.act (op ((Scheme.proEtaleBaseChange f).obj U.unop)) (hom.hom.app U p)
      (v.toContinuousMap.comp (g.comp (pullback.fst U.unop.hom f).base.hom))

/-- Composition comparison for the specified inverse images of set sheaves.
Source: Stacks, Tag 00VE, uniqueness of adjoints
(blueprint: def-sfb-continuous-right-torsor). -/
def setPullbackComp {Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    Scheme.proEtaleSheafInverseImage (g ≫ f) (Type (u + 1)) ≅
      Scheme.proEtaleSheafInverseImage f (Type (u + 1)) ⋙
        Scheme.proEtaleSheafInverseImage g (Type (u + 1)) :=
  ((conjugateIsoEquiv (Scheme.proEtaleSheafAdjunction (g ≫ f) (Type (u + 1)))
    ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).comp
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1))))).symm
    (Functor.sheafPushforwardContinuousComp'
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g f).symm
      (Type (u + 1)) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology Z)).symm).symm

/-- Map on actual fibres for a base and coefficient change.
Source: Bhatt--Scholze, functoriality of the fibre in Section 7.4
(blueprint: def-sfb-continuous-right-torsor). -/
def Along.fibreMap {Y : Scheme.{u}} {H : TorsorCoefficientGroup.{u}} {f : Y ⟶ X}
    {v : G.carrier →ₜ* H.carrier} {P : ContinuousRightTorsor X G}
    {Q : ContinuousRightTorsor Y H} (a : Along f v P Q) {K : Type u} [Field K]
    (y : Spec (.of K) ⟶ Y) : P.fibre (y ≫ f) → Q.fibre y :=
  ((setPullbackComp f y).hom.app P.sheaf ≫
    (Scheme.proEtaleSheafInverseImage y (Type (u + 1))).map
      (((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).homEquiv _ _).symm a.hom)).hom.app
        (op (Scheme.ProEt.mk (𝟙 _)))

/-- The universal contracted-product presentation, without choosing representatives.
The map q satisfies q(p g,h)=q(p,v(g)h) and is H-equivariant. Its universal
property ranges over all natural balanced maps to arbitrary set sheaves; no
H-action or equivariance is required on the target of the universal property.
Source: Bhatt--Scholze, proof of Lemma 7.4.7
(blueprint: def-sfb-continuous-right-torsor). -/
structure ExtensionPresentation {H : TorsorCoefficientGroup.{u}}
    (v : G.carrier →ₜ* H.carrier) (P : ContinuousRightTorsor X G)
    (Q : ContinuousRightTorsor X H) where
  quotientMap (U : X.ProEtᵒᵖ) :
    P.sheaf.obj.obj U → C(U.unop.left, H.carrier) → Q.sheaf.obj.obj U
  natural : ∀ {U V} (f : U ⟶ V) p h,
    Q.sheaf.obj.map f (quotientMap U p h) =
      quotientMap V (P.sheaf.obj.map f p) ((continuousSetPresheaf X H.carrier).map f h)
  balanced : ∀ U p g h,
    quotientMap U (P.act U p g) h = quotientMap U p (v.toContinuousMap.comp g * h)
  universal : ∀ (R : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (b : ∀ U, P.sheaf.obj.obj U → C(U.unop.left, H.carrier) → R.obj.obj U),
    (∀ {U V} (f : U ⟶ V) p h, R.obj.map f (b U p h) =
      b V (P.sheaf.obj.map f p) ((continuousSetPresheaf X H.carrier).map f h)) →
    (∀ U p g h, b U (P.act U p g) h = b U p (v.toContinuousMap.comp g * h)) →
    ∃! a : Q.sheaf ⟶ R, ∀ U p h, a.hom.app U (quotientMap U p h) = b U p h
  right_equivariant : ∀ U p h h',
    quotientMap U p (h * h') = Q.act U (quotientMap U p h) h'

/-- The canonical map p ↦ [p,1] into the extension of structural group.
Source: Bhatt--Scholze, pushout construction in Lemma 7.4.7
(blueprint: def-sfb-continuous-right-torsor). -/
def ExtensionPresentation.inclusion {H : TorsorCoefficientGroup.{u}}
    {v : G.carrier →ₜ* H.carrier} {P : ContinuousRightTorsor X G}
    {Q : ContinuousRightTorsor X H} (E : ExtensionPresentation v P Q) : P.sheaf ⟶ Q.sheaf :=
  ⟨{ app := fun U ↦ ↾fun p ↦ E.quotientMap U p 1
     naturality := fun _ _ f ↦ by ext p; exact (E.natural f p 1).symm }⟩

/-- The point [p,1] in the fibre of the extension of structural group.
Source: Bhatt--Scholze, pushout construction in Lemma 7.4.7
(blueprint: def-sfb-continuous-right-torsor). -/
def ExtensionPresentation.fibreMap {H : TorsorCoefficientGroup.{u}}
    {v : G.carrier →ₜ* H.carrier} {P : ContinuousRightTorsor X G}
    {Q : ContinuousRightTorsor X H} (E : ExtensionPresentation v P Q)
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ X) : P.fibre x → Q.fibre x :=
  ((Scheme.proEtaleSheafInverseImage x (Type (u + 1))).map E.inclusion).hom.app
    (op (Scheme.ProEt.mk (𝟙 _)))

/-- Restriction of a geometric fibre across an embedding of algebraically closed fields.
It is the section restriction given by the inverse-image unit and composition comparison.
Source: Stacks, Tag 00VE; Bhatt--Scholze, Section 7.4
(blueprint: def-sfb-continuous-right-torsor). -/
def fibreFieldRestriction (P : ContinuousRightTorsor X G) {K L : Type u}
    [Field K] [Field L] (x : Spec (.of K) ⟶ X) (i : K →+* L) :
    P.fibre x → P.fibre (Spec.map (CommRingCat.ofHom i) ≫ x) :=
  fun p ↦ ((setPullbackComp x (Spec.map (CommRingCat.ofHom i))).inv.app P.sheaf).hom.app
    (op (Scheme.ProEt.mk (𝟙 _)))
    (((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i))
      (Type (u + 1))).obj
      ((Scheme.proEtaleSheafInverseImage x (Type (u + 1))).obj P.sheaf)).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift (Spec.map (CommRingCat.ofHom i)) (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _)).op
      (((Scheme.proEtaleSheafAdjunction (Spec.map (CommRingCat.ofHom i))
        (Type (u + 1))).unit.app
          ((Scheme.proEtaleSheafInverseImage x (Type (u + 1))).obj P.sheaf)).hom.app
            (op (Scheme.ProEt.mk (𝟙 _))) p))

end ContinuousRightTorsor
end AlgebraicGeometry.ProEtale
