/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Thickening

/-! # Square-zero ringed extension data on algebraic spaces

Source: Stacks Project, Tags 05ZS, 05ZT and 05ZN
(blueprint: def-sfb-space-square-zero-extension-data).

Ring maps are expressed on all compatible pairs of scheme charts, with naturality
in both charts. This is the chart description of a map from the inverse-image
ring sheaf; in particular it does not replace inverse image by tensor pullback.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Forget to schemes over the original base. Source: Stacks, Tag 03ED
(blueprint: def-sfb-space-square-zero-extension-data). -/
abbrev chartOver {S : Scheme.{u}} (X : AlgebraicSpace S) : X.EtaleSite ⥤ Over S :=
  ObjectProperty.ι _ ⋙ CostructuredArrow.proj yoneda X.obj.obj

/-- A ring-sheaf map on the inverse image along `f`, expressed on all scheme
charts and commuting chart squares. Source: Stacks, Tags 03G8 and 05ZN
(blueprint: def-sfb-space-square-zero-extension-data). -/
structure ChartRingMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : Y.EtaleSiteᵒᵖ ⥤ RingCat.{u}) (D : X.EtaleSiteᵒᵖ ⥤ RingCat.{u}) where
  app (U : X.EtaleSite) (V : Y.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom) :
    A.obj (op V) ⟶ D.obj (op U)
  naturality (U U₁ : X.EtaleSite) (V V₁ : Y.EtaleSite)
    (a : U.obj.left ⟶ V.obj.left) (b : U₁.obj.left ⟶ V₁.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom)
    (hb : U₁.obj.hom ≫ f.hom.hom = yoneda.map b ≫ V₁.obj.hom)
    (c : U₁ ⟶ U) (d : V₁ ⟶ V)
    (h : (chartOver X).map c ≫ a = b ≫ (chartOver Y).map d) :
    A.map d.op ≫ app U₁ V₁ b hb = app U V a ha ≫ D.map c.op

/-- Square-zero closed immersion on every scheme test, using the existing scheme
predicate. Such immersions induce homeomorphisms since their kernels are nilpotent.
Source: Stacks, Tag 04EX and Tag 05ZT
(blueprint: def-sfb-space-square-zero-extension-data). -/
def IsSpaceFirstOrderThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') : Prop :=
  IsRepresentableWith (fun _ _ p ↦ IsFirstOrderThickening p.left) i.hom.hom

/-- A normalized lift of the small étale site through a thickening. The reduction
arrows exhibit actual scheme pullback squares; the quotient map on rings is the
pullback of regular functions along those same arrows. Source: Stacks, Tag 05ZS
(blueprint: def-sfb-space-square-zero-extension-data). -/
structure ThickeningSiteModel {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') where
  equivalence : X'.EtaleSite ≌ X.EtaleSite
  reduction : chartOver X ⟶ equivalence.inverse ⋙ chartOver X'
  cartesian (U : X.EtaleSite) :
    IsPullback U.obj.hom (yoneda.map (reduction.app U)) i.hom.hom
      (equivalence.inverse.obj U).obj.hom
  continuous : Functor.IsContinuous equivalence.functor X'.etaleTopology X.etaleTopology
  inverse_continuous :
    Functor.IsContinuous equivalence.inverse X.etaleTopology X'.etaleTopology
  quotient : equivalence.inverse.op ⋙ X'.structurePresheaf ⟶ X.structurePresheaf
  quotient_app (U : X.EtaleSite) : quotient.app (op U) =
    (forget₂ CommRingCat RingCat).map (Scheme.Γ.map (reduction.app U).left.op)

/-- The ring presheaf of the thickened space on the identified reduced site.
Source: Stacks, Tags 05ZS and 05ZT
(blueprint: def-sfb-space-square-zero-extension-data). -/
abbrev ThickeningSiteModel.rings {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {i : X ⟶ X'} (T : ThickeningSiteModel i) : X.EtaleSiteᵒᵖ ⥤ RingCat.{u} :=
  T.equivalence.inverse.op ⋙ X'.structurePresheaf

/-- A thickening over `B` with its normalized site model and base ring action.
The latter is prescribed by actual lifts to every étale `B`-chart, rather than
by an arbitrary algebra map. Source: Stacks, Tags 05ZS and 05ZN
(blueprint: def-sfb-space-square-zero-extension-data). -/
structure ThickeningOverModel {S : Scheme.{u}} {X X' B : AlgebraicSpace S}
    (f : X ⟶ B) (i : X ⟶ X') (q : X' ⟶ B) extends ThickeningSiteModel i where
  base : ChartRingMap f B.structurePresheaf toThickeningSiteModel.rings
  base_normalization (U : X.EtaleSite) (V : B.EtaleSite)
    (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom) :
    ∃ r : (equivalence.inverse.obj U).obj.left ⟶ V.obj.left,
      reduction.app U ≫ r = a ∧
      (equivalence.inverse.obj U).obj.hom ≫ q.hom.hom = yoneda.map r ≫ V.obj.hom ∧
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map r.left.op) = base.app U V a ha

/-- A square-zero extension of the structure sheaf with its specified kernel and
base algebra structure. Exactness at the quotient is LOCAL surjectivity.
The equation `scalar` is the prescribed quotient action on the kernel.
Source: Stacks, Tag 05ZT (blueprint: def-sfb-space-square-zero-extension-data). -/
structure SpaceSquareZeroExtension {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (G : X.Modules) where
  algebra : Sheaf X.etaleTopology RingCat.{u}
  commutative (U : X.EtaleSite) (a b : algebra.obj.obj (op U)) : a * b = b * a
  quotient : algebra.obj ⟶ X.structurePresheaf
  inclusion (U : X.EtaleSite) : G.val.obj (op U) →+ algebra.obj.obj (op U)
  inclusion_naturality {U V : X.EtaleSite} (a : U ⟶ V) (m : G.val.obj (op V)) :
    algebra.obj.map a.op (inclusion V m) = inclusion U (G.val.map a.op m)
  injective (U : X.EtaleSite) : Function.Injective (inclusion U)
  kernel (U : X.EtaleSite) (a : algebra.obj.obj (op U)) :
    quotient.app (op U) a = 0 ↔ ∃ m : G.val.obj (op U), inclusion U m = a
  locally_surjective (U : X.EtaleSite) (a : X.structurePresheaf.obj (op U)) :
    ∃ R : Sieve U, R ∈ X.etaleTopology U ∧
      ∀ (V : X.EtaleSite) (v : V ⟶ U), R v →
        ∃ b : algebra.obj.obj (op V), quotient.app (op V) b = X.structurePresheaf.map v.op a
  square_zero (U : X.EtaleSite) (m n : G.val.obj (op U)) :
    inclusion U m * inclusion U n = 0
  scalar (U : X.EtaleSite) (a : algebra.obj.obj (op U)) (m : G.val.obj (op U)) :
    inclusion U (quotient.app (op U) a • m) = a * inclusion U m
  base : ChartRingMap f B.structurePresheaf algebra.obj
  base_quotient (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom) :
    base.app U V a ha ≫ quotient.app (op U) =
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map a.left.op)

/-- The reduction condition on a map of extension ring sheaves along an arbitrary
reduced morphism. Source: Stacks, Tag 05ZN
(blueprint: def-sfb-space-square-zero-extension-data). -/
def ChartRingMap.Reduces {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {j : Y ⟶ Y'} (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
    {g : X ⟶ Y} (α : ChartRingMap g W.rings T.rings) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ g.hom.hom = yoneda.map a ≫ V.obj.hom),
    α.app U V a ha ≫ T.quotient.app (op U) = W.quotient.app (op V) ≫
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map a.left.op)

/-- Compatibility of a ring map with the base algebra structures, checked on every
composable triple of charts. Source: Stacks, Tag 05ZN
(blueprint: def-sfb-space-square-zero-extension-data). -/
def ChartRingMap.OverBase {S : Scheme.{u}} {X Y X' Y' B : AlgebraicSpace S}
    {i : X ⟶ X'} {j : Y ⟶ Y'} {f : X ⟶ B} {h : Y ⟶ B}
    {q : X' ⟶ B} {r : Y' ⟶ B}
    (T : ThickeningOverModel f i q) (W : ThickeningOverModel h j r)
    {g : X ⟶ Y} (α : ChartRingMap g W.toThickeningSiteModel.rings
      T.toThickeningSiteModel.rings) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (Z : B.EtaleSite)
    (a : U.obj.left ⟶ V.obj.left) (b : V.obj.left ⟶ Z.obj.left)
    (c : U.obj.left ⟶ Z.obj.left)
    (ha : U.obj.hom ≫ g.hom.hom = yoneda.map a ≫ V.obj.hom)
    (hb : V.obj.hom ≫ h.hom.hom = yoneda.map b ≫ Z.obj.hom)
    (hc : U.obj.hom ≫ f.hom.hom = yoneda.map c ≫ Z.obj.hom),
    a ≫ b = c → W.base.app V Z b hb ≫ α.app U V a ha = T.base.app U Z c hc

/-- The map on the thickened ring sheaves is the pullback of regular functions
along actual maps of lifted chart schemes. Source: Stacks, Tag 05ZN
(blueprint: def-sfb-space-square-zero-extension-data). -/
def ChartRingMap.InducedBy {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {j : Y ⟶ Y'} (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
    {g : X ⟶ Y} (α : ChartRingMap g W.rings T.rings) (g' : X' ⟶ Y') : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
    (ha : U.obj.hom ≫ g.hom.hom = yoneda.map a ≫ V.obj.hom),
    ∃ a' : (T.equivalence.inverse.obj U).obj.left ⟶ (W.equivalence.inverse.obj V).obj.left,
      T.reduction.app U ≫ a' = a ≫ W.reduction.app V ∧
      (T.equivalence.inverse.obj U).obj.hom ≫ g'.hom.hom =
        yoneda.map a' ≫ (W.equivalence.inverse.obj V).obj.hom ∧
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map a'.left.op) = α.app U V a ha

/-- The ring isomorphism induced by an isomorphism between two thickenings of the
same reduced space, on every lifted chart. Source: Stacks, Tags 05ZT and 05ZN
(blueprint: def-sfb-space-square-zero-extension-data). -/
def ThickeningSiteModel.InducesIso {S : Scheme.{u}} {X X' Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {j : X ⟶ Y'} (T : ThickeningSiteModel i) (W : ThickeningSiteModel j)
    (θ : W.rings ≅ T.rings) (e : X' ≅ Y') : Prop :=
  ∀ U : X.EtaleSite,
    ∃ a : (T.equivalence.inverse.obj U).obj.left ⟶ (W.equivalence.inverse.obj U).obj.left,
      T.reduction.app U ≫ a = W.reduction.app U ∧
      (T.equivalence.inverse.obj U).obj.hom ≫ e.hom.hom.hom =
        yoneda.map a ≫ (W.equivalence.inverse.obj U).obj.hom ∧
      (forget₂ CommRingCat RingCat).map (Scheme.Γ.map a.left.op) = θ.hom.app (op U)

end AlgebraicGeometry.AlgebraicSpace
