/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap
public import Sheaf.Paper.DerivedPullbackTensorIso
/-! # Canonical constructible projection mates
Source: projection-formula construction, proof steps 1--6
(blueprint: def-sf-constructible-projection-mates).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe u v w v' w' a b c d ha hb hc hd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The identity base-change square retaining a prescribed compactification.
Source: the chosen compactification paragraph of the projection transformation
(blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProjectionSquare {D : FiniteFieldDatum.{u}}
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) :
    SixFunctorCompactifiedSquare D where
  X := X
  Y := Y
  X' := X
  Y' := Y
  Z := ⟨Over.mk (c.g ≫ Y.obj.hom), by
    have := c.isProper
    have := Y.property.1
    have := Y.property.2
    change LocallyOfFiniteType (c.g ≫ Y.obj.hom) ∧ QuasiCompact (c.g ≫ Y.obj.hom)
    exact ⟨inferInstance, inferInstance⟩⟩
  Z' := ⟨Over.mk (c.g ≫ Y.obj.hom), by
    have := c.isProper
    have := Y.property.1
    have := Y.property.2
    change LocallyOfFiniteType (c.g ≫ Y.obj.hom) ∧ QuasiCompact (c.g ≫ Y.obj.hom)
    exact ⟨inferInstance, inferInstance⟩⟩
  f := f
  f' := f
  g := 𝟙 Y
  g' := 𝟙 X
  i := ObjectProperty.homMk (Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ Y.obj.hom) c.comm.symm).trans f.hom.w)))
  i' := ObjectProperty.homMk (Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.obj.hom = X.obj.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ Y.obj.hom) c.comm.symm).trans f.hom.w)))
  p := ObjectProperty.homMk (Over.homMk c.g)
  p' := ObjectProperty.homMk (Over.homMk c.g)
  h := 𝟙 _
  open_i := c.isOpenImmersion
  open_i' := c.isOpenImmersion
  proper_p := c.isProper
  proper_p' := c.isProper
  factorization := by ext; exact c.comm
  factorization' := by ext; exact c.comm
  square := IsPullback.of_id_fst
  properSquare := IsPullback.of_id_fst
  openSquare := IsPullback.of_id_fst
  squareComm := by simp
  properComm := by simp
  openComm := by simp

/-- Components of the specified compactification projection in operation coordinates.
Source: def-exchange-projection, the counit mate followed by open projection
(blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProjectionComponent {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : B X) (L : B Y) :
    ((T Y).obj ((S.support f c).obj K)).obj L ⟶
      (S.support f c).obj (((T X).obj K).obj ((S.pull f).obj L)) :=
  (A (compactSupportProjectionSquare f c)).projectionComponent K L

/-- Identity-open square for the proper comparison, in the original object coordinates.
Source: the proper clause (blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProperSquare {D : FiniteFieldDatum.{u}}
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left] :
    SixFunctorCompactifiedSquare D where
  X := X
  Y := Y
  X' := X
  Y' := Y
  Z := X
  Z' := X
  f := f
  f' := f
  g := 𝟙 Y
  g' := 𝟙 X
  i := 𝟙 X
  i' := 𝟙 X
  p := f
  p' := f
  h := 𝟙 X
  open_i := inferInstance
  open_i' := inferInstance
  proper_p := inferInstance
  proper_p' := inferInstance
  factorization := by simp
  factorization' := by simp
  square := IsPullback.of_id_fst
  properSquare := IsPullback.of_id_fst
  openSquare := IsPullback.of_id_fst
  squareComm := by simp
  properComm := by simp
  openComm := by simp

/-- The same counit mate for a proper map, without the open factor.
Source: proper identification clause of the projection formula
(blueprint: def-sf-constructible-projection-mates). -/
def compactSupportProperProjection {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : B X) (L : B Y) :
    ((T Y).obj ((S.direct f).obj K)).obj L ⟶
      (S.direct f).obj (((T X).obj K).obj ((S.pull f).obj L)) :=
  eqToHom (by
    simp only [(A (compactSupportProperSquare f)).tensorY,
      (A (compactSupportProperSquare f)).properPush]
    rfl) ≫
  (((A (compactSupportProperSquare f)).stage.properAdjunction.rightAdjointProjectionMap
    (A (compactSupportProperSquare f)).stage.tensorPullback.hom).app K).app L ≫
  eqToHom (by
    simp only [(A (compactSupportProperSquare f)).tensorBar,
      (A (compactSupportProperSquare f)).properPush,
      (A (compactSupportProperSquare f)).properPull]
    rfl)

/-- All coherence clauses on the indicated second-input domain. The family is the
specified mate, not an existential family of arrows. The pentagon is expressed as the
component equation between the two threefold compositors, with equality transport of the
composite compactification. No separatedness of the structure maps is imposed.
Source: projection-formula statement and proof steps 7--13
(blueprint: def-sf-constructible-projection-mates). -/
structure CompactSupportProjectionLaws {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ X, ObjectProperty (B X)) : Prop where
  isIso : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
      IsIso (compactSupportProjectionComponent A f c K L)
  naturality : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) {K K' : B X} {L L' : B Y},
    P Y L → P Y L' → ∀ (a : K ⟶ K') (b : L ⟶ L'),
      ((T Y).map ((S.support f c).map a)).app L ≫
          ((T Y).obj ((S.support f c).obj K')).map b ≫
          compactSupportProjectionComponent A f c K' L' =
        compactSupportProjectionComponent A f c K L ≫
          (S.support f c).map
            (((T X).map a).app ((S.pull f).obj L) ≫
              ((T X).obj K').map ((S.pull f).map b))
  compactification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
      ((T Y).map ((S.comparison f c d).hom.app K)).app L ≫
          compactSupportProjectionComponent A f d K L =
        compactSupportProjectionComponent A f c K L ≫
          (S.comparison f c d).hom.app (((T X).obj K).obj ((S.pull f).obj L))
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z), P Z L →
      ((T Z).map ((S.composition f g cf cg cfg).hom.app K)).app L ≫
          compactSupportProjectionComponent A g cg ((S.support f cf).obj K) L ≫
          (S.support g cg).map
            (compactSupportProjectionComponent A f cf K ((S.pull g).obj L)) =
        compactSupportProjectionComponent A (f ≫ g) cfg K L ≫
          (S.composition f g cf cg cfg).hom.app
            (((T X).obj K).obj ((S.pull (f ≫ g)).obj L)) ≫
          (S.support g cg).map ((S.support f cf).map
            (((T X).obj K).map ((S.pullComposition f g).hom.app L)))
  pentagon : ∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B X),
    HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))
  proper : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
      ((T Y).map ((S.properIdentification f c).hom.app K)).app L ≫
          compactSupportProperProjection A f K L =
        compactSupportProjectionComponent A f c K L ≫
          (S.properIdentification f c).hom.app
            (((T X).obj K).obj ((S.pull f).obj L))

/-- Tensoring a comparison in the first slot, then applying a realization.
Source: coefficient transport of projection (blueprint: def-sf-constructible-projection-mates). -/
def projectionTensorLeftRealization {A : Type v} [Category.{w} A]
    {B : Type v'} [Category.{w'} B] (T : A ⥤ A ⥤ A) (V : A ⥤ B)
    {K K' : A} (e : K ≅ K') (L : A) :
    V.obj ((T.obj K).obj L) ≅ V.obj ((T.obj K').obj L) :=
  V.mapIso ((T.mapIso e).app L)

/-- Cancel the inner coefficient unit, tensor a pullback comparison, and apply
compact support and realization. Source: finite projection
(blueprint: def-sf-constructible-projection-mates). -/
def projectionTensorTargetRealization
    {A : Type a} [Category.{ha} A] {B : Type b} [Category.{hb} B]
    {C : Type c} [Category.{hc} C] {D : Type d} [Category.{hd} D]
    (R : A ≌ B) (V : C ⥤ D) (F : A ⥤ C) (T : A ⥤ A ⥤ A)
    (K : A) {L : B} {L' : A} (e : R.inverse.obj L ≅ L') :
    V.obj (F.obj (R.inverse.obj (R.functor.obj ((T.obj K).obj (R.inverse.obj L))))) ≅
      V.obj (F.obj ((T.obj K).obj L')) :=
  V.mapIso (F.mapIso ((R.unitIso.app _).symm ≪≫ (T.obj K).mapIso e))

/-- Conjugation of an ambient arrow, lifted through a full subcategory.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def projectionFullConjugate {A : Type v} [Category.{w} A] {P : ObjectProperty A}
    {K L : P.FullSubcategory} {U V : A} (e : K.obj ≅ U) (e' : L.obj ≅ V)
    (a : U ⟶ V) : K ⟶ L :=
  ObjectProperty.homMk (e.hom ≫ a ≫ e'.inv)

namespace CompactSupportFiniteProjection
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorFiniteOperations D C E n hn)

/-- The canonical derived coefficient realization, with the positive exponent retained.
Source: the finite clause (blueprint: def-sf-constructible-projection-mates). -/
def realization (X : SixFunctorSpace D) :
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ≌
        proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) :=
  sixFunctorFiniteRealization D C E n hn X

/-- The recorded fixed-scalar tensor with its derived-category type exposed.
Source: finite tensor convention (blueprint: def-sf-constructible-projection-mates). -/
def fixedTensor (X : SixFunctorSpace D) :
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) :=
  AlgebraicGeometry.ProEtale.derivedTensor
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) X.obj.left

/-- The K-flat left-derived inverse image, with a fixed exposed category type.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedDerivedPull {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) ⥤
    DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))) :=
  (AlgebraicGeometry.ProEtale.upperStar
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
    f.hom.left).leftDerivedFunctor

/-- The published normalization of K-flat inverse image by exact inverse image.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedPullComparison {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    fixedDerivedPull (C := C) (E := E) (n := n) f ≅
      sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) f.hom.left :=
  AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) f.hom.left

/-- The existing proper/open projection in a compact exposed signature.
Source: def-exchange-projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedComponent {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (L : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    ((fixedTensor (C := C) (E := E) (n := n) Y).obj
      ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj K)).obj L ⟶
    (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
      (((fixedTensor (C := C) (E := E) (n := n) X).obj K).obj
        ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj L)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ((AlgebraicGeometry.ProEtale.projectionMapOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) c).app K).app L

/-- The finite signed derived tensor, transported through the published coefficient
realization. This is a change of presentation of the existing tensor.
Source: the finite projection display (blueprint: def-sf-constructible-projection-mates). -/
def tensor (X : SixFunctorSpace D) :
    proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) ⥤
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) ⥤
        proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E n) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (Functor.postcompose₂.obj (realization (C := C) (E := E) (n := n) (hn := hn) X).functor).obj
    ((((Functor.whiskeringLeft₂ _).obj
      (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse).obj
      (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse).obj
      (fixedTensor (C := C) (E := E) (n := n) X))

/-- Exactly the typing facts for the partial finite tensor and finite-Tor pullback.
There is no finite-Tor assumption on the first input.
Source: the domains of the projection formula (blueprint: def-sf-constructible-projection-mates).
Proof (postponed): use the finite constructible etale-origin equivalence and its
Tor comparison. On etale representatives, tensor with a bounded flat model of the
second input preserves bounded constructibility. Exact inverse image preserves the
same flat interval. Transport through the canonical coefficient equivalence and
finitePullback. These assertions involve all representatives and all morphisms. -/
theorem domains :
    (∀ (X : SixFunctorSpace D) (K : sixFunctorFiniteCategory D C E n hn X)
      (L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
      intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left
        (((tensor (C := C) (E := E) (n := n) (hn := hn) X).obj K.obj).obj L.obj)) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      finiteTorConstructible C.l E n hn X.obj.left ((S.finite.pull f).obj
        ⟨L.obj, L.property.1⟩).obj) := by
  sorry

/-- The partial tensor on its full first and finite-Tor second domains.
Source: the finite coefficient clause (blueprint: def-sf-constructible-projection-mates). -/
def partialTensor (X : SixFunctorSpace D) :
    sixFunctorFiniteCategory D C E n hn X ⥤
      finiteTorConstructibleCategory C.l E n hn X.obj.left ⥤
        sixFunctorFiniteCategory D C E n hn X :=
  Functor.currying.inverse.obj
    ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).lift
      ((((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι).prod
        (finiteTorConstructible C.l E n hn X.obj.left).ι) ⋙
          Functor.uncurry.obj (tensor (C := C) (E := E) (n := n) (hn := hn) X))
      (fun KL ↦ (domains S).1 X KL.1 KL.2))

/-- The restriction of the recorded inverse image to finite-Tor inputs.
Source: the finite coefficient clause (blueprint: def-sf-constructible-projection-mates). -/
def torPull {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    finiteTorConstructibleCategory C.l E n hn Y.obj.left ⥤
      finiteTorConstructibleCategory C.l E n hn X.obj.left :=
  (finiteTorConstructible C.l E n hn X.obj.left).lift
    ((ObjectProperty.ιOfLE (show finiteTorConstructible C.l E n hn Y.obj.left ≤
      intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left from fun _ h ↦ h.1)) ⋙
        S.finite.pull f ⋙ (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι)
    (fun L ↦ (domains S).2 f L)

/-- The prescribed support realization, including cancellation of the coefficient
unit. Thus no free comparison of support functors is introduced.
Source: finite compactification construction (blueprint: def-sf-constructible-projection-mates). -/
def supportRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X) :
    ((S.finite.support f c).obj K).obj ≅
      (realization (C := C) (E := E) (n := n) (hn := hn) Y).functor.obj
        ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
          ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (S.finiteSupport f c).app K ≪≫
    (sixFunctorFiniteSupport D C E n hn f c).mapIso
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).counitIso.app K.obj).symm ≪≫
    (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) c).app
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)

/-- Canonical cancellation of the coefficient equivalence in inverse image.
Source: finite pullback construction (blueprint: def-sf-constructible-projection-mates). -/
def pullRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sixFunctorFiniteCategory D C E n hn Y) :
    ((S.finite.pull f).obj L).obj ≅
      (realization (C := C) (E := E) (n := n) (hn := hn) X).functor.obj
        ((sfFixedDerivedPullback (Padic.coefficientExtensionRing C.l E n) f.hom.left).obj
          ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  (S.finitePullback f).app L ≪≫
    ((Functor.mapDerivedCategoryCompIso
      (sfIntrinsicModuleEquivalence Y.obj.left (Padic.coefficientExtensionRing C.l E n)).inverse
      (AlgebraicGeometry.ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
          f.hom.left ⋙
        (sfIntrinsicModuleEquivalence X.obj.left
          (Padic.coefficientExtensionRing C.l E n)).functor)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)).app L.obj

/-- Support realization in fixed-scalar coordinates, cancelling the unit before
applying tensor. Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedSupportRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X) :
    (realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj
      ((S.finite.support f c).obj K).obj ≅
    (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
      ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  RY.inverse.mapIso (supportRealization S f c K) ≪≫
    (RY.unitIso.app ((sfFixedCompactSupport
      (Padic.coefficientExtensionRing C.l E n) c).obj (RX.inverse.obj K.obj))).symm

/-- Tensor the fixed support comparison and realize it back. Source: finite projection
(blueprint: def-sf-constructible-projection-mates). -/
def sourceComparison {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  projectionTensorLeftRealization TY RY.functor
    (fixedSupportRealization S f c K) (RY.inverse.obj L.obj)

/-- Pullback in fixed-scalar coordinates, with the coefficient unit cancelled.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def fixedPullRealization {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sixFunctorFiniteCategory D C E n hn Y) :
    (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj
      ((S.finite.pull f).obj L).obj ≅
    (fixedDerivedPull (C := C) (E := E) (n := n) f).obj
      ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  RX.inverse.mapIso (pullRealization S f L) ≪≫
    (RX.unitIso.app ((sfFixedDerivedPullback
      (Padic.coefficientExtensionRing C.l E n) f.hom.left).obj
        (RY.inverse.obj L.obj))).symm ≪≫
    (fixedPullComparison (C := C) (E := E) (n := n) f).symm.app (RY.inverse.obj L.obj)

/-- Target realization of the finite partial tensor projection.
Source: finite projection (blueprint: def-sf-constructible-projection-mates). -/
def targetComparison {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c
  supportRealization S f c (((partialTensor S X).obj K).obj ((torPull S f).obj L)) ≪≫
    projectionTensorTargetRealization RX RY.functor F TX (RX.inverse.obj K.obj)
      (fixedPullRealization S f ⟨L.obj, L.property.1⟩)

/-- The finite projection on the full bounded constructible first domain. The
published proper-counit/open projection is conjugated only by the explicit source
and target comparisons above, then lifted through the full inclusion.
Source: the finite projection display (blueprint: def-sf-constructible-projection-mates). -/
def component {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    ((partialTensor S Y).obj ((S.finite.support f c).obj K)).obj L ⟶
      (S.finite.support f c).obj
        (((partialTensor S X).obj K).obj ((torPull S f).obj L)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  projectionFullConjugate (sourceComparison S f c K L) (targetComparison S f c K L)
    ((realization (C := C) (E := E) (n := n) (hn := hn) Y).functor.map
      (fixedComponent (C := C) (E := E) (n := n) (hn := hn) f c
        ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj)
        ((realization (C := C) (E := E) (n := n) (hn := hn) Y).inverse.obj L.obj)))

/-- The restricted pullback compositor is the recorded compositor, lifted through
its full finite-Tor inclusion. Source: composition clause
(blueprint: def-sf-constructible-projection-mates). -/
def torPullComposition {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    (torPull S (f ≫ g)).obj L ≅ (torPull S f).obj ((torPull S g).obj L) :=
  ObjectProperty.isoMk _
    ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.mapIso
      ((S.finite.pullComposition f g).app ⟨L.obj, L.property.1⟩))

/-- The proper counit projection in these coordinates. The identity-open
compactification cancels via the specified proper identification.
Source: proper clause (blueprint: def-sf-constructible-projection-mates). -/
def properComponent {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    ((partialTensor S Y).obj ((S.finite.direct f).obj K)).obj L ⟶
      (S.finite.direct f).obj (((partialTensor S X).obj K).obj ((torPull S f).obj L)) :=
  ((partialTensor S Y).map ((S.finite.properIdentity f).inv.app K)).app L ≫
    component S f (.ofIsProper f.hom.left) K L ≫
    (S.finite.properIdentity f).hom.app
      (((partialTensor S X).obj K).obj ((torPull S f).obj L))

/-- Finite projection coherence on the full first and finite-Tor second domains.
Every arrow is the explicit canonical component above. Source: finite coefficient
and coherence clauses (blueprint: def-sf-constructible-projection-mates). -/
structure Laws : Prop where
  isIso : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      IsIso (component S f c K L)
  naturality : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) {K K' : sixFunctorFiniteCategory D C E n hn X}
    {L L' : finiteTorConstructibleCategory C.l E n hn Y.obj.left},
    ∀ (a : K ⟶ K') (b : L ⟶ L'),
      ((partialTensor S Y).map ((S.finite.support f c).map a)).app L ≫
          ((partialTensor S Y).obj ((S.finite.support f c).obj K')).map b ≫
          component S f c K' L' =
        component S f c K L ≫
          (S.finite.support f c).map
            (((partialTensor S X).map a).app ((torPull S f).obj L) ≫
              ((partialTensor S X).obj K').map ((torPull S f).map b))
  compactification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      ((partialTensor S Y).map ((S.finite.comparison f c d).hom.app K)).app L ≫
          component S f d K L =
        component S f c K L ≫
          (S.finite.comparison f c d).hom.app
            (((partialTensor S X).obj K).obj ((torPull S f).obj L))
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left),
      ((partialTensor S Z).map ((S.finite.composition f g cf cg cfg).hom.app K)).app L ≫
          component S g cg ((S.finite.support f cf).obj K) L ≫
          (S.finite.support g cg).map
            (component S f cf K ((torPull S g).obj L)) =
        component S (f ≫ g) cfg K L ≫
          (S.finite.composition f g cf cg cfg).hom.app
            (((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)) ≫
          (S.finite.support g cg).map ((S.finite.support f cf).map
            (((partialTensor S X).obj K).map (torPullComposition S f g L).hom))
  pentagon : ∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : sixFunctorFiniteCategory D C E n hn X),
    HEq ((S.finite.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.finite.support h ch).map ((S.finite.composition f g cf cg cfg).hom.app K))
      ((S.finite.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.finite.composition g h cg ch cgh).hom.app ((S.finite.support f cf).obj K))
  proper : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      ((partialTensor S Y).map ((S.finite.properIdentification f c).hom.app K)).app L ≫
          properComponent S f K L =
        component S f c K L ≫
          (S.finite.properIdentification f c).hom.app
            (((partialTensor S X).obj K).obj ((torPull S f).obj L))

end CompactSupportFiniteProjection
end WeilConjectures
