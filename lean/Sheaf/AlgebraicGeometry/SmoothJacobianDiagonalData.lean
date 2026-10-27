module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import WeilConjectures.AlgebraicGeometry.Picard.DegreeMorphism
public import WeilConjectures.AlgebraicGeometry.Hilbert.Defs
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Smooth Jacobian diagonal data

Source: Deligne, Le lemme de Gabber, Section 4.1, pp.141--142; Milne,
Jacobian Varieties, Sections 5--6
(blueprint: def-sfb-smooth-jacobian-diagonal-data).

All bases over a fixed ambient scheme are retained. Thus arbitrary base-change
comparisons live in one category of algebraic spaces and use the published tensor
pullback and its normalized compositors. Theta is specified by the scheme-theoretic
Abel image on all scheme tests, including nonreduced tests.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.AlgebraicSpace.JacobianDiagonal
open Poincare

/-- The degree-zero Picard functor, viewed over an ambient scheme: a section consists
of its map to the actual base and its relative degree-zero class.
Source: relative Picard functor; Stacks 03I4--03I5
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def totalPicardZero {S : Scheme.{u}} {T : Over S} {C : Scheme.{u}} (f : C ⟶ T.left)
    [IsProper f] [LocallyOfFinitePresentation f] : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj R := Σ a : R.unop ⟶ T,
    (picardDegreeSubfunctor f 0).toFunctor.obj (op (Over.mk a.left))
  map {R R'} b := ↾fun x ↦ ⟨b.unop ≫ x.1,
    (picardDegreeSubfunctor f 0).toFunctor.map
      (Over.homMk b.unop.left rfl : Over.mk (b.unop.left ≫ x.1.left) ⟶
        Over.mk x.1.left).op x.2⟩
  map_id R := by
    apply ConcreteCategory.hom_ext _ _
    rintro ⟨a, x⟩
    dsimp
    congr 1
    change (picardDegreeSubfunctor f 0).toFunctor.map (𝟙 _) x = x
    simp
  map_comp b c := by
    apply ConcreteCategory.hom_ext _ _
    rintro ⟨a, x⟩
    dsimp
    congr 1
    change (picardDegreeSubfunctor f 0).toFunctor.map
      ((Over.homMk c.unop.left rfl : Over.mk (c.unop.left ≫ b.unop.left ≫ a.left) ⟶
          Over.mk (b.unop.left ≫ a.left)) ≫
        (Over.homMk b.unop.left rfl : Over.mk (b.unop.left ≫ a.left) ⟶
          Over.mk a.left)).op x = _
    rw [op_comp, Functor.map_comp]
    rfl

/-- A smooth stable unpointed genus-at-least-two family and a space representing its
relative degree-zero Picard functor. Properness and finite presentation are recorded
explicitly because the degree API needs these consequences of stability as instances.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
structure Input (S : Scheme.{u}) where
  genus : ℕ
  family : StablePointedModuli S genus 0
  noetherian : IsLocallyNoetherian family.base.left
  smooth : Smooth family.projection
  proper : IsProper family.projection
  finitePresentation : LocallyOfFinitePresentation family.projection
  J : AlgebraicSpace S
  representation : J.obj.obj ⋙ uliftFunctor.{u + 1, u} ≅
    @totalPicardZero S family.base family.curve family.projection proper finitePresentation

/-- The actual base, represented in the common ambient category.
Source: Stacks 025Y (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
abbrev Input.B {S : Scheme.{u}} (I : Input S) := schemeSpace I.family.base

/-- The map and Picard class of a Jacobian section, through its specified representation.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def classAt {S : Scheme.{u}} (I : Input S) (T : Over S) (x : I.J.obj.obj.obj (op T)) :=
  I.representation.hom.app (op T) (ULift.up x)

/-- The universal point of the represented base.
Source: Yoneda (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def schemePoint {S : Scheme.{u}} (T : Over S) : (schemeSpace T).obj.obj.obj (op T) :=
  ((Scheme.fppfTopology.over S).yonedaCompSheafToPresheaf.app T).inv.app (op T) (𝟙 T)

/-- Evaluation at the universal point.
Source: Yoneda (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def mapPoint {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (a : schemeSpace T ⟶ X) : X.obj.obj.obj (op T) :=
  a.hom.hom.app (op T) (schemePoint T)

/-- The line class O(D) of an effective Cartier divisor, with real data.
Source: Milne, Jacobian Varieties, Section 5
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def divisorClass {X : Scheme.{u}} (D : X.IdealSheafData) (h : D.IsInvertible) : X.Pic :=
  @Scheme.Pic.ofIsInvertible X D.toModulesᵛ h.isInvertible_dual_toModules

/-- A Picard class over its specified base map; only equality transport is used.
Source: relative Picard functor (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def classOver {S : Scheme.{u}} (I : Input S) (T : Over S)
    (b : T ⟶ I.family.base) (x : I.J.obj.obj.obj (op T))
    (w : (classAt I T x).1 = b) :
    (picardFunctorGrp I.family.projection).obj (op (Over.mk b.left)) :=
  w ▸ (classAt I T x).2.1

/-- The group maps are exactly tensor product, the trivial line and dualization on
all Picard test classes. Thus they specify the relative commutative group law, not
an unrelated group structure on the disjoint union over different base maps.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
structure GroupData {S : Scheme.{u}} (I : Input S) where
  p : I.J ⟶ I.B
  e : I.B ⟶ I.J
  section_eq : e ≫ p = 𝟙 I.B
  projection : ∀ (T : Over S) (x : I.J.obj.obj.obj (op T)),
    p.hom.hom.app (op T) x =
      (groupSchemeMap (classAt I T x).1).hom.hom.app (op T) (schemePoint T)
  add : product p p ⟶ I.J
  add_base : add ≫ p = fst p p ≫ p
  inv : I.J ⟶ I.J
  inv_base : inv ≫ p = p
  inv_identity : e ≫ inv = e
  one_class : ∀ (T : Over S) (a : T ⟶ I.family.base),
    ∃ w : (classAt I T (mapPoint (groupSchemeMap a ≫ e))).1 = a,
      classOver I T a (mapPoint (groupSchemeMap a ≫ e)) w = 1
  mul_class : ∀ (T : Over S) (z : (product p p).obj.obj.obj (op T)),
    ∃ (b : T ⟶ I.family.base)
      (w : (classAt I T (add.hom.hom.app (op T) z)).1 = b)
      (w₁ : (classAt I T ((fst p p).hom.hom.app (op T) z)).1 = b)
      (w₂ : (classAt I T ((snd p p).hom.hom.app (op T) z)).1 = b),
      classOver I T b (add.hom.hom.app (op T) z) w =
        classOver I T b ((fst p p).hom.hom.app (op T) z) w₁ *
        classOver I T b ((snd p p).hom.hom.app (op T) z) w₂
  inv_class : ∀ (T : Over S) (x : I.J.obj.obj.obj (op T)),
    ∃ w : (classAt I T (inv.hom.hom.app (op T) x)).1 = (classAt I T x).1,
      classOver I T (classAt I T x).1 (inv.hom.hom.app (op T) x) w =
        @Inv.inv _ (GrpCat.str ((picardFunctorGrp I.family.projection).obj
          (op (Over.mk (classAt I T x).1.left)))).toInv (classAt I T x).2.1

/-- The relative group with its actual identity and projection.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def GroupData.pointed {S : Scheme.{u}} {I : Input S} (g : GroupData I) : Pointed I.B :=
  ⟨I.J, g.p, g.e, g.section_eq⟩

/-- A degree-g-minus-one class translated by the given degree-zero class is effective.
The divisor is finite flat of degree g-minus-one and is effective Cartier.
Source: Milne, Jacobian Varieties, Sections 5--6
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def AbelTest {S : Scheme.{u}} (I : Input S) (T V : Over S)
    (b : T ⟶ I.family.base) (a : V ⟶ T)
    (N : (picardFunctorGrp I.family.projection).obj (op (Over.mk b.left)))
    (x : I.J.obj.obj.obj (op V)) (w : (classAt I V x).1 = a ≫ b)
    (R : Scheme.{u}) (q : R ⟶ V.left)
    (D : (Limits.pullback I.family.projection (q ≫ a.left ≫ b.left)).IdealSheafData)
    (hD : D.IsInvertible) : Prop :=
  IsHilbertSubscheme I.family.projection (I.genus - 1)
    (Over.mk (q ≫ a.left ≫ b.left)) D ∧
    (toPicardFunctor I.family.projection).app (op (Over.mk (q ≫ a.left ≫ b.left)))
      (divisorClass D hD) =
    (picardFunctorGrp I.family.projection).map
      (Over.homMk q rfl : Over.mk (q ≫ a.left ≫ b.left) ⟶
        Over.mk (a.left ≫ b.left)).op
      (classOver I V (a ≫ b) x w *
        (picardFunctorGrp I.family.projection).map
          (Over.homMk a.left rfl : Over.mk (a.left ≫ b.left) ⟶ Over.mk b.left).op N)

/-- The scheme-theoretic Abel image ideal on a chart is the intersection of the
kernels of all effective-divisor tests, not only tests over fields.
Source: Milne, Jacobian Varieties, Section 5
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def ThetaIdeal {S : Scheme.{u}} (I : Input S) (T V : Over S)
    (b : T ⟶ I.family.base) (a : V ⟶ T)
    (N : (picardFunctorGrp I.family.projection).obj (op (Over.mk b.left)))
    (x : I.J.obj.obj.obj (op V)) (w : (classAt I V x).1 = a ≫ b)
    (H : V.left.IdealSheafData) : Prop :=
  ∀ K : V.left.IdealSheafData, K ≤ H ↔
    ∀ (R : Scheme.{u}) (q : R ⟶ V.left)
      (D : (Limits.pullback I.family.projection (q ≫ a.left ≫ b.left)).IdealSheafData)
      (hD : D.IsInvertible), AbelTest I T V b a N x w R q D hD → K ≤ q.ker

/-- Theta is O(Theta) on every etale scheme chart of the pulled-back Jacobian.
Source: Deligne 4.1; Milne, Jacobian Varieties, Sections 5--6
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def ThetaLine {S : Scheme.{u}} (I : Input S) (g : GroupData I)
    (T : Over S) (b : T ⟶ I.family.base)
    (N : (picardFunctorGrp I.family.projection).obj (op (Over.mk b.left)))
    (L : (g.pointed.baseChange (groupSchemeMap b)).X.SmallModules) : Prop :=
  ∀ (V : Over S) (v : schemeSpace V ⟶ (g.pointed.baseChange (groupSchemeMap b)).X),
    IsEtale v.hom.hom → ∀ a : V ⟶ T,
    v ≫ (g.pointed.baseChange (groupSchemeMap b)).p = groupSchemeMap a →
    ∃ (w : (classAt I V (mapPoint (v ≫ g.pointed.baseChangeMap (groupSchemeMap b)))).1 =
        a ≫ b) (H : V.left.IdealSheafData), H.IsInvertible ∧
      ThetaIdeal I T V b a N (mapPoint (v ≫ g.pointed.baseChangeMap (groupSchemeMap b))) w H ∧
      Nonempty ((schemeModule V).obj ((smallModuleTensorPullback v).obj L) ≅ H.toModulesᵛ)

/-- Addition after base change, retained as its cartesian-square characterization.
Source: fibre products (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def IsLocalAddition {S : Scheme.{u}} {I : Input S} (g : GroupData I)
    (T : Over S) (b : T ⟶ I.family.base)
    (m : product (g.pointed.baseChange (groupSchemeMap b)).p
      (g.pointed.baseChange (groupSchemeMap b)).p ⟶
        (g.pointed.baseChange (groupSchemeMap b)).X) : Prop :=
  m ≫ (g.pointed.baseChange (groupSchemeMap b)).p = fst _ _ ≫ snd g.p (groupSchemeMap b) ∧
    ∃ q : product (g.pointed.baseChange (groupSchemeMap b)).p
        (g.pointed.baseChange (groupSchemeMap b)).p ⟶ product g.p g.p,
      q ≫ fst g.p g.p = fst _ _ ≫ fst g.p (groupSchemeMap b) ∧
      q ≫ snd g.p g.p = snd _ _ ≫ fst g.p (groupSchemeMap b) ∧
      m ≫ fst g.p (groupSchemeMap b) = q ≫ g.add

/-- The local normalized difference line, with its explicit tensor formula.
Source: Milne I Section 8 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def localDifference {S : Scheme.{u}} {I : Input S} (A : Pointed I.B)
    (T : Over S) (b : T ⟶ I.family.base)
    (m : product (A.baseChange (groupSchemeMap b)).p (A.baseChange (groupSchemeMap b)).p ⟶
      (A.baseChange (groupSchemeMap b)).X)
    (L : (A.baseChange (groupSchemeMap b)).X.SmallModules) :=
  (((smallModuleTensorPullback m).obj L ⊗
    (smallModuleTensorPullback (fst _ _)).obj (dual _ L)) ⊗
    (smallModuleTensorPullback (snd _ _)).obj (dual _ L)) ⊗
    (smallModuleTensorPullback (fst _ _ ≫ (A.baseChange (groupSchemeMap b)).p ≫
      (A.baseChange (groupSchemeMap b)).e)).obj L

/-- Local theta-difference characterization of the canonical principal polarization.
The map into J times its dual is fixed by both its projections.
Source: Deligne 4.1; Milne, Jacobian Varieties, Sections 5--6
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def ThetaPolarization {S : Scheme.{u}} (I : Input S) (g : GroupData I) (D : Pointed I.B)
    (P : (product g.p D.p).SmallModules) (lambda : I.J ⟶ D.X) : Prop :=
  ∀ (T : Over S) (b : T ⟶ I.family.base), Etale b.left →
    ∀ N : (picardFunctorGrp I.family.projection).obj (op (Over.mk b.left)),
    (∀ t : T.left, picardDegree I.family.projection N t = (I.genus : ℤ) - 1) →
    ∃ (L : (g.pointed.baseChange (groupSchemeMap b)).X.SmallModules)
      (m : product (g.pointed.baseChange (groupSchemeMap b)).p
        (g.pointed.baseChange (groupSchemeMap b)).p ⟶
          (g.pointed.baseChange (groupSchemeMap b)).X)
      (q : product (g.pointed.baseChange (groupSchemeMap b)).p
        (g.pointed.baseChange (groupSchemeMap b)).p ⟶ product g.p D.p),
      IsLine _ L ∧ ThetaLine I g T b N L ∧ IsLocalAddition g T b m ∧
      q ≫ fst g.p D.p = fst _ _ ≫ fst g.p (groupSchemeMap b) ∧
      q ≫ snd g.p D.p = snd _ _ ≫ fst g.p (groupSchemeMap b) ≫ lambda ∧
      AxisEquivalent (g.pointed.baseChange (groupSchemeMap b))
        (g.pointed.baseChange (groupSchemeMap b)) (localDifference g.pointed T b m L)
        ((smallModuleTensorPullback q).obj P)

/-- Normalized duality and theta autoduality, without a chosen global theta line.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
structure Polarization {S : Scheme.{u}} (I : Input S) where
  group : GroupData I
  D : Pointed I.B
  P : (product group.p D.p).SmallModules
  axes : Axes group.pointed D P
  represents : Represents group.pointed D P axes
  lambda : I.J ≅ D.X
  over_base : lambda.hom ≫ D.p = group.p
  identity : group.e ≫ lambda.hom = D.e
  theta : ThetaPolarization I group D P lambda.hom

/-- The graph (1,lambda) is an actual fibre-product map.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def diagonal {S : Scheme.{u}} {I : Input S} (p : Polarization I) :
    I.J ⟶ product p.group.p p.D.p :=
  pair (𝟙 I.J) p.lambda.hom ((Category.id_comp _).trans p.over_base.symm)

/-- The actual diagonal Poincare pullback, with no choice from an existence theorem.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def line {S : Scheme.{u}} {I : Input S} (p : Polarization I) : I.J.SmallModules :=
  (smallModuleTensorPullback (diagonal p)).obj p.P

/-- The specified axis-induced identity trivialization of the diagonal line.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def IsDiagonalRigidification {S : Scheme.{u}} {I : Input S} (p : Polarization I)
    (r : (smallModuleTensorPullback p.group.e).obj (line p) ≅ 𝟙_ I.B.SmallModules) : Prop :=
  ∃ w : p.group.e ≫ diagonal p = p.D.e ≫ leftAxis p.group.pointed p.D,
    r = rigidificationPullback (leftAxis p.group.pointed p.D) p.group.e
      p.D.e (diagonal p) w p.P p.axes.left

/-- A scheme representative of J over its actual base.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
structure Model {S : Scheme.{u}} {I : Input S} (p : Polarization I) where
  scheme : Over I.family.base.left
  iso : schemeSpace (Over.mk (scheme.hom ≫ I.family.base.hom)) ≅ I.J
  over_base : iso.hom ≫ p.group.p =
    groupSchemeMap (Over.homMk scheme.hom rfl :
      Over.mk (scheme.hom ≫ I.family.base.hom) ⟶ I.family.base)

/-- The corresponding ordinary invertible module on the scheme representative.
Source: Stacks 03G7; Deligne 4.1
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def ordinaryLine {S : Scheme.{u}} {I : Input S} {p : Polarization I} (M : Model p) :=
  (schemeModule (Over.mk (M.scheme.hom ≫ I.family.base.hom))).obj
    ((smallModuleTensorPullback M.iso.hom).obj (line p))

/-- Relative ampleness on every affine open of the actual base, in the recorded
ordinary ampleness convention.
Source: Stacks 01VH; Deligne 4.1
(blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def RelativelyAmple {S : Scheme.{u}} {I : Input S} {p : Polarization I} (M : Model p) : Prop :=
  ∀ U : I.family.base.left.Opens, IsAffineOpen U →
    ∃ h : ((Scheme.Modules.pullback ((M.scheme.hom ⁻¹ᵁ U).ι)).obj
      (ordinaryLine M)).IsInvertible,
      @Scheme.Modules.IsAmple (M.scheme.hom ⁻¹ᵁ U).toScheme
        ((Scheme.Modules.pullback ((M.scheme.hom ⁻¹ᵁ U).ι)).obj (ordinaryLine M)) h

/-- A cartesian curve arrow over any base arrow, including identity base change.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
structure CurveArrow {S : Scheme.{u}} (I' I : Input S) where
  base : I'.family.base ⟶ I.family.base
  curve : I'.family.curve ⟶ I.family.curve
  square : IsPullback curve I'.family.projection I.family.projection base.left

/-- The canonical Jacobian comparison is fixed on every Picard class, using the
published Picard pullback isomorphism for the specified cartesian square.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def IsCanonicalMap {S : Scheme.{u}} {I' I : Input S} (f : CurveArrow I' I)
    (a : I'.J ⟶ I.J) : Prop :=
  ∀ (T : Over S) (x : I'.J.obj.obj.obj (op T)),
    ∃ w : (classAt I T (a.hom.hom.app (op T) x)).1 = (classAt I' T x).1 ≫ f.base,
      (picardFunctorIsoOfIsPullback f.square).hom.app
        (op (Over.mk (classAt I' T x).1.left))
        (classOver I T ((classAt I' T x).1 ≫ f.base) (a.hom.hom.app (op T) x) w) =
        (classAt I' T x).2.1

/-- A normalized line comparison along a given canonical space map.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def PreservesRigidification {S : Scheme.{u}} {I' I : Input S}
    (p' : Polarization I') (p : Polarization I) (f : CurveArrow I' I)
    (a : I'.J ⟶ I.J) (w : p'.group.e ≫ a = groupSchemeMap f.base ≫ p.group.e)
    (r' : (smallModuleTensorPullback p'.group.e).obj (line p') ≅ 𝟙_ I'.B.SmallModules)
    (r : (smallModuleTensorPullback p.group.e).obj (line p) ≅ 𝟙_ I.B.SmallModules)
    (v : (smallModuleTensorPullback a).obj (line p) ≅ line p') : Prop :=
  (smallModuleTensorPullback p'.group.e).map v.hom ≫ r'.hom =
    (rigidificationPullback p.group.e p'.group.e (groupSchemeMap f.base) a w (line p) r).hom


/-- The identity cartesian curve arrow.
Source: fibre products (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def CurveArrow.id {S : Scheme.{u}} (I : Input S) : CurveArrow I I where
  base := 𝟙 I.family.base
  curve := 𝟙 I.family.curve
  square := IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Composition of cartesian curve arrows is pasting.
Source: fibre products (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
def CurveArrow.comp {S : Scheme.{u}} {I'' I' I : Input S}
    (f : CurveArrow I'' I') (g : CurveArrow I' I) : CurveArrow I'' I where
  base := f.base ≫ g.base
  curve := f.curve ≫ g.curve
  square := f.square.paste_horiz g.square

/-- A coherent normalized diagonal-line assignment for all the actual base schemes
in one ambient category. Maps are fixed by the Picard comparison; line maps preserve
identity rigidifications. The last two fields explicitly impose the identity and
composition laws, with the canonical pullback compositors. Hence they include the
cocycle on triple fibre products. No property of the diagonal line is assumed here.
Source: Deligne 4.1 (blueprint: def-sfb-smooth-jacobian-diagonal-data). -/
structure Assignment (S : Scheme.{u}) where
  polarization (I : Input S) : Polarization I
  rigidification (I : Input S) :
    (smallModuleTensorPullback (polarization I).group.e).obj (line (polarization I)) ≅
      𝟙_ I.B.SmallModules
  rigidification_eq (I : Input S) :
    IsDiagonalRigidification (polarization I) (rigidification I)
  map {I' I : Input S} (f : CurveArrow I' I) : I'.J ⟶ I.J
  canonical {I' I : Input S} (f : CurveArrow I' I) : IsCanonicalMap f (map f)
  over_base {I' I : Input S} (f : CurveArrow I' I) :
    map f ≫ (polarization I).group.p =
      (polarization I').group.p ≫ groupSchemeMap f.base
  identity {I' I : Input S} (f : CurveArrow I' I) :
    (polarization I').group.e ≫ map f = groupSchemeMap f.base ≫ (polarization I).group.e
  comparison {I' I : Input S} (f : CurveArrow I' I) :
    (smallModuleTensorPullback (map f)).obj (line (polarization I)) ≅ line (polarization I')
  normalized {I' I : Input S} (f : CurveArrow I' I) :
    PreservesRigidification (polarization I') (polarization I) f (map f) (identity f)
      (rigidification I') (rigidification I) (comparison f)
  map_id (I : Input S) : map (CurveArrow.id I) = 𝟙 I.J
  map_comp {I'' I' I : Input S} (f : CurveArrow I'' I') (g : CurveArrow I' I) :
    map (f.comp g) = map f ≫ map g
  comparison_id (I : Input S) :
    (comparison (CurveArrow.id I)).hom =
      (eqToIso (congrArg (fun a ↦ (smallModuleTensorPullback a).obj
        (line (polarization I))) (map_id I))).hom ≫
        (smallModuleTensorPullbackId I.J).hom.app (line (polarization I))
  comparison_comp {I'' I' I : Input S} (f : CurveArrow I'' I') (g : CurveArrow I' I) :
    (comparison (f.comp g)).hom =
      (eqToIso (congrArg (fun a ↦ (smallModuleTensorPullback a).obj
        (line (polarization I))) (map_comp f g))).hom ≫
      (pullbackComp (map f) (map g) (line (polarization I))).inv ≫
      (smallModuleTensorPullback (map f)).map (comparison g).hom ≫ (comparison f).hom

end AlgebraicGeometry.AlgebraicSpace.JacobianDiagonal
