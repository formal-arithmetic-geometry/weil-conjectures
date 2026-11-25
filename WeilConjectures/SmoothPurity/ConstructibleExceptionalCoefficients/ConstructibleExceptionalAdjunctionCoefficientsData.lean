/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-! # Constructible exceptional adjunction and coefficients

This file packages the constructible exceptional adjunctions at the finite, field, integral and
common coefficient stages, together with their coefficient comparisons and refinement
compatibilities.

The records below package conclusions. In particular they do not assume an exceptional
adjunction on an unrestricted pro-etale category.

## References

* [Stacks, Tags 08G2, 0F7B]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients

/-- A packaged finite coefficient field, using the existing algebra and finiteness notions. -/
structure FieldStage (l : ℕ) [Fact l.Prime] where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra (Padic l) carrier]
  [finite : FiniteDimensional (Padic l) carrier]

attribute [instance] FieldStage.field FieldStage.algebra FieldStage.finite

/-- The four kinds of coefficient stage in the assertion. Positive levels are indexed by
`ℕ+`, so the zero quotient is never introduced. -/
inductive Stage (l : ℕ) [Fact l.Prime] where
  | finite (E : FieldStage.{u} l) (n : ℕ+)
  | integral (E : FieldStage.{u} l)
  | rational (E : FieldStage.{u} l)
  | closed

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The exact recorded full finite-Tor categories. At field stages finite Tor imposes no
additional condition. -/
abbrev C (T : Scheme.{max u v}) : Stage.{max u v} l → Type (max u v + 2)
  | .finite E n => finiteTorConstructibleCategory l E.carrier n n.pos T
  | .integral E => finiteTorConstructibleIntegralCategory l E.carrier T
  | .rational E => sfRationalConstructibleCategory l E.carrier T
  | .closed => generalAlgebraicallyClosedConstructibleCategory l Ω T

/-- The category structures are inherited from the existing coefficient categories. -/
instance category (T : Scheme.{max u v}) (s : Stage.{max u v} l) :
    Category.{max u v + 2} (C.{u, v} l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- The finite-Tor subcategories inherit the triangulation of their ordinary derived
categories. -/
instance finiteTriangulated (E : FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (finiteTorConstructible l E.carrier n n.pos T).IsTriangulated :=
  (finite_ctf_isTriangulated l E.carrier n n.pos T).2.1

/-- The integral finite-Tor constructible category is triangulated: it is closed under
isomorphisms, shifts and triangles in the derived category of completed integral coefficients. -/
theorem integralTriangulated (E : FieldStage.{u} l) (T : Scheme.{u}) :
    (finiteTorConstructibleIntegral l E.carrier T).IsTriangulated := by
  let Q : ObjectProperty (DerivedCategory (scalarReductionSource.{u, u} l E.carrier T)) :=
    fun K ↦ ∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E.carrier T n).obj K) a b
  have hred (n : ℕ) :
      ∃ (_ : (scalarReductionDerivedExtension.{u, u} l E.carrier T n).CommShift ℤ),
        (scalarReductionDerivedExtension.{u, u} l E.carrier T n).IsTriangulated :=
    (scalarReductionDerivedExistence l E.carrier T n).choose_spec.choose_spec.2.1
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    intro K L e hK
    obtain ⟨a, b, hab, h⟩ := hK
    exact ⟨a, b, hab, fun n ↦ amplitude_iso T _
      ((scalarReductionDerivedExtension l E.carrier T n).mapIso e) a b (h n)⟩⟩
  have : Q.ContainsZero := by
    refine ⟨HasZeroObject.zero.choose, HasZeroObject.zero.choose_spec, 0, 0, le_rfl, ?_⟩
    intro n
    obtain ⟨s, ht⟩ := hred n
    let R := scalarReductionDerivedExtension.{u, u} l E.carrier T n
    have hz := R.map_isZero (isZero_zero _)
    refine ⟨le_rfl, ?_⟩
    intro L P hL f hf hP M i _hi
    obtain ⟨F, c, htri, hcomp⟩ := tensor_functor T _ M
    obtain ⟨e⟩ := hL
    obtain ⟨q⟩ := hcomp L P f hf hP
    have hF := F.map_isZero (hz.of_iso e)
    exact ((DerivedCategory.homologyFunctor _ i).map_isZero hF).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso q.symm)
  have : Q.IsStableUnderShift ℤ := ⟨fun m ↦ ⟨by
    intro K hK
    obtain ⟨a, b, hab, h⟩ := hK
    refine ⟨a - m, b - m, sub_le_sub_right hab m, ?_⟩
    intro n
    obtain ⟨s, ht⟩ := hred n
    exact amplitude_iso T _
      (((scalarReductionDerivedExtension l E.carrier T n).commShiftIso m).app K).symm
      _ _ ((finite_ctf_isTriangulated l E.carrier (n + 1) (Nat.succ_pos n) T).2.2.1
        _ a b m (h n))⟩⟩
  have : Q.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro V hV h₁ h₃
    obtain ⟨a, b, hab, h₁⟩ := h₁
    obtain ⟨c, d, hcd, h₃⟩ := h₃
    refine ⟨min a c, max b d, (min_le_left a c).trans (hab.trans (le_max_left b d)), ?_⟩
    intro n
    obtain ⟨s, ht⟩ := hred n
    let R := scalarReductionDerivedExtension.{u, u} l E.carrier T n
    exact (finite_ctf_isTriangulated l E.carrier (n + 1) (Nat.succ_pos n) T).2.2.2
      (R.mapTriangle.obj V) _ _ (R.map_distinguished V hV)
      (amplitude_mono T _ (h₁ n) (min_le_left _ _) (le_max_left _ _))
      (amplitude_mono T _ (h₃ n) (min_le_right _ _) (le_max_right _ _)))
  have : Q.IsTriangulated := { }
  exact inferInstanceAs (sfIntegralConstructible l E.carrier T ⊓ Q).IsTriangulated

attribute [instance] integralTriangulated

/-- Inherited zero objects. -/
instance zero (T : Scheme.{max u v}) (s : Stage.{max u v} l) : HasZeroObject (C.{u, v} l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Inherited additive structures. -/
instance preadditive (T : Scheme.{max u v}) (s : Stage.{max u v} l) :
    Preadditive (C.{u, v} l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Inherited integer shifts. -/
instance shift (T : Scheme.{max u v}) (s : Stage.{max u v} l) : HasShift (C.{u, v} l Ω T s) ℤ :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Additivity of inherited shifts. -/
instance shiftAdditive (T : Scheme.{max u v}) (s : Stage.{max u v} l) (n : ℤ) :
    (shiftFunctor (C.{u, v} l Ω T s) n).Additive :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Inherited distinguished triangles. -/
instance pretriangulated (T : Scheme.{max u v}) (s : Stage.{max u v} l) :
    Pretriangulated (C.{u, v} l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- The exact adjunction at one of the specified coefficient stages. Both triangle
identities and naturality of the Hom equivalences are fields of `Adjunction` itself. -/
structure Operation (X Y : Scheme.{max u v}) (s : Stage.{max u v} l) where
  F : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω Y s
  G : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω X s
  adjunction : F ⊣ G
  [leftAdditive : F.Additive]
  [rightAdditive : G.Additive]
  [leftShift : F.CommShift ℤ]
  [rightShift : G.CommShift ℤ]
  leftExact : F.IsTriangulated
  rightExact : G.IsTriangulated
  unitShift : adjunction.unit.CommShift ℤ
  counitShift : adjunction.counit.CommShift ℤ

attribute [instance] Operation.leftAdditive Operation.rightAdditive
  Operation.leftShift Operation.rightShift

/-- The coefficient comparison and the two completed unit/counit equations, for exact
scalar functors between two of the actual finite-Tor categories. The counit equation
uniquely characterizes b as the transpose of inverse q followed by the old counit. -/
structure Comparison {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    [TX.CommShift ℤ] [TY.CommShift ℤ] where
  q : A.F ⋙ TY ≅ TX ⋙ B.F
  b : A.G ⋙ TX ≅ TY ⋙ B.G
  unit (K : C.{u, v} l Ω X s) :
    TX.map (A.adjunction.unit.app K) ≫ b.hom.app (A.F.obj K) ≫
      B.G.map (q.hom.app K) = B.adjunction.unit.app (TX.obj K)
  counit (L : C.{u, v} l Ω Y s) :
    q.hom.app (A.G.obj L) ≫ B.F.map (b.hom.app L) ≫
      B.adjunction.counit.app (TY.obj L) = TY.map (A.adjunction.counit.app L)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ

/-- Composition of q and b, with the scalar associators retained at both endpoints. -/
structure Cocycle {X Y : Scheme.{max u v}} {s t r : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t} {D :
    Operation.{u, v} l Ω X Y r}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    {UX : C.{u, v} l Ω X t ⥤ C.{u, v} l Ω X r} {UY : C.{u, v} l Ω Y t ⥤ C.{u, v} l Ω Y r}
    {VX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X r} {VY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y r}
    [TX.CommShift ℤ] [TY.CommShift ℤ] [UX.CommShift ℤ] [UY.CommShift ℤ]
    [VX.CommShift ℤ] [VY.CommShift ℤ]
    (a : Comparison.{u, v} l Ω A B TX TY) (b : Comparison.{u, v} l Ω B D UX UY)
    (d : Comparison.{u, v} l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY) : Prop where
  left (K : C.{u, v} l Ω X s) :
    UY.map (a.q.hom.app K) ≫ b.q.hom.app (TX.obj K) ≫ D.F.map (αX.hom.app K) =
      αY.hom.app (A.F.obj K) ≫ d.q.hom.app K
  right (L : C.{u, v} l Ω Y s) :
    UX.map (a.b.hom.app L) ≫ b.b.hom.app (TY.obj L) ≫ D.G.map (αY.hom.app L) =
      αX.hom.app (A.G.obj L) ≫ d.b.hom.app L

/-- The finite and completed integral ring stages. This is only an index for the two
ring-sheaf constructions already present in the dependencies. -/
inductive RingStage (l : ℕ) [Fact l.Prime] where
  | finite (E : FieldStage.{u} l) (n : ℕ+)
  | integral (E : FieldStage.{u} l)

/-- Forget the restriction to ring stages. -/
abbrev RingStage.stage : RingStage.{u} l → Stage.{u} l
  | .finite E n => .finite E n
  | .integral E => .integral E

/-- The published coefficient sheaves, including their canonical pullback identifications. -/
abbrev RingStage.coefficients : RingStage.{u} l → PurCompactSupport.Coefficients.{u}
  | .finite E n => PurCompactSupport.finite l E.carrier n n.pos
  | .integral E => PurCompactSupport.completed l E.carrier

/-- Inclusion into the ordinary derived category of the corresponding ring sheaf. -/
abbrev RingStage.inclusion (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    C.{u, v} l Ω T (s.stage l) ⥤
      DerivedCategory (pbcModules T ((s.coefficients l).ring T)) :=
  match s with
  | .finite E n => (finiteTorConstructible l E.carrier n n.pos T).ι
  | .integral E => (finiteTorConstructibleIntegral l E.carrier T).ι

/-- Exactly the ring coefficient changes generated by quotients, integral reductions,
retained ramified extensions and completed inclusions. Composition is allowed only
when its actual ring-sheaf maps compose, and identities have identity ring maps. -/
inductive Allowed : {s t : RingStage.{u} l} →
    PurCompactSupport.Change (s.coefficients l) (t.coefficients l) → Prop
  | quotient (E : FieldStage.{u} l) (m n : ℕ+) (h : (n : ℕ) ≤ m) :
      Allowed (s := .finite E m) (t := .finite E n)
        (PurCompactSupport.finiteQuotientChange l E.carrier m n m.pos n.pos h)
  | ramified (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (n : ℕ+) :
      Allowed (s := .finite E n) (t := .finite L ⟨e * n, Nat.mul_pos e.pos n.pos⟩)
        (PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos n n.pos)
  | reduction (E : FieldStage.{u} l) (n : ℕ+) :
      Allowed (s := .integral E) (t := .finite E n)
        (PurCompactSupport.reduction l E.carrier n n.pos)
  | integral (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
      Allowed (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
  | identity (s : RingStage.{u} l)
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ W : Scheme.{u}, a.map W = 𝟙 _) : Allowed a
  | comp {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W) :
      Allowed a → Allowed b → Allowed d

/-- The restricted scalar functor, together with its identification with actual derived
extension along the specified ring-sheaf map. This records preservation as a conclusion. -/
structure Scalar {s t : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (T : Scheme.{max u v}) where
  functor : C.{u, v} l Ω T (s.stage l) ⥤ C.{u, v} l Ω T (t.stage l)
  realization : functor ⋙ RingStage.inclusion.{u, v} l Ω T t ≅
    RingStage.inclusion.{u, v} l Ω T s ⋙ pbcDerivedExtend (a.map T)
  [commShift : functor.CommShift ℤ]
  [additive : functor.Additive]
  exact : functor.IsTriangulated

attribute [instance] Scalar.commShift Scalar.additive

/-- The q projection with the actual restricted scalar structures supplied explicitly. -/
def Scalar.q {X Y : Scheme.{max u v}} {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {A : Operation.{u, v} l Ω X Y (s.stage l)} {B : Operation.{u, v} l Ω X Y (t.stage l)}
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y)
    (d : Comparison.{u, v} l Ω A B SX.functor SY.functor) : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F :=
  d.q

/-- The ambient realization of the left functor at a ring stage. -/
abbrev LeftRealization {X Y : Scheme.{max u v}} {f : X ⟶ Y} (c : Compactification f)
    (s : RingStage.{max u v} l) (A : Operation.{u, v} l Ω X Y (s.stage l)) :=
  A.F ⋙ RingStage.inclusion.{u, v} l Ω Y s ≅ RingStage.inclusion.{u, v} l Ω X s ⋙
    PurCompactSupport.image (s.coefficients l) c

/-- The q map is the canonical scalar-adjunction mate of the proper/open restriction
square, expressed through the actual scalar and support realizations. In particular
it is not an arbitrarily selected natural isomorphism. -/
def QNormalized {X Y : Scheme.{max u v}} {f : X ⟶ Y} (c : Compactification f)
    {s t : RingStage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y (s.stage l)} {B : Operation.{u, v} l Ω X Y (t.stage l)}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (SX : Scalar.{u, v} l Ω a X) (SY : Scalar.{u, v} l Ω a Y)
    (rA : LeftRealization.{u, v} l Ω c s A) (rB : LeftRealization.{u, v} l Ω c t B)
    (d : Comparison.{u, v} l Ω A B SX.functor SY.functor) : Prop :=
  ∀ K : C.{u, v} l Ω X (s.stage l),
    (RingStage.inclusion.{u, v} l Ω Y t).map (d.q.hom.app K) ≫
        rB.hom.app (SX.functor.obj K) ≫
        (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
      SY.realization.hom.app (A.F.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
        (PurCompactSupport.comparison a c).app ((RingStage.inclusion.{u, v} l Ω X s).obj K)

/-- Scalar associators are the existing tensor-unit-normalized adjunction comparisons,
lifted through the full inclusions. -/
structure ScalarComposition {s t r : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l)}
    {d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l)}
    (h : ∀ W : Scheme.{max u v}, a.map W ≫ b.map W = d.map W) (T : Scheme.{max u v})
    (A : Scalar.{u, v} l Ω a T) (B : Scalar.{u, v} l Ω b T) (D : Scalar.{u, v} l Ω d T) where
  iso : A.functor ⋙ B.functor ≅ D.functor
  normalized (K : C.{u, v} l Ω T (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω T r).map (iso.hom.app K) ≫ D.realization.hom.app K =
      B.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (b.map T)).map (A.realization.hom.app K) ≫
        (PurCompactSupport.tensorComposition (a.map T) (b.map T) (d.map T) (h T)).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K)

/-- Identity scalar extension is normalized by multiplication, through the existing
scalar adjunction. -/
structure ScalarIdentity {s : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ W : Scheme.{max u v}, a.map W = 𝟙 _) (T : Scheme.{max u v}) (A :
    Scalar.{u, v} l Ω a T) where
  iso : A.functor ≅ 𝟭 _
  normalized (K : C.{u, v} l Ω T (s.stage l)) :
    (RingStage.inclusion.{u, v} l Ω T s).map (iso.hom.app K) =
      A.realization.hom.app K ≫
        (eqToIso (congrArg pbcDerivedExtend (h T))).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K) ≫
        (PurCompactSupport.tensorIdentity ((s.coefficients l).ring T)).hom.app
          ((RingStage.inclusion.{u, v} l Ω T s).obj K)

/-- Rationalization on the integral finite-Tor category uses the specified raw scalar
localization, with the same integral representatives. -/
abbrev rationalization (E : FieldStage.{max u v} l) (T : Scheme.{max u v}) :
    C.{u, v} l Ω T (.integral E) ⥤ C.{u, v} l Ω T (.rational E) :=
  PurCompactSupport.finiteTorIntegralInclusion l E.carrier T ⋙
    sfRationalConstructibleLocalization l E.carrier T

/-- The actual completed scalar functor after rationalization. The parameter zero is
only the proof parameter of the published intrinsic construction, independent of the
geometric characteristic. -/
abbrev rationalScalar (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (T : Scheme.{max u v}) : C.{u, v} l Ω T (.rational E) ⥤ C.{u, v} l Ω T (.rational L) :=
  sfRationalScalarExtension l E.carrier T 0 (Fact.out : l.Prime).ne_zero L.carrier i

/-- The canonical small field model of a common coefficient stage. -/
abbrev commonField (i : AlgebraicallyClosedCoefficients.Index l Ω) : FieldStage.{max u v} l where
  carrier := AlgebraicallyClosedCoefficients.Coefficient.{max u v} l Ω i

/-- Select one endpoint of the fixed morphism, without imposing extra geometric
hypotheses on arbitrary schemes. -/
abbrev endpoint (X Y : Scheme.{u}) (side : Bool) : Scheme.{u} :=
  if side then X else Y

/-- Coefficient equations with the shift structures supplied as output data, for the
published raw rationalization, rational extension, and finite-stage inclusion functors. -/
structure FieldComparison {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t) (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t) where
  [shiftX : TX.CommShift ℤ]
  [shiftY : TY.CommShift ℤ]
  comparison : Comparison.{u, v} l Ω A B TX TY

/-- Left comparison with the output shift structures retained in its type. -/
def FieldComparison.q {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : FieldComparison.{u, v} l Ω A B TX TY) : A.F ⋙ TY ≅ TX ⋙ B.F :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.q

/-- Right comparison with the output shift structures retained in its type. -/
def FieldComparison.b {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    (d : FieldComparison.{u, v} l Ω A B TX TY) : A.G ⋙ TX ≅ TY ⋙ B.G :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.b

/-- The same cocycle at field stages, retaining the existing scalar associators. -/
def FieldCocycle {X Y : Scheme.{max u v}} {s t r : Stage.{max u v} l}
    {A : Operation.{u, v} l Ω X Y s} {B : Operation.{u, v} l Ω X Y t} {D :
    Operation.{u, v} l Ω X Y r}
    {TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t} {TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t}
    {UX : C.{u, v} l Ω X t ⥤ C.{u, v} l Ω X r} {UY : C.{u, v} l Ω Y t ⥤ C.{u, v} l Ω Y r}
    {VX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X r} {VY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y r}
    (a : FieldComparison.{u, v} l Ω A B TX TY) (b : FieldComparison.{u, v} l Ω B D UX UY)
    (d : FieldComparison.{u, v} l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY) : Prop :=
  letI := a.shiftX
  letI := a.shiftY
  letI := b.shiftX
  letI := b.shiftY
  letI := d.shiftX
  letI := d.shiftY
  Cocycle.{u, v} l Ω a.comparison b.comparison d.comparison αX αY

/-- The published finite-stage inclusion with both endpoint categories explicit. -/
abbrev commonInclusion (T : Scheme.{max u v}) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    C.{u, v} l Ω T (.rational (commonField.{u, v} l Ω i)) ⥤ C.{u, v} l Ω T .closed :=
  GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := T) i

/-- The existing common-stage transition isomorphism, transported from the opaque
stage-system transition to the actual rational tensor functor by its defining equality. -/
def commonTransition (T : Scheme.{max u v}) (i j : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : i ≤ j) :
    rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) T ⋙
        commonInclusion.{u, v} l Ω T j ≅
      commonInclusion.{u, v} l Ω T i :=
  eqToIso (congrArg (fun F ↦ F ⋙ commonInclusion.{u, v} l Ω T j)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω T).exists.choose_spec.1
      i j h).symm) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).transIso h

/-- Refinement is the counit-normalized conjugate comparison between the two adjunctions.
Both displayed equations retain all functor components, including the unit equation. -/
structure RefinementComparison {X Y : Scheme.{max u v}} {s : Stage.{max u v} l}
    (A B : Operation.{u, v} l Ω X Y s) where
  left : A.F ≅ B.F
  right : B.G ≅ A.G
  counit (L : C.{u, v} l Ω Y s) :
    left.hom.app (B.G.obj L) ≫ B.adjunction.counit.app L =
      A.F.map (right.hom.app L) ≫ A.adjunction.counit.app L
  unit (K : C.{u, v} l Ω X s) :
    B.adjunction.unit.app K ≫ right.hom.app (B.F.obj K) =
      A.adjunction.unit.app K ≫ A.G.map (left.hom.app K)
  leftShift : left.hom.CommShift ℤ
  rightShift : right.hom.CommShift ℤ

/-- The canonical proper/open refinement comparison, normalized by the open unit
and proper counit. The pullback equality is proof data, not a new comparison map. -/
def RingRefinementNormalized {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (s : RingStage.{max u v} l)
    {A B : Operation.{u, v} l Ω X Y (s.stage l)}
    (rA : LeftRealization.{u, v} l Ω c s A) (rB : LeftRealization.{u, v} l Ω d s B)
    (ρ : RefinementComparison.{u, v} l Ω A B) : Prop :=
  ∃ (hi : (s.coefficients l).pull (c.i ≫ r.hom) =
        proEtaleRingCompositeCoefficients c.i r.hom
          ((s.coefficients l).ring d.Z) ((s.coefficients l).ring c.Z)
          ((s.coefficients l).ring X)
          ((s.coefficients l).pull r.hom) ((s.coefficients l).pull c.i))
    (hg : (s.coefficients l).pull (r.hom ≫ d.g) =
        proEtaleRingCompositeCoefficients r.hom d.g
          ((s.coefficients l).ring Y) ((s.coefficients l).ring d.Z)
          ((s.coefficients l).ring c.Z)
          ((s.coefficients l).pull d.g) ((s.coefficients l).pull r.hom)),
  ∀ K : C.{u, v} l Ω X (s.stage l),
    ∃ ε : (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory.obj
          ((RingStage.inclusion.{u, v} l Ω X s).obj K) ≅
        (PurCompactSupport.push (s.coefficients l) r.hom).obj
          ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory.obj
            ((RingStage.inclusion.{u, v} l Ω X s).obj K)),
      (PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv _ _ ε.hom ≫
          PurCompactSupport.refinementRestriction (s.coefficients l) r hi
            ((RingStage.inclusion.{u, v} l Ω X s).obj K) =
        (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit.app
          ((RingStage.inclusion.{u, v} l Ω X s).obj K) ∧
      rA.inv.app K ≫ (RingStage.inclusion.{u, v} l Ω Y s).map (ρ.left.hom.app K) ≫ rB.hom.app K =
        ((PurCompactSupport.geometricPushComposition (s.coefficients l) r.hom d.g hg ≪≫
          eqToIso (congrArg (fun h ↦ PurCompactSupport.push (s.coefficients l) h)
            r.hom_g)).symm.app _).hom ≫
          (PurCompactSupport.push (s.coefficients l) d.g).map ε.inv

/-- The full conclusion, with actual categories and canonical scalar/proper-open
normalizations. All functors and comparisons are output data; no adjunction or
coefficient compatibility is a premise of the theorem asserting this record exists. -/
structure RingSystem (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] where
  operation (c : Compactification f) (s : Stage.{max u v} l) : Operation.{u, v} l Ω X Y s
  left (c : Compactification f) (s : RingStage.{max u v} l) :
    LeftRealization.{u, v} l Ω c s (operation c (s.stage l))
  finiteRight (c : Compactification f) (E : FieldStage.{max u v} l) (n : ℕ+) :
    (operation c (.finite E n)).G ⋙ RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n) ≅
      RingStage.inclusion.{u, v} l Ω Y (RingStage.finite E n) ⋙
        @ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E.carrier n) _
          (Padic.finite_coefficientExtensionRing l E.carrier n n.pos) X Y f c
  integralLeft (c : Compactification f) (E : FieldStage.{max u v} l) :
    (operation c (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
  integralLeft_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    ((sfIntegralConstructible l E.carrier Y).ι.map
        ((integralLeft c E).hom.app K)) =
      (left c (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl)
          c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  rationalLeft (c : Compactification f) (E : FieldStage.{max u v} l) :
    (operation c (.rational E)).F ≅
      sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
  scalar {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : Scalar.{u, v} l Ω a (endpoint X Y side)
  finiteScalar_eq {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.finite E n) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) s ⋙
        pbcDerivedExtend (a.map (endpoint X Y side))
  finiteScalar_normalized {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)
  integralScalar_eq (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral L) =
      RingStage.inclusion.{u, v} l Ω (endpoint X Y side) (RingStage.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)
  integralScalar_normalized (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C.{u, v} l Ω (endpoint X Y side) (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)
  comparison (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    Comparison.{u, v} l Ω (operation c (s.stage l)) (operation c (t.stage l))
      (scalar a ha true).functor (scalar a ha false).functor
  comparison_normalized (c : Compactification f) {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    QNormalized.{u, v} l Ω c a (scalar a ha true) (scalar a ha false)
      (left c s) (left c t) (comparison c a ha)
  scalarComposition {s t r : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :
    ScalarComposition.{u, v} l Ω h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  cocycle (c : Compactification f) {s t r : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) :
    Cocycle.{u, v} l Ω (comparison c a ha) (comparison c b hb) (comparison c d hd)
      (scalarComposition a b d h ha hb hd true).iso
      (scalarComposition a b d h ha hb hd false).iso
  scalarIdentity {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :
    ScalarIdentity.{u, v} l Ω h (endpoint X Y side) (scalar a ha side)
  identityLeft (c : Compactification f) {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C.{u, v} l Ω X (s.stage l)) :
    (comparison c a ha).q.hom.app K ≫
        (operation c (s.stage l)).F.map ((scalarIdentity a h ha true).iso.hom.app K) =
      (scalarIdentity a h ha false).iso.hom.app ((operation c (s.stage l)).F.obj K)
  identityRight (c : Compactification f) {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a)
      (L : C.{u, v} l Ω Y (s.stage l)) :
    (comparison c a ha).b.hom.app L ≫
        (operation c (s.stage l)).G.map ((scalarIdentity a h ha false).iso.hom.app L) =
      (scalarIdentity a h ha true).iso.hom.app ((operation c (s.stage l)).G.obj L)

/-- Rational localization and common-stage descent of the same ring-stage system. -/
structure FieldSystem (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem.{u, v} l Ω D hl (f := f)) where
  rationalizationComparison (c : Compactification f) (E : FieldStage.{max u v} l) :
    FieldComparison.{u, v} l Ω (R.operation c (.integral E)) (R.operation c (.rational E))
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  rationalization_normalized (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (rationalizationComparison c E).q.hom.app K ≫
        (R.rationalLeft c E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map
        ((R.integralLeft c E).hom.app K)
  rationalComparison (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :
    FieldComparison.{u, v} l Ω (R.operation c (.rational E)) (R.operation c (.rational L))
      (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y)
  rational_normalized (c : Compactification f) (E L : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((rationalComparison c E L i).q.hom.app
        ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω L Y).map
        ((Scalar.q.{u, v} l Ω
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) true)
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) false)
          (R.comparison c (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i))).hom.app K))
  rationalCocycle (c : Compactification f) (E L M : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier) :
    FieldCocycle.{u, v} l Ω (rationalComparison c E L i) (rationalComparison c L M j)
      (rationalComparison c E M (j.comp i))
      (sfRationalScalarComp l E.carrier L.carrier i X 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
  rationalIdentityLeft (c : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.rational E)) :
    (rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).q.hom.app K ≫
        (R.operation c (.rational E)).F.map
          ((sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).F.obj K)
  rationalIdentityRight (c : Compactification f) (E : FieldStage.{max u v} l)
      (L : C.{u, v} l Ω Y (.rational E)) :
    (rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).b.hom.app L ≫
        (R.operation c (.rational E)).G.map
          ((sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app L) =
      (sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).G.obj L)
/-- Common coefficient stages and compactification refinement of the fixed system. -/
structure CommonSystem (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem.{u, v} l Ω D hl (f := f))
    (F : FieldSystem.{u, v} l Ω D hl R) where
  commonComparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    FieldComparison.{u, v} l Ω (R.operation c (.rational (commonField.{u, v} l Ω i)))
      (R.operation c .closed)
      (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
  common_normalized (c : Compactification f)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((commonComparison c i).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y i).obj
        ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K)))
  commonCocycleLeft (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq
      ((commonInclusion.{u, v} l Ω Y j).map
          ((F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app
              K) ≫
        (commonComparison c j).q.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X i j h).obj K))
      ((commonTransition.{u, v} l Ω Y i j h).hom.app
            ((R.operation c (.rational (commonField.{u, v} l Ω i))).F.obj K) ≫
        (commonComparison c i).q.hom.app K ≫
        (R.operation c .closed).F.map
          ((commonTransition.{u, v} l Ω X i j h).inv.app K))
  commonCocycleRight (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (L : C.{u, v} l Ω Y (.rational (commonField.{u, v} l Ω i))) :
    HEq
      ((commonInclusion.{u, v} l Ω X j).map
          ((F.rationalComparison c (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).b.hom.app
              L) ≫
        (commonComparison c j).b.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Y i j h).obj L))
      ((commonTransition.{u, v} l Ω X i j h).hom.app
            ((R.operation c (.rational (commonField.{u, v} l Ω i))).G.obj L) ≫
        (commonComparison c i).b.hom.app L ≫
        (R.operation c .closed).G.map
          ((commonTransition.{u, v} l Ω Y i j h).inv.app L))
/-- Compactification refinements, retaining the counit-conjugate right comparisons. -/
structure RefinementSystem (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem.{u, v} l Ω D hl (f := f)) (F : FieldSystem.{u, v} l Ω D hl R)
    (M : CommonSystem.{u, v} l Ω D hl R F) where
  refinement {c d : Compactification f} (r : c.Refinement d) (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (R.operation c s) (R.operation d s)
  refinement_normalized {c d : Compactification f} (r : c.Refinement d)
      (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (R.left c s) (R.left d s) (refinement r (s.stage l))
  refinementRational {c d : Compactification f} (r : c.Refinement d)
      (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((refinement r (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K))
      ((rationalization.{u, v} l Ω E Y).map ((refinement r (.integral E)).left.hom.app K))
  refinementCommon {c d : Compactification f} (r : c.Refinement d)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (M.commonComparison c i).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y i).map
          ((refinement r (.rational (commonField.{u, v} l Ω i))).left.hom.app K) ≫
        (M.commonComparison d i).q.hom.app K =
      (refinement r .closed).left.hom.app
        ((commonInclusion.{u, v} l Ω X i).obj K)
  refinementIdentity (c : Compactification f) (s : Stage.{max u v} l) :
    (refinement (Compactification.Refinement.id c) s).left = Iso.refl _
  refinementComposition {a b c : Compactification f}
      (r : a.Refinement b) (t : b.Refinement c) (s : Stage.{max u v} l) :
    (refinement (r.comp t) s).left = (refinement r s).left ≪≫ (refinement t s).left

/-- One joint family of ring, field, common-stage and refinement conclusions.
The later records refer to the very same operation and comparison data in the earlier ones. -/
structure System (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
 where
  ring : RingSystem.{u, v} l Ω D hl (f := f)
  fields : FieldSystem.{u, v} l Ω D hl ring
  common : CommonSystem.{u, v} l Ω D hl ring fields
  refinements : RefinementSystem.{u, v} l Ω D hl ring fields common

end ConstructibleExceptionalCoefficients
end WeilConjectures
