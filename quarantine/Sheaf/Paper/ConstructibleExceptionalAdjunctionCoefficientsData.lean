/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import all Sheaf.Paper.FiniteCtfTriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor


/-! # Constructible exceptional adjunction and coefficients

Source: current blueprint, exceptional inverse image and coefficient comparisons
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients).

The records below package conclusions. In particular they do not assume an exceptional
adjunction on an unrestricted pro-etale category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients

/-- A packaged finite coefficient field, using the existing algebra and finiteness notions.
Source: blueprint coefficient conventions
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure FieldStage (l : ℕ) [Fact l.Prime] where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra (Padic l) carrier]
  [finite : FiniteDimensional (Padic l) carrier]

attribute [instance] FieldStage.field FieldStage.algebra FieldStage.finite

/-- The four kinds of coefficient stage in the assertion. Positive levels are indexed by
`ℕ+`, so the zero quotient is never introduced. Source: blueprint exceptional paragraph
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
inductive Stage (l : ℕ) [Fact l.Prime] where
  | finite (E : FieldStage.{u} l) (n : ℕ+)
  | integral (E : FieldStage.{u} l)
  | rational (E : FieldStage.{u} l)
  | closed

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The exact recorded full finite-Tor categories. At field stages finite Tor imposes no
additional condition. Source: blueprint finite-Tor and coefficient conventions
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev C (T : Scheme.{u}) : Stage.{u} l → Type (u + 2)
  | .finite E n => finiteTorConstructibleCategory l E.carrier n n.pos T
  | .integral E => finiteTorConstructibleIntegralCategory l E.carrier T
  | .rational E => sfRationalConstructibleCategory l E.carrier T
  | .closed => generalAlgebraicallyClosedConstructibleCategory l Ω T

/-- The category structures are inherited from the existing coefficient categories.
Source: blueprint full-subcategory convention
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
instance category (T : Scheme.{u}) (s : Stage.{u} l) : Category.{u + 2} (C l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- The finite-Tor subcategories inherit the triangulation of their ordinary derived
categories. Source: blueprint finite-Tor paragraph
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients).
Proof: finite Tor amplitude is invariant under isomorphisms and shifts. Tensor a
distinguished triangle with each degree-zero module and use its long exact cohomology
sequence. For integral objects use one common interval for all reductions. Combine
this with bounded constructibility and derived completeness. -/
instance finiteTriangulated (E : FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (finiteTorConstructible l E.carrier n n.pos T).IsTriangulated :=
  (finite_ctf_isTriangulated l E.carrier n n.pos T).2.1

/-- The same closure assertion for the completed integral coefficient category.
This is the DAG statement lem-weil-integral-ctf-triangulated, stated here on the
recorded predicate of def-weil-finite-tor-amplitude.
Source: blueprint integral finite-Tor paragraph; Stacks Project, Tag 08G2 (2)
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients).
Proof: every reduction is exact and preserves shifts. A common interval for two
vertices is enlarged by its minimum and maximum endpoints, independently of the level.
The finite triangle argument then gives the third vertex at every level. Completeness
and bounded constructibility are closed under triangles and shifts. -/
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

/-- Inherited zero objects. Source: blueprint finite-Tor paragraph
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
instance zero (T : Scheme.{u}) (s : Stage.{u} l) : HasZeroObject (C l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Inherited additive structures. Source: blueprint full-subcategory convention
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
instance preadditive (T : Scheme.{u}) (s : Stage.{u} l) : Preadditive (C l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Inherited integer shifts. Source: blueprint finite-Tor paragraph
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
instance shift (T : Scheme.{u}) (s : Stage.{u} l) : HasShift (C l Ω T s) ℤ :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Additivity of inherited shifts. Source: blueprint exactness assertion
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
instance shiftAdditive (T : Scheme.{u}) (s : Stage.{u} l) (n : ℤ) :
    (shiftFunctor (C l Ω T s) n).Additive :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- Inherited distinguished triangles. Source: blueprint exactness assertion
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
instance pretriangulated (T : Scheme.{u}) (s : Stage.{u} l) :
    Pretriangulated (C l Ω T s) :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance
  | .rational _ => inferInstance
  | .closed => inferInstance

/-- The exact adjunction at one of the specified coefficient stages. Both triangle
identities and naturality of the Hom equivalences are fields of `Adjunction` itself.
Source: blueprint exceptional adjunction and shift assertions
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure Operation (X Y : Scheme.{u}) (s : Stage.{u} l) where
  F : C l Ω X s ⥤ C l Ω Y s
  G : C l Ω Y s ⥤ C l Ω X s
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
uniquely characterizes b as the transpose of inverse q followed by the old counit.
Source: blueprint coefficient-compatibility displays
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure Comparison {X Y : Scheme.{u}} {s t : Stage.{u} l}
    (A : Operation l Ω X Y s) (B : Operation l Ω X Y t)
    (TX : C l Ω X s ⥤ C l Ω X t) (TY : C l Ω Y s ⥤ C l Ω Y t)
    [TX.CommShift ℤ] [TY.CommShift ℤ] where
  q : A.F ⋙ TY ≅ TX ⋙ B.F
  b : A.G ⋙ TX ≅ TY ⋙ B.G
  unit (K : C l Ω X s) :
    TX.map (A.adjunction.unit.app K) ≫ b.hom.app (A.F.obj K) ≫
      B.G.map (q.hom.app K) = B.adjunction.unit.app (TX.obj K)
  counit (L : C l Ω Y s) :
    q.hom.app (A.G.obj L) ≫ B.F.map (b.hom.app L) ≫
      B.adjunction.counit.app (TY.obj L) = TY.map (A.adjunction.counit.app L)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ

/-- Composition of q and b, with the scalar associators retained at both endpoints.
Source: blueprint identity and composition cocycles
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure Cocycle {X Y : Scheme.{u}} {s t r : Stage.{u} l}
    {A : Operation l Ω X Y s} {B : Operation l Ω X Y t} {D : Operation l Ω X Y r}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {UX : C l Ω X t ⥤ C l Ω X r} {UY : C l Ω Y t ⥤ C l Ω Y r}
    {VX : C l Ω X s ⥤ C l Ω X r} {VY : C l Ω Y s ⥤ C l Ω Y r}
    [TX.CommShift ℤ] [TY.CommShift ℤ] [UX.CommShift ℤ] [UY.CommShift ℤ]
    [VX.CommShift ℤ] [VY.CommShift ℤ]
    (a : Comparison l Ω A B TX TY) (b : Comparison l Ω B D UX UY)
    (d : Comparison l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY) : Prop where
  left (K : C l Ω X s) :
    UY.map (a.q.hom.app K) ≫ b.q.hom.app (TX.obj K) ≫ D.F.map (αX.hom.app K) =
      αY.hom.app (A.F.obj K) ≫ d.q.hom.app K
  right (L : C l Ω Y s) :
    UX.map (a.b.hom.app L) ≫ b.b.hom.app (TY.obj L) ≫ D.G.map (αY.hom.app L) =
      αX.hom.app (A.G.obj L) ≫ d.b.hom.app L

/-- The finite and completed integral ring stages. This is only an index for the two
ring-sheaf constructions already present in the dependencies.
Source: blueprint finite and integral coefficients
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
inductive RingStage (l : ℕ) [Fact l.Prime] where
  | finite (E : FieldStage.{u} l) (n : ℕ+)
  | integral (E : FieldStage.{u} l)

/-- Forget the restriction to ring stages. Source: blueprint coefficient list
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev RingStage.stage : RingStage.{u} l → Stage.{u} l
  | .finite E n => .finite E n
  | .integral E => .integral E

/-- The published coefficient sheaves, including their canonical pullback identifications.
Source: blueprint ordinary finite and completed integral module conventions
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev RingStage.coefficients : RingStage.{u} l → PurCompactSupport.Coefficients.{u}
  | .finite E n => PurCompactSupport.finite l E.carrier n n.pos
  | .integral E => PurCompactSupport.completed l E.carrier

/-- Inclusion into the ordinary derived category of the corresponding ring sheaf.
Source: blueprint strictly full finite-Tor subcategories
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev RingStage.inclusion (T : Scheme.{u}) (s : RingStage.{u} l) :
    C l Ω T (s.stage l) ⥤
      DerivedCategory (pbcModules T ((s.coefficients l).ring T)) :=
  match s with
  | .finite E n => (finiteTorConstructible l E.carrier n n.pos T).ι
  | .integral E => (finiteTorConstructibleIntegral l E.carrier T).ι

/-- Exactly the ring coefficient changes generated by quotients, integral reductions,
retained ramified extensions and completed inclusions. Composition is allowed only
when its actual ring-sheaf maps compose, and identities have identity ring maps.
Source: blueprint coefficient-change list and the en convention
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
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
extension along the specified ring-sheaf map. This records preservation as a conclusion.
Source: blueprint derived finite change and completed scalar extension
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure Scalar {s t : RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (T : Scheme.{u}) where
  functor : C l Ω T (s.stage l) ⥤ C l Ω T (t.stage l)
  realization : functor ⋙ t.inclusion l Ω T ≅
    s.inclusion l Ω T ⋙ pbcDerivedExtend (a.map T)
  [commShift : functor.CommShift ℤ]
  [additive : functor.Additive]
  exact : functor.IsTriangulated

attribute [instance] Scalar.commShift Scalar.additive

/-- The q projection with the actual restricted scalar structures supplied explicitly.
Source: blueprint canonical q (blueprint: lem-sf-constructible-exceptional-adjunction-coefficients).
-/
def Scalar.q {X Y : Scheme.{u}} {s t : RingStage.{u} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {A : Operation l Ω X Y (s.stage l)} {B : Operation l Ω X Y (t.stage l)}
    (SX : Scalar l Ω a X) (SY : Scalar l Ω a Y)
    (d : Comparison l Ω A B SX.functor SY.functor) : A.F ⋙ SY.functor ≅ SX.functor ⋙ B.F :=
  d.q

/-- The ambient realization of the left functor at a ring stage.
Source: blueprint compact-support definition R p_* j_!
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev LeftRealization {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s : RingStage.{u} l) (A : Operation l Ω X Y (s.stage l)) :=
  A.F ⋙ s.inclusion l Ω Y ≅ s.inclusion l Ω X ⋙
    PurCompactSupport.image (s.coefficients l) c

/-- The q map is the canonical scalar-adjunction mate of the proper/open restriction
square, expressed through the actual scalar and support realizations. In particular
it is not an arbitrarily selected natural isomorphism.
Source: blueprint canonical q construction
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
def QNormalized {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {s t : RingStage.{u} l}
    {A : Operation l Ω X Y (s.stage l)} {B : Operation l Ω X Y (t.stage l)}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (SX : Scalar l Ω a X) (SY : Scalar l Ω a Y)
    (rA : LeftRealization l Ω c s A) (rB : LeftRealization l Ω c t B)
    (d : Comparison l Ω A B SX.functor SY.functor) : Prop :=
  ∀ K : C l Ω X (s.stage l),
    (t.inclusion l Ω Y).map (d.q.hom.app K) ≫
        rB.hom.app (SX.functor.obj K) ≫
        (PurCompactSupport.image (t.coefficients l) c).map (SX.realization.hom.app K) =
      SY.realization.hom.app (A.F.obj K) ≫
        (pbcDerivedExtend (a.map Y)).map (rA.hom.app K) ≫
        (PurCompactSupport.comparison a c).app ((s.inclusion l Ω X).obj K)


/-- Scalar associators are the existing tensor-unit-normalized adjunction comparisons,
lifted through the full inclusions. Source: blueprint coefficient composition
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure ScalarComposition {s t r : RingStage.{u} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l)}
    {d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l)}
    (h : ∀ W : Scheme.{u}, a.map W ≫ b.map W = d.map W) (T : Scheme.{u})
    (A : Scalar l Ω a T) (B : Scalar l Ω b T) (D : Scalar l Ω d T) where
  iso : A.functor ⋙ B.functor ≅ D.functor
  normalized (K : C l Ω T (s.stage l)) :
    (r.inclusion l Ω T).map (iso.hom.app K) ≫ D.realization.hom.app K =
      B.realization.hom.app (A.functor.obj K) ≫
        (pbcDerivedExtend (b.map T)).map (A.realization.hom.app K) ≫
        (PurCompactSupport.tensorComposition (a.map T) (b.map T) (d.map T) (h T)).hom.app
          ((s.inclusion l Ω T).obj K)

/-- Identity scalar extension is normalized by multiplication, through the existing
scalar adjunction. Source: blueprint identity coefficient change
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure ScalarIdentity {s : RingStage.{u} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ W : Scheme.{u}, a.map W = 𝟙 _) (T : Scheme.{u}) (A : Scalar l Ω a T) where
  iso : A.functor ≅ 𝟭 _
  normalized (K : C l Ω T (s.stage l)) :
    (s.inclusion l Ω T).map (iso.hom.app K) =
      A.realization.hom.app K ≫
        (eqToIso (congrArg pbcDerivedExtend (h T))).hom.app
          ((s.inclusion l Ω T).obj K) ≫
        (PurCompactSupport.tensorIdentity ((s.coefficients l).ring T)).hom.app
          ((s.inclusion l Ω T).obj K)

/-- Rationalization on the integral finite-Tor category uses the specified raw scalar
localization, with the same integral representatives. Source: blueprint R to E
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev rationalization (E : FieldStage.{u} l) (T : Scheme.{u}) :
    C l Ω T (.integral E) ⥤ C l Ω T (.rational E) :=
  PurCompactSupport.finiteTorIntegralInclusion l E.carrier T ⋙
    sfRationalConstructibleLocalization l E.carrier T

/-- The actual completed scalar functor after rationalization. The parameter zero is
only the proof parameter of the published intrinsic construction, independent of the
geometric characteristic. Source: blueprint rational coefficient extension
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (T : Scheme.{u}) : C l Ω T (.rational E) ⥤ C l Ω T (.rational L) :=
  sfRationalScalarExtension l E.carrier T 0 (Fact.out : l.Prime).ne_zero L.carrier i

/-- The canonical small field model of a common coefficient stage.
Source: blueprint common-stage coefficient category
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev commonField (i : AlgebraicallyClosedCoefficients.Index l Ω) : FieldStage.{u} l where
  carrier := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i

/-- Select one endpoint of the fixed morphism, without imposing extra geometric
hypotheses on arbitrary schemes. Source: blueprint fixed X and Y
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev endpoint (X Y : Scheme.{u}) (side : Bool) : Scheme.{u} :=
  if side then X else Y

/-- Coefficient equations with the shift structures supplied as output data, for the
published raw rationalization, rational extension, and finite-stage inclusion functors.
Source: blueprint rational and common-stage comparisons
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure FieldComparison {X Y : Scheme.{u}} {s t : Stage.{u} l}
    (A : Operation l Ω X Y s) (B : Operation l Ω X Y t)
    (TX : C l Ω X s ⥤ C l Ω X t) (TY : C l Ω Y s ⥤ C l Ω Y t) where
  [shiftX : TX.CommShift ℤ]
  [shiftY : TY.CommShift ℤ]
  comparison : Comparison l Ω A B TX TY

/-- Left comparison with the output shift structures retained in its type.
Source: blueprint coefficient q (blueprint:
lem-sf-constructible-exceptional-adjunction-coefficients).
-/
def FieldComparison.q {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {A : Operation l Ω X Y s} {B : Operation l Ω X Y t}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    (d : FieldComparison l Ω A B TX TY) : A.F ⋙ TY ≅ TX ⋙ B.F :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.q

/-- Right comparison with the output shift structures retained in its type.
Source: blueprint coefficient b (blueprint:
lem-sf-constructible-exceptional-adjunction-coefficients).
-/
def FieldComparison.b {X Y : Scheme.{u}} {s t : Stage.{u} l}
    {A : Operation l Ω X Y s} {B : Operation l Ω X Y t}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    (d : FieldComparison l Ω A B TX TY) : A.G ⋙ TX ≅ TY ⋙ B.G :=
  letI := d.shiftX
  letI := d.shiftY
  d.comparison.b

/-- The same cocycle at field stages, retaining the existing scalar associators.
Source: blueprint composition and common-stage clauses
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
def FieldCocycle {X Y : Scheme.{u}} {s t r : Stage.{u} l}
    {A : Operation l Ω X Y s} {B : Operation l Ω X Y t} {D : Operation l Ω X Y r}
    {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
    {UX : C l Ω X t ⥤ C l Ω X r} {UY : C l Ω Y t ⥤ C l Ω Y r}
    {VX : C l Ω X s ⥤ C l Ω X r} {VY : C l Ω Y s ⥤ C l Ω Y r}
    (a : FieldComparison l Ω A B TX TY) (b : FieldComparison l Ω B D UX UY)
    (d : FieldComparison l Ω A D VX VY) (αX : TX ⋙ UX ≅ VX) (αY : TY ⋙ UY ≅ VY) : Prop :=
  letI := a.shiftX
  letI := a.shiftY
  letI := b.shiftX
  letI := b.shiftY
  letI := d.shiftX
  letI := d.shiftY
  Cocycle l Ω a.comparison b.comparison d.comparison αX αY

/-- The published finite-stage inclusion with both endpoint categories explicit.
Source: blueprint common-stage category
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
abbrev commonInclusion (T : Scheme.{u}) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    C l Ω T (.rational (commonField l Ω i)) ⥤ C l Ω T .closed :=
  GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := T) i

/-- The existing common-stage transition isomorphism, transported from the opaque
stage-system transition to the actual rational tensor functor by its defining equality.
Source: blueprint common-stage coefficient convention
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
def commonTransition (T : Scheme.{u}) (i j : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : i ≤ j) :
    rationalScalar l Ω (commonField l Ω i) (commonField l Ω j)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) T ⋙
        commonInclusion l Ω T j ≅
      commonInclusion l Ω T i :=
  eqToIso (congrArg (fun F ↦ F ⋙ commonInclusion l Ω T j)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω T).exists.choose_spec.1
      i j h).symm) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).transIso h

/-- Refinement is the counit-normalized conjugate comparison between the two adjunctions.
Both displayed equations retain all functor components, including the unit equation.
Source: blueprint compactification refinement and uniqueness of right adjoints
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure RefinementComparison {X Y : Scheme.{u}} {s : Stage.{u} l}
    (A B : Operation l Ω X Y s) where
  left : A.F ≅ B.F
  right : B.G ≅ A.G
  counit (L : C l Ω Y s) :
    left.hom.app (B.G.obj L) ≫ B.adjunction.counit.app L =
      A.F.map (right.hom.app L) ≫ A.adjunction.counit.app L
  unit (K : C l Ω X s) :
    B.adjunction.unit.app K ≫ right.hom.app (B.F.obj K) =
      A.adjunction.unit.app K ≫ A.G.map (left.hom.app K)
  leftShift : left.hom.CommShift ℤ
  rightShift : right.hom.CommShift ℤ

/-- The canonical proper/open refinement comparison, normalized by the open unit
and proper counit. The pullback equality is proof data, not a new comparison map.
Source: blueprint compactification-refinement clause; Stacks 0F7B
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
def RingRefinementNormalized {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (s : RingStage.{u} l)
    {A B : Operation l Ω X Y (s.stage l)}
    (rA : LeftRealization l Ω c s A) (rB : LeftRealization l Ω d s B)
    (ρ : RefinementComparison l Ω A B) : Prop :=
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
  ∀ K : C l Ω X (s.stage l),
    ∃ ε : (PurCompactSupport.openExtension (s.coefficients l) d.i).mapDerivedCategory.obj
          ((s.inclusion l Ω X).obj K) ≅
        (PurCompactSupport.push (s.coefficients l) r.hom).obj
          ((PurCompactSupport.openExtension (s.coefficients l) c.i).mapDerivedCategory.obj
            ((s.inclusion l Ω X).obj K)),
      (PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv _ _ ε.hom ≫
          PurCompactSupport.refinementRestriction (s.coefficients l) r hi
            ((s.inclusion l Ω X).obj K) =
        (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit.app
          ((s.inclusion l Ω X).obj K) ∧
      rA.inv.app K ≫ (s.inclusion l Ω Y).map (ρ.left.hom.app K) ≫ rB.hom.app K =
        ((PurCompactSupport.geometricPushComposition (s.coefficients l) r.hom d.g hg ≪≫
          eqToIso (congrArg (fun h ↦ PurCompactSupport.push (s.coefficients l) h)
            r.hom_g)).symm.app _).hom ≫
          (PurCompactSupport.push (s.coefficients l) d.g).map ε.inv

/-- The full conclusion, with actual categories and canonical scalar/proper-open
normalizations. All functors and comparisons are output data; no adjunction or
coefficient compatibility is a premise of the theorem asserting this record exists.
Source: current blueprint exceptional-functor paragraph and coefficient compatibility
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure RingSystem (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] where
  operation (c : Compactification f) (s : Stage.{u} l) : Operation l Ω X Y s
  left (c : Compactification f) (s : RingStage.{u} l) :
    LeftRealization l Ω c s (operation c (s.stage l))
  finiteRight (c : Compactification f) (E : FieldStage.{u} l) (n : ℕ+) :
    (operation c (.finite E n)).G ⋙ (RingStage.finite E n).inclusion l Ω X ≅
      (RingStage.finite E n).inclusion l Ω Y ⋙
        @ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E.carrier n) _
          (Padic.finite_coefficientExtensionRing l E.carrier n n.pos) X Y f c
  integralLeft (c : Compactification f) (E : FieldStage.{u} l) :
    (operation c (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
  integralLeft_normalized (c : Compactification f) (E : FieldStage.{u} l)
      (K : C l Ω X (.integral E)) :
    ((sfIntegralConstructible l E.carrier Y).ι.map
        ((integralLeft c E).hom.app K)) =
      (left c (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl)
          c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  rationalLeft (c : Compactification f) (E : FieldStage.{u} l) :
    (operation c (.rational E)).F ≅
      sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c
          E.carrier
  scalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) (side : Bool) : Scalar l Ω a (endpoint X Y side)
  finiteScalar_eq {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).functor ⋙
        (RingStage.finite E n).inclusion l Ω (endpoint X Y side) =
      s.inclusion l Ω (endpoint X Y side) ⋙ pbcDerivedExtend (a.map (endpoint X Y side))
  finiteScalar_normalized {s : RingStage.{u} l} (E : FieldStage.{u} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a) (side : Bool) :
    (scalar (s := s) (t := .finite E n) a ha side).realization =
      eqToIso (finiteScalar_eq (s := s) E n a ha side)
  integralScalar_eq (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (side : Bool) :
    (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).functor ⋙
        (RingStage.integral L).inclusion l Ω (endpoint X Y side) =
      (RingStage.integral E).inclusion l Ω (endpoint X Y side) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i (endpoint X Y side)
  integralScalar_normalized (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (side : Bool)
      (K : C l Ω (endpoint X Y side) (.integral E)) :
    HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i) side).realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i (endpoint X Y side)).app K.obj)
  comparison (c : Compactification f) {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    Comparison l Ω (operation c (s.stage l)) (operation c (t.stage l))
      (scalar a ha true).functor (scalar a ha false).functor
  comparison_normalized (c : Compactification f) {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a) :
    QNormalized l Ω c a (scalar a ha true) (scalar a ha false)
      (left c s) (left c t) (comparison c a ha)
  scalarComposition {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) (side : Bool) :
    ScalarComposition l Ω h (endpoint X Y side)
      (scalar a ha side) (scalar b hb side) (scalar d hd side)
  cocycle (c : Compactification f) {s t r : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l))
      (d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T ≫ b.map T = d.map T)
      (ha : Allowed l a) (hb : Allowed l b) (hd : Allowed l d) :
    Cocycle l Ω (comparison c a ha) (comparison c b hb) (comparison c d hd)
      (scalarComposition a b d h ha hb hd true).iso
      (scalarComposition a b d h ha hb hd false).iso
  scalarIdentity {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a) (side : Bool) :
    ScalarIdentity l Ω h (endpoint X Y side) (scalar a ha side)
  identityLeft (c : Compactification f) {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (K : C l Ω X (s.stage l)) :
    (comparison c a ha).q.hom.app K ≫
        (operation c (s.stage l)).F.map ((scalarIdentity a h ha true).iso.hom.app K) =
      (scalarIdentity a h ha false).iso.hom.app ((operation c (s.stage l)).F.obj K)
  identityRight (c : Compactification f) {s : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{u}, a.map T = 𝟙 _) (ha : Allowed l a)
      (L : C l Ω Y (s.stage l)) :
    (comparison c a ha).b.hom.app L ≫
        (operation c (s.stage l)).G.map ((scalarIdentity a h ha false).iso.hom.app L) =
      (scalarIdentity a h ha true).iso.hom.app ((operation c (s.stage l)).G.obj L)

/-- Rational localization and common-stage descent of the same ring-stage system.
Source: blueprint field-coefficient clauses
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure FieldSystem (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem l Ω D hl (f := f)) where
  rationalizationComparison (c : Compactification f) (E : FieldStage.{u} l) :
    FieldComparison l Ω (R.operation c (.integral E)) (R.operation c (.rational E))
      (rationalization l Ω E X) (rationalization l Ω E Y)
  rationalization_normalized (c : Compactification f) (E : FieldStage.{u} l)
      (K : C l Ω X (.integral E)) :
    (rationalizationComparison c E).q.hom.app K ≫
        (R.rationalLeft c E).hom.app ((rationalization l Ω E X).obj K) =
      (sfRationalConstructibleLocalization l E.carrier Y).map
        ((R.integralLeft c E).hom.app K)
  rationalComparison (c : Compactification f) (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) :
    FieldComparison l Ω (R.operation c (.rational E)) (R.operation c (.rational L))
      (rationalScalar l Ω E L i X) (rationalScalar l Ω E L i Y)
  rational_normalized (c : Compactification f) (E L : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (K : C l Ω X (.integral E)) :
    HEq ((rationalComparison c E L i).q.hom.app
        ((rationalization l Ω E X).obj K))
      ((rationalization l Ω L Y).map
        ((Scalar.q l Ω
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) true)
          (R.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) false)
          (R.comparison c (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i))).hom.app K))
  rationalCocycle (c : Compactification f) (E L M : FieldStage.{u} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier) :
    FieldCocycle l Ω (rationalComparison c E L i) (rationalComparison c L M j)
      (rationalComparison c E M (j.comp i))
      (sfRationalScalarComp l E.carrier L.carrier i X 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j)
  rationalIdentityLeft (c : Compactification f) (E : FieldStage.{u} l)
      (K : C l Ω X (.rational E)) :
    (rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).q.hom.app K ≫
        (R.operation c (.rational E)).F.map
          ((sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).F.obj K)
  rationalIdentityRight (c : Compactification f) (E : FieldStage.{u} l)
      (L : C l Ω Y (.rational E)) :
    (rationalComparison c E E (AlgHom.id (Padic l) E.carrier)).b.hom.app L ≫
        (R.operation c (.rational E)).G.map
          ((sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app L) =
      (sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((R.operation c (.rational E)).G.obj L)
/-- Common coefficient stages and compactification refinement of the fixed system.
Source: blueprint common-stage and refinement clauses
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure CommonSystem (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem l Ω D hl (f := f)) (F : FieldSystem l Ω D hl R) where
  commonComparison (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    FieldComparison l Ω (R.operation c (.rational (commonField l Ω i))) (R.operation c .closed)
      (commonInclusion l Ω X i) (commonInclusion l Ω Y i)
  common_normalized (c : Compactification f)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C l Ω X (.rational (commonField l Ω i))) :
    HEq ((commonComparison c i).q.hom.app K)
      (𝟙 ((commonInclusion l Ω Y i).obj
        ((R.operation c (.rational (commonField l Ω i))).F.obj K)))
  commonCocycleLeft (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C l Ω X (.rational (commonField l Ω i))) :
    HEq
      ((commonInclusion l Ω Y j).map
          ((F.rationalComparison c (commonField l Ω i) (commonField l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).q.hom.app
              K) ≫
        (commonComparison c j).q.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X i j h).obj K))
      ((commonTransition l Ω Y i j h).hom.app
            ((R.operation c (.rational (commonField l Ω i))).F.obj K) ≫
        (commonComparison c i).q.hom.app K ≫
        (R.operation c .closed).F.map
          ((commonTransition l Ω X i j h).inv.app K))
  commonCocycleRight (c : Compactification f)
      (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (L : C l Ω Y (.rational (commonField l Ω i))) :
    HEq
      ((commonInclusion l Ω X j).map
          ((F.rationalComparison c (commonField l Ω i) (commonField l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).b.hom.app
              L) ≫
        (commonComparison c j).b.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.transition l Ω Y i j h).obj L))
      ((commonTransition l Ω X i j h).hom.app
            ((R.operation c (.rational (commonField l Ω i))).G.obj L) ≫
        (commonComparison c i).b.hom.app L ≫
        (R.operation c .closed).G.map
          ((commonTransition l Ω Y i j h).inv.app L))
/-- Compactification refinements, retaining the counit-conjugate right comparisons.
Source: blueprint refinement clause
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure RefinementSystem (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem l Ω D hl (f := f)) (F : FieldSystem l Ω D hl R)
    (M : CommonSystem l Ω D hl R F) where
  refinement {c d : Compactification f} (r : c.Refinement d) (s : Stage.{u} l) :
    RefinementComparison l Ω (R.operation c s) (R.operation d s)
  refinement_normalized {c d : Compactification f} (r : c.Refinement d)
      (s : RingStage.{u} l) :
    RingRefinementNormalized l Ω r s (R.left c s) (R.left d s) (refinement r (s.stage l))
  refinementRational {c d : Compactification f} (r : c.Refinement d)
      (E : FieldStage.{u} l) (K : C l Ω X (.integral E)) :
    HEq ((refinement r (.rational E)).left.hom.app ((rationalization l Ω E X).obj K))
      ((rationalization l Ω E Y).map ((refinement r (.integral E)).left.hom.app K))
  refinementCommon {c d : Compactification f} (r : c.Refinement d)
      (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C l Ω X (.rational (commonField l Ω i))) :
    (M.commonComparison c i).q.inv.app K ≫
        (commonInclusion l Ω Y i).map
          ((refinement r (.rational (commonField l Ω i))).left.hom.app K) ≫
        (M.commonComparison d i).q.hom.app K =
      (refinement r .closed).left.hom.app
        ((commonInclusion l Ω X i).obj K)
  refinementIdentity (c : Compactification f) (s : Stage.{u} l) :
    (refinement (Compactification.Refinement.id c) s).left = Iso.refl _
  refinementComposition {a b c : Compactification f}
      (r : a.Refinement b) (t : b.Refinement c) (s : Stage.{u} l) :
    (refinement (r.comp t) s).left = (refinement r s).left ≪≫ (refinement t s).left

/-- One joint family of ring, field, common-stage and refinement conclusions.
The later records refer to the very same operation and comparison data in the earlier ones.
Source: blueprint constructible adjunction with coefficients
(blueprint: lem-sf-constructible-exceptional-adjunction-coefficients). -/
structure System (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
 where
  ring : RingSystem l Ω D hl (f := f)
  fields : FieldSystem l Ω D hl ring
  common : CommonSystem l Ω D hl ring fields
  refinements : RefinementSystem l Ω D hl ring fields common

end ConstructibleExceptionalCoefficients
end WeilConjectures
