# Constructible exceptional compositor data module

## Reason

The geometric left-compositor coherence theorem needs `LeftCompositors`, `finiteAlpha`,
`integralAlpha` and their published comparison data. The final theorem combines this
left coherence with formal mate calculations. Move the existing data verbatim to
`Sheaf.Paper.ConstructibleExceptionalCompositorData` and publicly re-export it from the
original module, avoiding an import cycle. This refactor is for that dependency, not
for a compile time limit. No declaration name or signature is changed. The auxiliary
integral-support equality receives a proof via normalized projections and finite Hom.

## Old

The following exact pre-existing interface was defined directly in
`Sheaf.Paper.ConstructibleExceptionalCompositor`:

```lean
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.CompactifiedTowerComparisons
import Sheaf.Paper.FiniteStructuralMapsCommShift
import Sheaf.SixFunctors.IntegralRealizationShiftCoherence
import Sheaf.Paper.PbcRationalTransport
import Sheaf.CategoryTheory.StageSystemFunctorDescent

/-! # Canonical constructible exceptional composition

Source: blueprint main-20261015, Verdier exchange, proof Step 1
(blueprint: lem-sf-constructible-exceptional-compositor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- Change from the finite tensor-pullback presentation to the published fixed-scalar
one, preserving the ordinary units. The coefficient-identification transport has
identity hom. Source: blueprint finite exceptional adjunction
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def constructibleFinitePullIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModulePullback f
        ((PurCompactSupport.finite l E n n.pos).ring Y)
        ((PurCompactSupport.finite l E n n.pos).ring X)
        ((PurCompactSupport.finite l E n n.pos).pull f) ≅
      @sfIntrinsicPullback (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n n.pos) X Y f :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n n.pos
  eqToIso (congrArg
      (fun e ↦ proEtaleRingModulePullback f
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)) e)
      (Iso.ext (by rfl) :
        @sfConstantCoefficientIso X Y f (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n n.pos) =
        proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E n))) ≪≫
    @openSquarePullbackModel (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n n.pos) X Y f

/-- The finite proper/open presentations are compared by their unit-normalized
adjunctions, then by termwise and K-injective descent.
Source: blueprint finite exceptional adjunction, ordinary open-extension comparison
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def constructibleFiniteImageIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    PurCompactSupport.image (PurCompactSupport.finite l E n n.pos) c ≅
      @sfIntrinsicCompactSupport X Y f c (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n n.pos) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n n.pos
  letI : IsOpenImmersion c.i := c.isOpenImmersion
  letI : (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)).Additive :=
    sfIntrinsicExtensionByZero_additive c.i (Padic.coefficientExtensionRing l E n)
  letI : Limits.PreservesFiniteLimits
      (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)) :=
    sfIntrinsicExtensionByZero_preservesFiniteLimits c.i (Padic.coefficientExtensionRing l E n)
  letI : Limits.PreservesFiniteColimits
      (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)) :=
    sfIntrinsicExtensionByZero_preservesFiniteColimits c.i (Padic.coefficientExtensionRing l E n)
  letI : (proEtaleConstantModuleDirectImage c.g
      (Padic.coefficientExtensionRing l E n)).Additive :=
    proEtaleConstantModuleDirectImage_additive c.g (Padic.coefficientExtensionRing l E n)
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (((PurCompactSupport.openAdjunction
          (PurCompactSupport.finite l E n n.pos) c.i).ofNatIsoRight
            (constructibleFinitePullIso l E n c.i)).leftAdjointUniq
          (@sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n n.pos) X c.Z c.i
            c.isOpenImmersion))) _ ≪≫
  Functor.isoWhiskerLeft _
    (Functor.rightDerivedFunctorNatIso
      (((proEtaleRingModuleAdjunction c.g
          (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
          (proEtaleConstantRing c.Z (Padic.coefficientExtensionRing l E n))
          (@sfConstantCoefficientIso c.Z Y c.g (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n n.pos))).ofNatIsoLeft
              (constructibleFinitePullIso l E n c.g)).rightAdjointUniq
        (@sfIntrinsicConstantModuleAdjunction c.Z Y c.g
          (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n n.pos))))

/-- The operation datum's integral support is the specified normalized realization.
Source: blueprint exceptional adjunction, integral construction, and the operation
normalizations (blueprint: lem-sf-constructible-exceptional-compositor).

Proof:
1. Project supportConstruction from S.higher and the realization specification of
   sfCompactSupportFiniteIntegralFunctor. Their object-normalization clauses give
   the same sfIntegralCompactSupportValue, so first transport to these fixed objects.
2. For a morphism v, naturality of the two strict-tower comparisons and their
   projection normalizations identify the composites of both image maps with every
   fixed Roos projection. The finite maps are the same proper/open reduction maps.
3. To deduce equality of the image maps, apply the Milnor exact sequence for maps
   into the total derived inverse limit. Its kernel is lim^1 of the degree-minus-one
   Hom tower. Reduction adjunction identifies these Hom groups with finite-level
   constructible Ext groups. They are finite by constructible etale finiteness over
   the algebraically closed finite-field base, using etale origin and the common
   bounded constructible intervals. An inverse sequence of finite groups is
   Mittag-Leffler: in each finite target its descending images stabilize. Hence this
   lim^1 vanishes. Equality of the fixed projection composites now implies equality
   of maps into this total limit. This uses finiteness, not faithfulness of finite
   evaluation on arbitrary derived systems.
4. The full-subcategory inclusion is faithful. Apply functor extensionality to the
   object equalities and transported map equalities; proof irrelevance identifies
   the constructibility witnesses. This proves equality of the normalized functors,
   so eqToIso below is the identity transport of their common normalization. -/
theorem constructibleIntegralSupport_eq
    (D : FiniteFieldDatum.{u}) (B : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic B.l) E]
    [FiniteDimensional (Padic B.l) E] (n : ℕ+) (S : SixFunctorOperationDatum D B E n n.pos)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) :
    S.higher.integral.support f c =
      sfCompactSupportFiniteIntegralFunctor B.l D.k
        (PurCompactSupport.coefficientPrimeUnit B.l D B.different) c E := by
  sorry


end WeilConjectures

namespace WeilConjectures.ConstructibleExceptionalCompositor
open ConstructibleExceptionalCoefficients
variable {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)

/-- The existing finite-Tor full subcategory included in the constructible category.
Source: blueprint finite-Tor convention
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def finiteInclusion (E : FieldStage.{u} B.l) (n : ℕ+) (X : SixFunctorSpace D) :
    C B.l B.Qbar X.obj.left (.finite E n) ⥤ sixFunctorFiniteCategory D B E.carrier n n.pos X :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1)

/-- Integral inclusion is the dependency's recorded inclusion.
Source: blueprint completed finite-Tor convention
(blueprint: lem-sf-constructible-exceptional-compositor). -/
abbrev integralInclusion (E : FieldStage.{u} B.l) (X : SixFunctorSpace D) :=
  PurCompactSupport.finiteTorIntegralInclusion B.l E.carrier X.obj.left

section OneArrow
variable {X Y : SixFunctorSpace D} (f : X ⟶ Y)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (P : System B.l B.Qbar D B.different (f := f.hom.left))

/-- The finite comparison is the unique lift of the two specified ambient realizations.
No new comparison map is chosen. Source: blueprint compact-support restriction
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def finiteLeft (E : FieldStage.{u} B.l) (n : ℕ+)
    (S : SixFunctorOperationDatum D B E.carrier n n.pos) (c : Compactification f.hom.left) :
    (P.ring.operation c (.finite E n)).F ⋙ finiteInclusion B E n Y ≅
      finiteInclusion B E n X ⋙ S.finite.support f c :=
  ((intrinsicFiniteTorsionConstructible B.l E.carrier n n.pos
    Y.obj.left).fullyFaithfulι.whiskeringRight _).preimageIso
    (X := (P.ring.operation c (.finite E n)).F ⋙ finiteInclusion B E n Y)
    (Y := finiteInclusion B E n X ⋙ S.finite.support f c)
    (P.ring.left c (.finite E n) ≪≫
      Functor.isoWhiskerLeft _ (constructibleFiniteImageIso B.l E.carrier n c) ≪≫
      (Functor.isoWhiskerLeft (finiteInclusion B E n X) (S.finiteSupport f c)).symm)

/-- The integral comparison is fixed by the normalized integral realization, and the
identity transport between the two presentations of that same realization.
Source: blueprint completed support construction
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def integralLeft (E : FieldStage.{u} B.l)
    (S : SixFunctorOperationDatum D B E.carrier 1 (by decide))
    (c : Compactification f.hom.left) :
    (P.ring.operation c (.integral E)).F ⋙ integralInclusion B E Y ≅
      integralInclusion B E X ⋙ S.higher.integral.support f c :=
  P.ring.integralLeft c E ≪≫ Functor.isoWhiskerLeft (integralInclusion B E X)
    (eqToIso (constructibleIntegralSupport_eq D B E.carrier 1 S f c).symm)

end OneArrow

/-- The composite in the full over category has its original underlying scheme map.
Source: blueprint composable finite-type morphisms
(blueprint: lem-sf-constructible-exceptional-compositor). -/
instance separatedComp {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [IsSeparated g.hom.left] :
    IsSeparated (f ≫ g).hom.left :=
  inferInstanceAs (IsSeparated (f.hom.left ≫ g.hom.left))

/-- Finite type is stable under composition, with no new hypothesis.
Source: blueprint composable finite-type morphisms
(blueprint: lem-sf-constructible-exceptional-compositor). -/
instance lftComp {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f.hom.left] [LocallyOfFiniteType g.hom.left] :
    LocallyOfFiniteType (f ≫ g).hom.left :=
  inferInstanceAs (LocallyOfFiniteType (f.hom.left ≫ g.hom.left))

/-- Quasi-compactness is stable under composition, with no new hypothesis.
Source: blueprint composable finite-type morphisms
(blueprint: lem-sf-constructible-exceptional-compositor). -/
instance qcComp {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left] :
    QuasiCompact (f ≫ g).hom.left :=
  inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))

/-- The exact coefficient comparison equation for a left compositor. Its q maps
are the recorded coefficient maps, including their specified normalizations.
Source: blueprint completed/rational/common compact-support forms
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def LeftCoefficientEquation {X Y Z : Scheme.{u}} {s t : Stage.{u} B.l}
    (A : Operation B.l B.Qbar X Y s) (A' : Operation B.l B.Qbar X Y t)
    (G : Operation B.l B.Qbar Y Z s) (G' : Operation B.l B.Qbar Y Z t)
    (H : Operation B.l B.Qbar X Z s) (H' : Operation B.l B.Qbar X Z t)
    (TX : C B.l B.Qbar X s ⥤ C B.l B.Qbar X t)
    (TY : C B.l B.Qbar Y s ⥤ C B.l B.Qbar Y t)
    (TZ : C B.l B.Qbar Z s ⥤ C B.l B.Qbar Z t)
    (qf : A.F ⋙ TY ≅ TX ⋙ A'.F) (qg : G.F ⋙ TZ ≅ TY ⋙ G'.F)
    (qx : H.F ⋙ TZ ≅ TX ⋙ H'.F)
    (alpha : A.F ⋙ G.F ≅ H.F) (alpha' : A'.F ⋙ G'.F ≅ H'.F) : Prop :=
  ∀ K : C B.l B.Qbar X s,
    TZ.map (alpha.hom.app K) ≫ qx.hom.app K =
      qg.hom.app (A.F.obj K) ≫ G'.F.map (qf.hom.app K) ≫ alpha'.hom.app (TX.obj K)

/-- The exceptional compositor is literally the conjugate of inverse alpha under
the composite constructible adjunction and the direct constructible adjunction.
Source: blueprint Verdier-exchange proof Step 1; Mathlib conjugateIsoEquiv
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def exceptionalIso {X Y Z : Scheme.{u}} {s : Stage.{u} B.l}
    (A : Operation B.l B.Qbar X Y s) (G : Operation B.l B.Qbar Y Z s)
    (H : Operation B.l B.Qbar X Z s) (alpha : A.F ⋙ G.F ≅ H.F) : G.G ⋙ A.G ≅ H.G :=
  conjugateIsoEquiv (A.adjunction.comp G.adjunction) H.adjunction alpha.symm

/-- Hom action, the pasted counit, componentwise uniqueness, and integer-shift
compatibility. Naturality and invertibility are already fields of exceptionalIso.
Source: blueprint Verdier-exchange proof Step 1, expanded mate calculation
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def MateProperties {X Y Z : Scheme.{u}} {s : Stage.{u} B.l}
    (A : Operation B.l B.Qbar X Y s) (G : Operation B.l B.Qbar Y Z s)
    (H : Operation B.l B.Qbar X Z s) (alpha : A.F ⋙ G.F ≅ H.F) : Prop :=
  (∀ (K : C B.l B.Qbar X s) (L : C B.l B.Qbar Z s) (u : K ⟶ (G.G ⋙ A.G).obj L),
    u ≫ (exceptionalIso B A G H alpha).hom.app L =
      H.adjunction.homEquiv K L
        (alpha.inv.app K ≫ ((A.adjunction.comp G.adjunction).homEquiv K L).symm u)) ∧
  (∀ L : C B.l B.Qbar Z s,
    alpha.hom.app ((G.G ⋙ A.G).obj L) ≫
        H.F.map ((exceptionalIso B A G H alpha).hom.app L) ≫ H.adjunction.counit.app L =
      G.F.map (A.adjunction.counit.app (G.G.obj L)) ≫ G.adjunction.counit.app L) ∧
  (∀ (L : C B.l B.Qbar Z s) (t : (G.G ⋙ A.G).obj L ⟶ H.G.obj L),
    (alpha.hom.app ((G.G ⋙ A.G).obj L) ≫ H.F.map t ≫ H.adjunction.counit.app L =
      G.F.map (A.adjunction.counit.app (G.G.obj L)) ≫ G.adjunction.counit.app L) ↔
        t = (exceptionalIso B A G H alpha).hom.app L) ∧
  alpha.hom.CommShift ℤ ∧ (exceptionalIso B A G H alpha).hom.CommShift ℤ

section TwoArrows
variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  (P : System B.l B.Qbar D B.different (f := f.hom.left))
  (Q : System B.l B.Qbar D B.different (f := g.hom.left))
  (R : System B.l B.Qbar D B.different (f := (f ≫ g).hom.left))

/-- Canonical finite compact-support composition, lifted from the published normalized
compactification compositor along the fully faithful finite-Tor inclusion.
Source: blueprint compact-support composition and its finite-Tor restriction
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def finiteAlpha (E : FieldStage.{u} B.l) (n : ℕ+)
    (S : SixFunctorOperationDatum D B E.carrier n n.pos)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left) :
    (P.ring.operation cf (.finite E n)).F ⋙ (Q.ring.operation cg (.finite E n)).F ≅
      (R.ring.operation cx (.finite E n)).F :=
  ((ObjectProperty.fullyFaithfulιOfLE
    (show finiteTorConstructible B.l E.carrier n n.pos Z.obj.left ≤
      intrinsicFiniteTorsionConstructible B.l E.carrier n n.pos Z.obj.left from
        fun _ h ↦ h.1)).whiskeringRight _).preimageIso
    (X := (P.ring.operation cf (.finite E n)).F ⋙ (Q.ring.operation cg (.finite E n)).F)
    (Y := (R.ring.operation cx (.finite E n)).F)
    (Functor.associator (P.ring.operation cf (.finite E n)).F
        (Q.ring.operation cg (.finite E n)).F (finiteInclusion B E n Z) ≪≫
      Functor.isoWhiskerLeft (P.ring.operation cf (.finite E n)).F
        (finiteLeft B g Q E n S cg) ≪≫
      (Functor.associator (P.ring.operation cf (.finite E n)).F
        (finiteInclusion B E n Y) (S.finite.support g cg)).symm ≪≫
      Functor.isoWhiskerRight (finiteLeft B f P E n S cf) (S.finite.support g cg) ≪≫
      Functor.associator (finiteInclusion B E n X)
        (S.finite.support f cf) (S.finite.support g cg) ≪≫
      Functor.isoWhiskerLeft (finiteInclusion B E n X) (S.finite.composition f g cf cg cx).symm ≪≫
      (finiteLeft B (f ≫ g) R E n S cx).symm)

/-- Canonical completed composition, transported through the specified integral
realizations and lifted through the full finite-Tor inclusion. Source: blueprint
completed support composition (blueprint: lem-sf-constructible-exceptional-compositor). -/
def integralAlpha (E : FieldStage.{u} B.l)
    (S : SixFunctorOperationDatum D B E.carrier 1 (by decide))
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left) :
    (P.ring.operation cf (.integral E)).F ⋙ (Q.ring.operation cg (.integral E)).F ≅
      (R.ring.operation cx (.integral E)).F :=
  ((ObjectProperty.fullyFaithfulιOfLE
    (show finiteTorConstructibleIntegral B.l E.carrier Z.obj.left ≤
      sfIntegralConstructible B.l E.carrier Z.obj.left from
        fun _ h ↦ h.1)).whiskeringRight _).preimageIso
    (X := (P.ring.operation cf (.integral E)).F ⋙ (Q.ring.operation cg (.integral E)).F)
    (Y := (R.ring.operation cx (.integral E)).F)
    (Functor.associator (P.ring.operation cf (.integral E)).F
        (Q.ring.operation cg (.integral E)).F (integralInclusion B E Z) ≪≫
      Functor.isoWhiskerLeft (P.ring.operation cf (.integral E)).F
        (integralLeft B g Q E S cg) ≪≫
      (Functor.associator (P.ring.operation cf (.integral E)).F
        (integralInclusion B E Y) (S.higher.integral.support g cg)).symm ≪≫
      Functor.isoWhiskerRight (integralLeft B f P E S cf) (S.higher.integral.support g cg) ≪≫
      Functor.associator (integralInclusion B E X)
        (S.higher.integral.support f cf) (S.higher.integral.support g cg) ≪≫
      Functor.isoWhiskerLeft (integralInclusion B E X)
        (S.higher.integral.composition f g cf cg cx).symm ≪≫
      (integralLeft B (f ≫ g) R E S cx).symm)

/-- The canonical left maps at all four coefficient stages. The finite and integral
maps equal the published compactification maps lifted above, and the field maps
satisfy their actual localization and common-stage component equations. Thus no
unconstrained isomorphism between left adjoints is supplied here.
Source: blueprint Verdier-exchange Step 1, coefficient conventions
(blueprint: lem-sf-constructible-exceptional-compositor). -/
structure LeftCompositors
    (S : ∀ (E : FieldStage.{u} B.l) (n : ℕ+),
      SixFunctorOperationDatum D B E.carrier n n.pos) where
  alpha (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (s : Stage.{u} B.l) :
    (P.ring.operation cf s).F ⋙ (Q.ring.operation cg s).F ≅ (R.ring.operation cx s).F
  finite (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (E : FieldStage.{u} B.l) (n : ℕ+) :
    alpha cf cg cx (.finite E n) = finiteAlpha B f g P Q R E n (S E n) cf cg cx
  integral (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (E : FieldStage.{u} B.l) :
    alpha cf cg cx (.integral E) = integralAlpha B f g P Q R E (S E 1) cf cg cx
  rational (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (E : FieldStage.{u} B.l) :
    LeftCoefficientEquation B
      (P.ring.operation cf (.integral E)) (P.ring.operation cf (.rational E))
      (Q.ring.operation cg (.integral E)) (Q.ring.operation cg (.rational E))
      (R.ring.operation cx (.integral E)) (R.ring.operation cx (.rational E))
      (rationalization B.l B.Qbar E X.obj.left)
      (rationalization B.l B.Qbar E Y.obj.left)
      (rationalization B.l B.Qbar E Z.obj.left)
      (P.fields.rationalizationComparison cf E).q
      (Q.fields.rationalizationComparison cg E).q
      (R.fields.rationalizationComparison cx E).q
      (alpha cf cg cx (.integral E)) (alpha cf cg cx (.rational E))
  common (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left)
      (i : AlgebraicallyClosedCoefficients.Index B.l B.Qbar) :
    LeftCoefficientEquation B
      (P.ring.operation cf (.rational (commonField B.l B.Qbar i)))
      (P.ring.operation cf .closed)
      (Q.ring.operation cg (.rational (commonField B.l B.Qbar i)))
      (Q.ring.operation cg .closed)
      (R.ring.operation cx (.rational (commonField B.l B.Qbar i)))
      (R.ring.operation cx .closed)
      (commonInclusion B.l B.Qbar X.obj.left i)
      (commonInclusion B.l B.Qbar Y.obj.left i)
      (commonInclusion B.l B.Qbar Z.obj.left i)
      (P.common.commonComparison cf i).q (Q.common.commonComparison cg i).q
      (R.common.commonComparison cx i).q
      (alpha cf cg cx (.rational (commonField B.l B.Qbar i))) (alpha cf cg cx .closed)

/-- Independence is the actual commuting refinement square on right adjoints,
with the specified counit-compatible comparisons, in their contravariant direction.
Source: blueprint compactification independence, Verdier-exchange Step 1
(blueprint: lem-sf-constructible-exceptional-compositor). -/
def RefinementIndependent
    {S : ∀ (E : FieldStage.{u} B.l) (n : ℕ+),
      SixFunctorOperationDatum D B E.carrier n n.pos}
    (A : LeftCompositors B f g P Q R S) : Prop :=
  ∀ (cf df : Compactification f.hom.left) (rf : cf.Refinement df)
    (cg dg : Compactification g.hom.left) (rg : cg.Refinement dg)
    (cx dx : Compactification (f ≫ g).hom.left) (rx : cx.Refinement dx)
    (s : Stage.{u} B.l) (L : C B.l B.Qbar Z.obj.left s),
    (P.refinements.refinement rf s).right.hom.app ((Q.ring.operation dg s).G.obj L) ≫
        (P.ring.operation cf s).G.map ((Q.refinements.refinement rg s).right.hom.app L) ≫
        (exceptionalIso B (P.ring.operation cf s) (Q.ring.operation cg s)
          (R.ring.operation cx s) (A.alpha cf cg cx s)).hom.app L =
      (exceptionalIso B (P.ring.operation df s) (Q.ring.operation dg s)
        (R.ring.operation dx s) (A.alpha df dg dx s)).hom.app L ≫
          (R.refinements.refinement rx s).right.hom.app L

end TwoArrows
```

## New

The same declarations, with the same mathematical signatures and definition bodies, are defined in
`Sheaf.Paper.ConstructibleExceptionalCompositorData`. The old module begins with:

```lean
public import Sheaf.Paper.ConstructibleExceptionalCompositorData
```

The mathematical construction bodies are preserved. Explicit universe annotations
fix the existing coefficient universe, and local transparency settings control
elaboration. The proof of `constructibleIntegralSupport_eq` is replaced by the
finite-Hom/Milnor argument. The final theorem's
signature is unchanged. The new left-coherence lemma imports the data module and the
final theorem imports that lemma. Thus all old imports still expose the same interface.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Item refactored; public interface preserved. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | W2 | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Public re-export preserves its existing interface; no edit. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Public re-export preserves its existing interface; no edit. |

The direct importers are AdicPurityScalarNaturality, FiniteCompactSupportCoefficientSquare,
and FiniteExceptionalCompositorCoefficients. The rest are transitive consumers returned
by tools/downstream.py. No consumer is adapted. Explicit universe annotations fix
elaboration to the existing single-universe coefficient categories. The mathematical
signatures and all non-theorem constructions are preserved. The target statements and
the meanings of their definitions are unchanged. Both existing definition attachments
move to the data module; the new node records the remaining data and integral equality.

## Status

landed 20261025T122737-L-1801866 2026-10-25 (merge of deliver/D8/Sheaf.Paper.ConstructibleExceptionalCompositor)
