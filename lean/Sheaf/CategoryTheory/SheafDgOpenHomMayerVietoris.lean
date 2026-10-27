module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
import Sheaf.CategoryTheory.RingedDgScalarAdjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.OpenCoverMateModuleShortExact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.HomologySequence

/-! # Sheaf dg Hom Mayer–Vietoris with derived scalar naturality

Source: Stacks Project, cohomology.tex, Tag 08BW, and sdga.tex, Tags 0FRW,
0FRX and 0FTB. Scalar compatibility is the refinement in the DAG proof
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris).
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- These dependent projections intentionally stay opaque to typeclass reduction.
set_option warn.classDefReducibility false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

attribute [-instance] CategoryTheory.RingedSiteDg.complexMonoidal

namespace CategoryTheory.SheafDg

variable {X : TopCat.{u}} [EssentiallySmall.{w} (Opens X)]
  {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w}}

/-- The additive triangulation on the fixed left-module word localization, normalized
by its signed cones. This is interface data, not an assumption in the existence theorem.
Source: Stacks sdga, 0FT5 and 0FTB
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
class HomTriangulation {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {O : Sheaf J CommRingCat.{w}} (A : Algebra O) where
  [additive : Preadditive (Derived A)]
  [moduleAdditive : (moduleQ A).Additive]
  [zero : HasZeroObject (Derived A)]
  [shiftAdditive : ∀ n : ℤ, (CategoryTheory.shiftFunctor (Derived A) n).Additive]
  [triangles : Pretriangulated (Derived A)]
  [octahedron : IsTriangulated (Derived A)]
  standard (t : Triangle (Derived A)) : t ∈ distTriang (Derived A) ↔ IsConeTriangle A t

attribute [instance 10] HomTriangulation.additive HomTriangulation.zero
  HomTriangulation.shiftAdditive HomTriangulation.triangles HomTriangulation.octahedron

/-- The open-extension and restriction data used by the sequence. Ordinary lower shriek
is the left adjoint of the actual dg restriction; its derived comparison and adjunction
are normalized by that ordinary adjunction, not chosen independently. The shift
comparison of restriction is required to make restriction exact, as in the recorded
scalar model; this excludes a sign-twisted shift comparison such as (-1)^n.
Source: Stacks sdga, 0FRW; cohomology.tex, 08BU
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
class OpenHomGeometry (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w}) where
  [globalTriangulation : ∀ A : Algebra S, HomTriangulation A]
  [openTriangulation : ∀ (A : Algebra S) (U : Opens X),
    HomTriangulation (restrictAlgebra A U)]
  [restrictionAdditive : ∀ (A : Algebra S) (U : Opens X), (derivedRestriction A U).Additive]
  [restrictionShift : ∀ (A : Algebra S) (U : Opens X),
    (derivedRestriction A U).CommShift ℤ]
  restrictionExact (A : Algebra S) (U : Opens X) : (derivedRestriction A U).IsTriangulated
  ordinary (A : Algebra S) (U : Opens X) : LeftModule (restrictAlgebra A U) ⥤ LeftModule A
  ordinaryAdjunction (A : Algebra S) (U : Opens X) : ordinary A U ⊣ restriction A U
  lower (A : Algebra S) (U : Opens X) : Derived (restrictAlgebra A U) ⥤ Derived A
  adjunction (A : Algebra S) (U : Opens X) : lower A U ⊣ derivedRestriction A U
  comparison (A : Algebra S) (U : Opens X) :
    moduleQ (restrictAlgebra A U) ⋙ lower A U ≅ ordinary A U ⋙ moduleQ A
  coverIso (A : Algebra S) (U : Opens X) :
    moduleQ A ⋙ (derivedRestriction A U ⋙ lower A U) ≅
      (restriction A U ⋙ ordinary A U) ⋙ moduleQ A
  coverIso_eq (A : Algebra S) (U : Opens X) (M : LeftModule A) :
    (coverIso A U).hom.app M =
      (lower A U).map (eqToHom (congrArg (fun F ↦ F.obj M)
        (existsUnique_derivedRestriction A U).choose_spec.1)) ≫
      (comparison A U).hom.app ((restriction A U).obj M)
  counit (A : Algebra S) (U : Opens X) (M : LeftModule A) :
    (adjunction A U).counit.app ((moduleQ A).obj M) =
      (lower A U).map
        (eqToHom (congrArg (fun F ↦ F.obj M)
          (existsUnique_derivedRestriction A U).choose_spec.1)) ≫
      (comparison A U).hom.app ((restriction A U).obj M) ≫
      (moduleQ A).map ((ordinaryAdjunction A U).counit.app M)

attribute [instance 10] OpenHomGeometry.globalTriangulation
  OpenHomGeometry.openTriangulation
  OpenHomGeometry.restrictionAdditive OpenHomGeometry.restrictionShift

/-- Restrict and extend by zero, before localization. Source: Stacks 08BU
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def coverOrdinary [g : OpenHomGeometry S] (A : Algebra S) (U : Opens X) :=
  restriction A U ⋙ g.ordinary A U

/-- Restrict and extend by zero, after localization. Source: Stacks 08BU
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def coverDerived [g : OpenHomGeometry S] (A : Algebra S) (U : Opens X) :=
  derivedRestriction A U ⋙ g.lower A U

/-- The comparison is the localization factorization followed by the specified lower
shriek comparison. Source: Stacks 0FRW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def coverComparison [g : OpenHomGeometry S] (A : Algebra S) (U : Opens X) :
    moduleQ A ⋙ coverDerived A U ≅ coverOrdinary A U ⋙ moduleQ A :=
  g.coverIso A U

/-- Nested extension maps. The ordinary map is uniquely fixed by the counit equation;
the derived map is its localization, as the comparison equation records on every dg
module. This prevents an arbitrary replacement of the restriction maps.
Source: Stacks 08BU, 0FRW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
structure OpenHomInclusions [g : OpenHomGeometry S] where
  ordinary (A : Algebra S) {W U : Opens X} (h : W ≤ U) :
    coverOrdinary A W ⟶ coverOrdinary A U
  ordinary_characterization (A : Algebra S) {W U : Opens X} (h : W ≤ U)
      (τ : coverOrdinary A W ⟶ coverOrdinary A U) :
    τ ≫ (g.ordinaryAdjunction A U).counit = (g.ordinaryAdjunction A W).counit ↔
      τ = ordinary A h
  derived (A : Algebra S) {W U : Opens X} (h : W ≤ U) :
    coverDerived A W ⟶ coverDerived A U
  localization (A : Algebra S) {W U : Opens X} (h : W ≤ U) (M : LeftModule A) :
    (derived A h).app ((moduleQ A).obj M) ≫ (coverComparison A U).hom.app M =
      (coverComparison A W).hom.app M ≫ (moduleQ A).map ((ordinary A h).app M)

/-- The first ordinary cover arrow has the opposite signs on its two components.
Source: Stacks 08BU (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def ordinaryCoverFirst [OpenHomGeometry S] (i : OpenHomInclusions (S := S))
    (A : Algebra S) (U V : Opens X) (M : LeftModule A) :=
  biprod.lift ((i.ordinary A (W := U ⊓ V) (U := U) inf_le_left).app M)
    (-((i.ordinary A (W := U ⊓ V) (U := V) inf_le_right).app M))

/-- The second ordinary cover arrow is the sum of the two counits.
Source: Stacks 08BU (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def ordinaryCoverSecond [g : OpenHomGeometry S] (A : Algebra S)
    (U V : Opens X) (M : LeftModule A) :=
  biprod.desc ((g.ordinaryAdjunction A U).counit.app M)
    ((g.ordinaryAdjunction A V).counit.app M)

/-- A natural cover triangle and its signed-cone normalization. The equation with q
specifies exactly the boundary -p q⁻¹, including its sign, on every representative.
The inl/inr equations fix q as (b,0), not an arbitrary quasi-isomorphism.
Source: Stacks 08BU, 08BW, sdga 0FTB
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
structure OpenHomTriangles [g : OpenHomGeometry S] (i : OpenHomInclusions (S := S))
    (U V : Opens X) where
  boundary (A : Algebra S) :
    𝟭 (Derived A) ⟶ coverDerived A (U ⊓ V) ⋙ CategoryTheory.shiftFunctor (Derived A) (1 : ℤ)
  distinguished (A : Algebra S) (P : Derived A) :
    Triangle.mk
      (biprod.lift ((i.derived A (W := U ⊓ V) (U := U) inf_le_left).app P)
        (-((i.derived A (W := U ⊓ V) (U := V) inf_le_right).app P)))
      (biprod.desc ((g.adjunction A U).counit.app P) ((g.adjunction A V).counit.app P))
      ((boundary A).app P) ∈ distTriang (Derived A)
  cone_normalization (A : Algebra S) (M : LeftModule A) :
    ∃ q : cone A (ordinaryCoverFirst i A U V M) ⟶ M,
      IsIso ((moduleQ A).map q) ∧
      coneIn A (ordinaryCoverFirst i A U V M) ≫ q = ordinaryCoverSecond A U V M ∧
      (∀ n : ℤ, (CochainComplex.mappingCone.inl
        (ordinaryCoverFirst i A U V M).hom).v (n + 1) n (by omega) ≫ q.hom.f n = 0) ∧
      (moduleQ A).map q ≫ (boundary A).app ((moduleQ A).obj M) =
        (moduleQ A).map (coneConnecting A (ordinaryCoverFirst i A U V M)) ≫
          (shiftObjectIso A 1 ((coverOrdinary A (U ⊓ V)).obj M)).hom ≫
          ((coverComparison A (U ⊓ V)).inv.app M)⟦(1 : ℤ)⟧'

/-- H_Z^n is the Hom in the fixed restricted left dg localization.
Source: Stacks 08BW (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
abbrev OpenHom [OpenHomGeometry S] (A : Algebra S) (Z : Opens X)
    (P Q : Derived A) (n : ℤ) :=
  (derivedRestriction A Z).obj P ⟶ ((derivedRestriction A Z).obj Q)⟦n⟧

/-- Restriction followed by its coherent shift identification.
Source: Stacks 08BW (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def homRestrict [OpenHomGeometry S] (A : Algebra S) (Z : Opens X)
    {P Q : Derived A} (n : ℤ) (f : P ⟶ Q⟦n⟧) : OpenHom A Z P Q n :=
  (derivedRestriction A Z).map f ≫ ((derivedRestriction A Z).commShiftIso n).hom.app Q

/-- Adjunction identifies a restricted shifted Hom with a global Hom from lower shriek.
The inverse shift comparison is essential in this transpose.
Source: Stacks 08BT, 08BW (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def homAdjunct [g : OpenHomGeometry S] (A : Algebra S) (Z : Opens X)
    {P Q : Derived A} (n : ℤ) (f : OpenHom A Z P Q n) :
    (coverDerived A Z).obj P ⟶ Q⟦n⟧ :=
  ((g.adjunction A Z).homEquiv _ _).symm
    (f ≫ ((derivedRestriction A Z).commShiftIso n).inv.app Q)

/-- Restriction between opens is precomposition by the canonical nested extension
map under the actual open adjunctions. Source: Stacks 08BW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def homRestrictNested [g : OpenHomGeometry S] (i : OpenHomInclusions (S := S))
    (A : Algebra S) {W Z : Opens X} (h : W ≤ Z) {P Q : Derived A}
    (n : ℤ) (f : OpenHom A Z P Q n) : OpenHom A W P Q n :=
  (g.adjunction A W).homEquiv _ _
      ((i.derived A h).app P ≫ homAdjunct A Z n f) ≫
    ((derivedRestriction A W).commShiftIso n).hom.app Q

/-- The X-to-U,V arrow. Source: Stacks 08BW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def homCoverRestrict [OpenHomGeometry S] (A : Algebra S) (U V : Opens X)
    {P Q : Derived A} (n : ℤ) (f : P ⟶ Q⟦n⟧) :
    OpenHom A U P Q n × OpenHom A V P Q n :=
  (homRestrict A U n f, homRestrict A V n f)

/-- Difference of restrictions on the intersection. Source: Stacks 08BW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def homCoverDifference [OpenHomGeometry S] (i : OpenHomInclusions (S := S))
    (A : Algebra S) (U V : Opens X) {P Q : Derived A} (n : ℤ)
    (f : OpenHom A U P Q n × OpenHom A V P Q n) : OpenHom A (U ⊓ V) P Q n :=
  homRestrictNested i A inf_le_left n f.1 - homRestrictNested i A inf_le_right n f.2

/-- Boundary obtained by shifting the adjunct and composing with the signed cover
boundary; shift addition identifies (Q[n])[1] with Q[n+1]. Source: Stacks 08BW, 0FTB
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def homCoverBoundary [OpenHomGeometry S] {i : OpenHomInclusions (S := S)}
    {U V : Opens X} (t : OpenHomTriangles i U V) (A : Algebra S)
    {P Q : Derived A} (n : ℤ) (f : OpenHom A (U ⊓ V) P Q n) : P ⟶ Q⟦n + 1⟧ :=
  (t.boundary A).app P ≫ (homAdjunct A (U ⊓ V) n f)⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd (Derived A) n 1).inv.app Q

/-- Exactness in every integer degree, including the three positions. Additivity makes
the finite product of two Hom groups their direct sum.
Source: Stacks 08BW (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def HomCoverExact [OpenHomGeometry S] {i : OpenHomInclusions (S := S)}
    {U V : Opens X} (t : OpenHomTriangles i U V) : Prop :=
  ∀ (A : Algebra S) (P Q : Derived A) (n : ℤ),
    Function.Exact (homCoverRestrict A U V (P := P) (Q := Q) n)
      (homCoverDifference i A U V n) ∧
    Function.Exact (homCoverDifference i A U V (P := P) (Q := Q) n)
      (homCoverBoundary t A n) ∧
    Function.Exact (homCoverBoundary t A (P := P) (Q := Q) n)
      (homCoverRestrict A U V (n + 1))

/-- All three sequence arrows are homomorphisms of the indicated abelian groups.
Source: Stacks 08BW (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def HomCoverAdditive [OpenHomGeometry S] {i : OpenHomInclusions (S := S)}
    {U V : Opens X} (t : OpenHomTriangles i U V) : Prop :=
  ∀ (A : Algebra S) (P Q : Derived A) (n : ℤ),
    (∀ f h : P ⟶ Q⟦n⟧, homCoverRestrict A U V n (f + h) =
      homCoverRestrict A U V n f + homCoverRestrict A U V n h) ∧
    (∀ f h : OpenHom A U P Q n × OpenHom A V P Q n,
      homCoverDifference i A U V n (f + h) =
        homCoverDifference i A U V n f + homCoverDifference i A U V n h) ∧
    (∀ f h : OpenHom A (U ⊓ V) P Q n,
      homCoverBoundary t A n (f + h) = homCoverBoundary t A n f + homCoverBoundary t A n h)

/-- Simultaneous contravariance in P and covariance in Q, on a restricted Hom.
Source: Stacks 08BW (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def homOpenMap [OpenHomGeometry S] (A : Algebra S) (Z : Opens X)
    {P P' Q Q' : Derived A} (a : P' ⟶ P) (b : Q ⟶ Q')
    (n : ℤ) (f : OpenHom A Z P Q n) : OpenHom A Z P' Q' n :=
  (derivedRestriction A Z).map a ≫ f ≫ ((derivedRestriction A Z).map b)⟦n⟧'

/-- Naturality of the boundary for both variables; the other two squares are included
as well. Source: Stacks 08BW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def HomCoverNatural [OpenHomGeometry S] {i : OpenHomInclusions (S := S)}
    {U V : Opens X} (t : OpenHomTriangles i U V) : Prop :=
  ∀ (A : Algebra S) (P P' Q Q' : Derived A) (a : P' ⟶ P) (b : Q ⟶ Q') (n : ℤ),
    (∀ f : P ⟶ Q⟦n⟧,
      homCoverRestrict A U V n (a ≫ f ≫ b⟦n⟧') =
        (homOpenMap A U a b n (homRestrict A U n f),
          homOpenMap A V a b n (homRestrict A V n f))) ∧
    (∀ f : OpenHom A U P Q n × OpenHom A V P Q n,
      homCoverDifference i A U V n
          (homOpenMap A U a b n f.1, homOpenMap A V a b n f.2) =
        homOpenMap A (U ⊓ V) a b n (homCoverDifference i A U V n f)) ∧
    (∀ f : OpenHom A (U ⊓ V) P Q n,
      homCoverBoundary t A n (homOpenMap A (U ⊓ V) a b n f) =
        a ≫ homCoverBoundary t A n f ≫ b⟦n + 1⟧')

/-- Normalized left-module derived scalar extension on the fixed localization, and
its open-support comparison. The counit fixes the adjunction as the action adjunction;
the comparison c is the canonical comparison for restriction followed by lower shriek,
fixed by its compatibility with the open counits. The boundary equation is separate.
Source: Stacks sdga, 0FTF, 0FTR, 0FRX; the DAG's scalar refinement of 08BW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
class HomScalarSystem [g : OpenHomGeometry S] where
  extension {A B : Algebra S} (φ : A ⟶ B) : DerivedExtension φ
  restriction {A B : Algebra S} (φ : A ⟶ B) : Derived B ⥤ Derived A
  restriction_eq {A B : Algebra S} (φ : A ⟶ B) :
    moduleQ B ⋙ restriction φ = restrictScalars φ ⋙ moduleQ A
  adjunction {A B : Algebra S} (φ : A ⟶ B) :
    (extension φ).functor ⊣ restriction φ
  counit {A B : Algebra S} (φ : A ⟶ B) (N : LeftModule B) :
    (adjunction φ).counit.app ((moduleQ B).obj N) =
      (extension φ).functor.map
        (eqToHom (congrArg (fun F ↦ F.obj N) (restriction_eq φ))) ≫
      derivedActionCounit (extension φ) N
  [additive : ∀ {A B : Algebra S} (φ : A ⟶ B), (extension φ).functor.Additive]
  [shift : ∀ {A B : Algebra S} (φ : A ⟶ B), (extension φ).functor.CommShift ℤ]
  exact {A B : Algebra S} (φ : A ⟶ B) : (extension φ).functor.IsTriangulated
  identityModule (A : Algebra S) : restrictScalars (𝟙 A) ≅ 𝟭 (LeftModule A)
  identityModule_eq (A : Algebra S) (N : LeftModule A) :
    ((identityModule A).hom.app N).hom = 𝟙 N.X
  compositionModule {A B C : Algebra S} (φ : A ⟶ B) (ψ : B ⟶ C) :
    restrictScalars ψ ⋙ restrictScalars φ ≅ restrictScalars (φ ≫ ψ)
  compositionModule_eq {A B C : Algebra S} (φ : A ⟶ B) (ψ : B ⟶ C)
      (N : LeftModule C) : ((compositionModule φ ψ).hom.app N).hom = 𝟙 N.X
  identityRestriction (A : Algebra S) : restriction (𝟙 A) ≅ 𝟭 (Derived A)
  identityRestriction_eq (A : Algebra S) (N : LeftModule A) :
    (identityRestriction A).hom.app ((moduleQ A).obj N) =
      eqToHom (congrArg (fun F ↦ F.obj N) (restriction_eq (𝟙 A))) ≫
        (moduleQ A).map ((identityModule A).hom.app N)
  compositionRestriction {A B C : Algebra S} (φ : A ⟶ B) (ψ : B ⟶ C) :
    restriction ψ ⋙ restriction φ ≅ restriction (φ ≫ ψ)
  compositionRestriction_eq {A B C : Algebra S} (φ : A ⟶ B) (ψ : B ⟶ C)
      (N : LeftModule C) :
    (compositionRestriction φ ψ).hom.app ((moduleQ C).obj N) =
      (restriction φ).map
        (eqToHom (congrArg (fun F ↦ F.obj N) (restriction_eq ψ))) ≫
      eqToHom (congrArg (fun F ↦ F.obj ((restrictScalars ψ).obj N))
        (restriction_eq φ)) ≫
      (moduleQ A).map ((compositionModule φ ψ).hom.app N) ≫
      eqToHom (congrArg (fun F ↦ F.obj N) (restriction_eq (φ ≫ ψ)).symm)
  openComparison {A B : Algebra S} (φ : A ⟶ B) (Z : Opens X) :
    coverDerived A Z ⋙ (extension φ).functor ≅ (extension φ).functor ⋙ coverDerived B Z
  openCounit {A B : Algebra S} (φ : A ⟶ B) (Z : Opens X) (P : Derived A) :
    (openComparison φ Z).hom.app P ≫
      (g.adjunction B Z).counit.app ((extension φ).functor.obj P) =
        (extension φ).functor.map ((g.adjunction A Z).counit.app P)

attribute [instance 10] HomScalarSystem.additive HomScalarSystem.shift

/-- Applying derived extension to a global shifted morphism.
Source: Stacks 0FTF (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def scalarHom [OpenHomGeometry S] [s : HomScalarSystem (S := S)]
    {A B : Algebra S} (φ : A ⟶ B) {P Q : Derived A} (n : ℤ) (f : P ⟶ Q⟦n⟧) :
    (s.extension φ).functor.obj P ⟶ ((s.extension φ).functor.obj Q)⟦n⟧ :=
  (s.extension φ).functor.map f ≫ ((s.extension φ).functor.commShiftIso n).hom.app Q

/-- The same scalar map on an open, expressed through its canonical open adjunction.
Transport along openComparison is the comparison with restriction and lower shriek;
thus this applies the derived extension on that open, not an arbitrary Hom map.
Source: Stacks 0FRX, 0FTR (blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def scalarOpenHom [g : OpenHomGeometry S] [s : HomScalarSystem (S := S)]
    {A B : Algebra S} (φ : A ⟶ B) (Z : Opens X) {P Q : Derived A}
    (n : ℤ) (f : OpenHom A Z P Q n) :
    OpenHom B Z ((s.extension φ).functor.obj P) ((s.extension φ).functor.obj Q) n :=
  (g.adjunction B Z).homEquiv _ _
      ((s.openComparison φ Z).inv.app P ≫
        (s.extension φ).functor.map (homAdjunct A Z n f) ≫
        ((s.extension φ).functor.commShiftIso n).hom.app Q) ≫
    ((derivedRestriction B Z).commShiftIso n).hom.app ((s.extension φ).functor.obj Q)

/-- Scalar compatibility of the full exact sequence, and additivity of its component
maps. In particular the last square is the connecting square in every integer degree.
Source: Stacks 0FRX, 0FTF, and the DAG refinement of 08BW
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def HomCoverScalar [OpenHomGeometry S] [s : HomScalarSystem (S := S)]
    {i : OpenHomInclusions (S := S)} {U V : Opens X} (t : OpenHomTriangles i U V) : Prop :=
  ∀ (A B : Algebra S) (φ : A ⟶ B) (P Q : Derived A) (n : ℤ),
    (∀ (Z : Opens X) (f h : OpenHom A Z P Q n),
      scalarOpenHom φ Z n (f + h) = scalarOpenHom φ Z n f + scalarOpenHom φ Z n h) ∧
    (∀ f : P ⟶ Q⟦n⟧,
      homCoverRestrict B U V n (scalarHom φ n f) =
        (scalarOpenHom φ U n (homRestrict A U n f),
          scalarOpenHom φ V n (homRestrict A V n f))) ∧
    (∀ f : OpenHom A U P Q n × OpenHom A V P Q n,
      scalarOpenHom φ (U ⊓ V) n (homCoverDifference i A U V n f) =
        homCoverDifference i B U V n
          (scalarOpenHom φ U n f.1, scalarOpenHom φ V n f.2)) ∧
    (∀ f : OpenHom A (U ⊓ V) P Q n,
      scalarHom φ (n + 1) (homCoverBoundary t A n f) =
        homCoverBoundary t B n (scalarOpenHom φ (U ⊓ V) n f)) ∧
    (∀ P' : Derived A,
      (s.extension φ).functor.map ((t.boundary A).app P') ≫
          ((s.extension φ).functor.commShiftIso 1).hom.app
            ((coverDerived A (U ⊓ V)).obj P') ≫
          ((s.openComparison φ (U ⊓ V)).hom.app P')⟦(1 : ℤ)⟧' =
        (t.boundary B).app ((s.extension φ).functor.obj P'))

/-- The identity comparison is the canonical uniqueness isomorphism for the action
adjunction and identity restriction. Source: adjunction uniqueness, Stacks 0FTR
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def scalarIdentityIso [OpenHomGeometry S] [s : HomScalarSystem (S := S)] (A : Algebra S) :
    (s.extension (𝟙 A)).functor ≅ 𝟭 (Derived A) :=
  Adjunction.leftAdjointIdIso (s.adjunction (𝟙 A)) (s.identityRestriction A)

/-- The composition comparison is the adjunction-composition mate of the literal
restriction comparison. Source: Stacks 0FTR, adjunction uniqueness
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def scalarCompositionIso [OpenHomGeometry S] [s : HomScalarSystem (S := S)]
    {A B C : Algebra S} (φ : A ⟶ B) (ψ : B ⟶ C) :
    (s.extension φ).functor ⋙ (s.extension ψ).functor ≅ (s.extension (φ ≫ ψ)).functor :=
  Adjunction.leftAdjointCompIso (s.adjunction φ) (s.adjunction ψ)
    (s.adjunction (φ ≫ ψ)) (s.compositionRestriction φ ψ)

/-- Identity and composition on every Hom term, transported by the canonical adjunction
comparisons. Since these hold for all objects, opens and integer degrees, and
HomCoverScalar includes every arrow square, they respect the entire exact sequence.
Source: Stacks 0FTR and adjunction-composition associativity
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
def HomScalarCoherent [OpenHomGeometry S] [s : HomScalarSystem (S := S)] : Prop :=
  (∀ (A : Algebra S) (P Q : Derived A) (n : ℤ) (f : P ⟶ Q⟦n⟧),
    scalarHom (𝟙 A) n f =
      (scalarIdentityIso A).hom.app P ≫ f ≫ ((scalarIdentityIso A).inv.app Q)⟦n⟧') ∧
  (∀ (A : Algebra S) (Z : Opens X) (P Q : Derived A) (n : ℤ)
      (f : OpenHom A Z P Q n),
    scalarOpenHom (𝟙 A) Z n f =
      homOpenMap A Z ((scalarIdentityIso A).hom.app P)
        ((scalarIdentityIso A).inv.app Q) n f) ∧
  (∀ (A B C : Algebra S) (φ : A ⟶ B) (ψ : B ⟶ C)
      (P Q : Derived A) (n : ℤ) (f : P ⟶ Q⟦n⟧),
    scalarHom ψ n (scalarHom φ n f) =
      (scalarCompositionIso φ ψ).hom.app P ≫ scalarHom (φ ≫ ψ) n f ≫
        ((scalarCompositionIso φ ψ).inv.app Q)⟦n⟧') ∧
  (∀ (A B C : Algebra S) (φ : A ⟶ B) (ψ : B ⟶ C) (Z : Opens X)
      (P Q : Derived A) (n : ℤ) (f : OpenHom A Z P Q n),
    scalarOpenHom ψ Z n (scalarOpenHom φ Z n f) =
      homOpenMap C Z ((scalarCompositionIso φ ψ).hom.app P)
        ((scalarCompositionIso φ ψ).inv.app Q) n (scalarOpenHom (φ ≫ ψ) Z n f))

/-- The data and properties asserted simultaneously by the existence theorem.
This structure packages the actual sequence and its canonical comparisons.
Source: Stacks 08BW and the scalar refinement in the node proof
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris). -/
structure OpenHomMayerVietoris
    (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w}) (U V : Opens X) where
  [geometry : OpenHomGeometry S]
  inclusions : OpenHomInclusions (S := S)
  triangles : OpenHomTriangles inclusions U V
  [scalars : HomScalarSystem (S := S)]
  exact : HomCoverExact triangles
  additive : HomCoverAdditive triangles
  natural : HomCoverNatural triangles
  scalar : HomCoverScalar triangles
  coherent : HomScalarCoherent (S := S)

/-- The sheaf dg Mayer–Vietoris long exact sequence with all its naturality data,
including boundary signs and derived scalar extension, with no boundedness or
geometric finiteness assumptions and with empty opens allowed.

Source: Stacks cohomology.tex, 08BU, 08BW; sdga.tex, 0FRW, 0FRX, 0FTB, 0FTF, 0FTR.
Scalar boundary and composition compatibility are the refinement of the node proof
(blueprint: lem-sfb-sheaf-dg-open-hom-mayer-vietoris).

Proof plan:
1. Apply lem-sc-open-cover-mate-module-short-exact in each degree. The stalk maps
are (1,-1), then addition on the intersection, and the identity elsewhere. The
lem-sfb-sheaf-dg-open-extension-calculus counits and inclusions are these maps.
2. Apply lem-pc-cone-short-exact-quasi-iso to q=(b,0). Localize and use the negative
cone projection to obtain delta=-p q⁻¹. Naturality of cone maps descends by
lem-weil-pbc-localization-universal-property to every derived morphism.
3. Apply lem-weil-pbc-hom-out-of-triangle-exact, rotate and shift, and use the open
adjunctions. This gives all three exactness positions, the difference sign, and
the formula for the Hom boundary. Pre- and postcomposition give naturality.
4. By lem-sfb-sheaf-dg-hflat-computation resolve P by a graded-flat h-flat module.
The two projection formulas in lem-sfb-sheaf-dg-open-tensor-projection show that
restriction and lower shriek preserve these properties. Finite sums and the signed
cone preserve them too, so ordinary extension computes L on the whole cover cone.
5. The tensor projection comparison preserves a,b,q,p. The cone comparison has sign
(-1)^degree on the shifted summand. The coherent-shift comparison of
lem-pur-right-kan-extension-coherent-shift then identifies L(delta) with delta(LP).
6. Apply L to the shifted adjunct formula for the boundary. Shift naturality and
counit compatibility identify the result with the adjunct of the scalar image.
This proves the boundary square, together with the two restriction squares.
7. Restrictions compose literally. The action-normalized adjunctions of
lem-sfb-ringed-dg-scalar-adjunction and lem-weil-pbc-conjugate-iso-unit-equation give
the canonical identity and composition comparisons. The node
lem-sc-left-adjoint-composition-iso-associativity gives their associativity. Their
shift compatibility follows from the universal derived comparison. Empty opens
have zero extension and Hom groups, so the same construction applies to them. -/
theorem sheaf_dg_open_hom_mayer_vietoris
    (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w})
    (U V : Opens X) (hcover : U ⊔ V = ⊤) :
    Nonempty (OpenHomMayerVietoris S U V) := by
  sorry

end CategoryTheory.SheafDg
