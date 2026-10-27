/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.Paper.IntegralQuotientCoefficients
public import Sheaf.Paper.InternalDerivedScalarComparisons
public import Sheaf.Paper.IntegralQuotientProjectionMap
public import Sheaf.Paper.SectionModuleOperationsData
public import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent

/-! # One K-flat representative for the six integral quotient pullback faces

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 06YS, 0G7E, 06YY, 0D6D and 03EL
(blueprint: lem-sfb-integral-quotient-pullback-face-model).

All module objects below have the fixed section-module reconstruction. Flatness and
K-flatness are tested in that section-module category, using its existing predicates.
The ordinary scalar maps are the published balanced `CondensedRing.pullIso` maps;
the derived maps are their published adjunction mates. The word comparisons compose
only the universal computation counits, and never choose another resolution.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient.PullbackFace

/-- Bookkeeping for an actual route and its computation counit, including the
conditions at its intermediate vertices. Source: blueprint integral proof (3)
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
structure Route (A B : Type v) [Category.{w} A] [Category.{w} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] where
  ordinary : CochainComplex A ℤ ⥤ CochainComplex B ℤ
  derived : DerivedCategory A ⥤ DerivedCategory B
  comparison : ∀ P : CochainComplex A ℤ,
    derived.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (ordinary.obj P)
  vertices : CochainComplex A ℤ → Prop

/-- Concatenation uses the computation maps in the order of the word.
The vertex condition retains every prefix and its comparison map.
Source: Stacks 06YY (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def Route.comp {A B C : Type v} [Category.{w} A] [Category.{w} B] [Category.{w} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    (a : Route A B) (b : Route B C) : Route A C where
  ordinary := a.ordinary ⋙ b.ordinary
  derived := a.derived ⋙ b.derived
  comparison P := b.derived.map (a.comparison P) ≫ b.comparison (a.ordinary.obj P)
  vertices P := a.vertices P ∧ b.vertices (a.ordinary.obj P) ∧
    IsIso (b.derived.map (a.comparison P) ≫ b.comparison (a.ordinary.obj P))

/-- Equality with localization of the specified ordinary face under the two route
counits. Source: Stacks 06YY, 0D6D
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def Route.Face {A B : Type v} [Category.{w} A] [Category.{w} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (a b : Route A B) (ordinary : a.ordinary ⟶ b.ordinary)
    (derived : a.derived ⟶ b.derived) (P : CochainComplex A ℤ) : Prop :=
  derived.app (DerivedCategory.Q.obj P) ≫ b.comparison P =
    a.comparison P ≫ DerivedCategory.Q.map (ordinary.app P)

/-- Naturality of the canonical representative identification at a chain map.
Source: Stacks 06YY (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def Route.NaturalAt {A B : Type v} [Category.{w} A] [Category.{w} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (a : Route A B) {P P' : CochainComplex A ℤ} (b : P ⟶ P') : Prop :=
  a.derived.map (DerivedCategory.Q.map b) ≫ a.comparison P' =
    a.comparison P ≫ DerivedCategory.Q.map (a.ordinary.map b)

/-- The recorded K-flat and flat-term predicates, in section coordinates.
Source: Stacks 06YS (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def FlatRepresentative (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (P : CochainComplex (QuotientChange.Modules Λ T) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
  ∀ i : ℤ, SheafOfModules.IsFlatOnSite
    (J := Scheme.ProEt.topology T) (R := ModuleRingedComparison.ring Λ T)
    ((ModuleRingedComparison.equivalence Λ T).functor.obj (P.X i))

/-- A geometric edge with its actual universal left-derived computation map.
Source: Stacks 06YY (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def pull (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U V : Scheme.{u}} (f : U ⟶ V) :
    Route (QuotientChange.Modules Λ V) (QuotientChange.Modules Λ U) where
  ordinary := (CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)
  derived := QuotientChange.L Λ f
  comparison := computePull f
  vertices P := FlatRepresentative Λ U
      (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) ∧
    IsIso (computePull f P)

/-- The actual positive quotient edge. The index n means exponent n+1.
Source: blueprint integral proof (3); Stacks 06YY
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def scalar (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u}) :
    Route (QuotientChange.Modules (integral l E) T)
      (QuotientChange.Modules (finite l E n) T) where
  ordinary := (QuotientChange.extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)
  derived := QuotientChange.D (reduction l E n) T
  comparison := QuotientChange.compute (reduction l E n) T
  vertices P := FlatRepresentative (finite l E n) T
      (((QuotientChange.extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P) ∧
    IsIso (QuotientChange.compute (reduction l E n) T P)

/-- Lift an ordinary functor square to the nested termwise complex functors.
Source: Stacks 03EL (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def complexSquare {A B C D : Type v}
    [Category.{w} A] [Category.{w} B] [Category.{w} C] [Category.{w} D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive] (e : F ⋙ G ≅ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso e (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I)) (.up ℤ)).symm

/-- The ordinary balanced scalar face, in the direction x tensor s maps to
pullback(x) tensor pullback(s). The published pullIso is the uniquely normalized
conjugate of scalar restriction and geometric inverse image; its inverse is chi.
Source: Stacks 03EL (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def ordinaryScalarFace (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (scalar l E n V).ordinary ⋙ (pull (finite l E n) f).ordinary ≅
      (pull (integral l E) f).ordinary ⋙ (scalar l E n U).ordinary :=
  complexSquare (CondensedRing.pullIso (reduction l E n) f).symm

/-- The specified scalar-adjunction mate, before asserting its invertibility.
It is formed from exact scalar restriction and exact geometric inverse image;
no exactness of extension along the quotient is required.
Source: Stacks 07A6 (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def scalarMate (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (pull (integral l E) f).derived ⋙ (scalar l E n U).derived ⟶
      (scalar l E n V).derived ⋙ (pull (finite l E n) f).derived := by
  let rV := QuotientChange.V (reduction l E n) V
  let rU := QuotientChange.V (reduction l E n) U
  let cR := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (integral l E) f
  let cS := CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (finite l E n) f
  let a := Functor.isoWhiskerLeft rV cR ≪≫
    (CondensedRing.derivedComapUpperStarIso (reduction l E n) f).symm ≪≫
    Functor.isoWhiskerRight cS.symm rU
  dsimp only [pull, scalar]
  unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
  exact SheafOfModules.ScalarPullback.mate
    (QuotientChange.scalarAdj (reduction l E n) V)
    (QuotientChange.scalarAdj (reduction l E n) U) a.hom

/-- The actual geometric compositor around the square, before localization.
Source: Stacks 0D6D (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def ordinarySquare (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    (pull Λ g).ordinary ⋙ (pull Λ f').ordinary ≅
      (pull Λ f).ordinary ⋙ (pull Λ h).ordinary :=
  complexSquare ((CondensedRing.upperStarComp Λ f' g).symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ Y ↦ CondensedRing.upperStar Λ k)
      sq.toCommSq.w.symm) ≪≫ CondensedRing.upperStarComp Λ h f)

/-- The derived geometric face uses precisely the published composition comparisons.
Source: Stacks 0D6D (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def derivedSquare (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    (pull Λ g).derived ⋙ (pull Λ f').derived ≅
      (pull Λ f).derived ⋙ (pull Λ h).derived := by
  unfold pull QuotientChange.L CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.condensedAmbientPullbackComparison Λ sq

/-- Whiskering a face on the left, with its necessary functor associators.
Source: Stacks 0D6D (blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def leftFace {A B C D E' : Type v}
    [Category.{w} A] [Category.{w} B] [Category.{w} C] [Category.{w} D] [Category.{w} E']
    (F : A ⥤ B) {G : B ⥤ C} {H : C ⥤ E'} {I : B ⥤ D} {J : D ⥤ E'}
    (e : G ⋙ H ≅ I ⋙ J) : (F ⋙ G) ⋙ H ≅ (F ⋙ I) ⋙ J :=
  Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F e ≪≫
    (Functor.associator F I J).symm

/-- Identity and composition coherence of the actual coefficient identifications.
Source: blueprint integral proof (3); Stacks 0D6D
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def CoefficientCoherence (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] : Prop :=
  (∀ T : Scheme.{u}, condensedPullbackHom Λ (𝟙 T) =
    (upperStarId Ab.{u + 1} T).hom.app (condensedRingObj Λ T)) ∧
  ∀ {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W),
    condensedPullbackHom Λ (f ≫ g) =
      (upperStarComp Ab.{u + 1} f g).hom.app (condensedRingObj Λ W) ≫
        (upperStar Ab.{u + 1} f).map (condensedPullbackHom Λ g) ≫ condensedPullbackHom Λ f


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The route scalar at Y, then g and f', with its intermediate computation maps.
Source: blueprint integral proof (3)
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def start {X' Y' Y : Scheme.{u}} (f' : X' ⟶ Y') (g : Y' ⟶ Y) :
    Route (QuotientChange.Modules (integral l E) Y)
      (QuotientChange.Modules (finite l E n) X') :=
  ((scalar l E n Y).comp (pull (finite l E n) g)).comp (pull (finite l E n) f')

/-- The route g, scalar at Y', then f', with its intermediate computation maps.
Source: blueprint integral proof (3)
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def afterG {X' Y' Y : Scheme.{u}} (f' : X' ⟶ Y') (g : Y' ⟶ Y) :
    Route (QuotientChange.Modules (integral l E) Y)
      (QuotientChange.Modules (finite l E n) X') :=
  ((pull (integral l E) g).comp (scalar l E n Y')).comp (pull (finite l E n) f')

/-- The route g and f', then scalar at X', with its intermediate computation maps.
Source: blueprint integral proof (3)
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def beforeSquare {X' Y' Y : Scheme.{u}} (f' : X' ⟶ Y') (g : Y' ⟶ Y) :
    Route (QuotientChange.Modules (integral l E) Y)
      (QuotientChange.Modules (finite l E n) X') :=
  ((pull (integral l E) g).comp (pull (integral l E) f')).comp (scalar l E n X')

/-- The route f and h, then scalar at X', with its intermediate computation maps.
Source: blueprint integral proof (3)
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def finish {X' X Y : Scheme.{u}} (h : X' ⟶ X) (f : X ⟶ Y) :
    Route (QuotientChange.Modules (integral l E) Y)
      (QuotientChange.Modules (finite l E n) X') :=
  ((pull (integral l E) f).comp (pull (integral l E) h)).comp (scalar l E n X')

/-- The route scalar at Y, then f and h, with its intermediate computation maps.
Source: blueprint integral proof (3)
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def afterSquare {X' X Y : Scheme.{u}} (h : X' ⟶ X) (f : X ⟶ Y) :
    Route (QuotientChange.Modules (integral l E) Y)
      (QuotientChange.Modules (finite l E n) X') :=
  ((scalar l E n Y).comp (pull (finite l E n) f)).comp (pull (finite l E n) h)

/-- The route f, scalar at X, then h, with its intermediate computation maps.
Source: blueprint integral proof (3)
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def afterF {X' X Y : Scheme.{u}} (h : X' ⟶ X) (f : X ⟶ Y) :
    Route (QuotientChange.Modules (integral l E) Y)
      (QuotientChange.Modules (finite l E n) X') :=
  ((pull (integral l E) f).comp (scalar l E n X)).comp (pull (finite l E n) h)

variable {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

variable (χ : ∀ {U V : Scheme.{u}} (a : U ⟶ V),
  (scalar l E n V).derived ⋙ (pull (finite l E n) a).derived ≅
    (pull (integral l E) a).derived ⋙ (scalar l E n U).derived)

/-- All six equations use the same P and the same vertex identifications. The first
three follow g,f'; the last three follow f,h. The square faces use only geometric
compositors and the scalar faces are the fixed balanced maps, with no fresh choices.
Source: blueprint integral proof (3); Stacks 03EL and 0D6D
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def SixFaces (sq : ChosenCartesianSquare h f' f g)
    (P : CochainComplex (QuotientChange.Modules (integral l E) Y) ℤ) : Prop :=
  Route.Face (start l E n f' g) (afterG l E n f' g)
    (Functor.isoWhiskerRight (ordinaryScalarFace l E n g)
        (pull (finite l E n) f').ordinary).hom
    (Functor.isoWhiskerRight (χ g)
        (pull (finite l E n) f').derived).hom P ∧
  Route.Face (afterG l E n f' g) (beforeSquare l E n f' g)
    (leftFace (pull (integral l E) g).ordinary (ordinaryScalarFace l E n f')).hom
    (leftFace (pull (integral l E) g).derived (χ f')).hom P ∧
  Route.Face (beforeSquare l E n f' g) (finish l E n h f)
    (Functor.isoWhiskerRight (ordinarySquare (integral l E) sq)
        (scalar l E n X').ordinary).hom
    (Functor.isoWhiskerRight (derivedSquare (integral l E) sq)
        (scalar l E n X').derived).hom P ∧
  Route.Face (start l E n f' g) (afterSquare l E n h f)
    (leftFace (scalar l E n Y).ordinary (ordinarySquare (finite l E n) sq)).hom
    (leftFace (scalar l E n Y).derived (derivedSquare (finite l E n) sq)).hom P ∧
  Route.Face (afterSquare l E n h f) (afterF l E n h f)
    (Functor.isoWhiskerRight (ordinaryScalarFace l E n f)
        (pull (finite l E n) h).ordinary).hom
    (Functor.isoWhiskerRight (χ f)
        (pull (finite l E n) h).derived).hom P ∧
  Route.Face (afterF l E n h f) (finish l E n h f)
    (leftFace (pull (integral l E) f).ordinary (ordinaryScalarFace l E n h)).hom
    (leftFace (pull (integral l E) f).derived (χ h)).hom P

/-- The complete common model, including all prefixes, invertibility of their
computation maps, all six localized faces and chain-map naturality.
Source: Stacks 06YY, 0G7E and 0D6D
(blueprint: lem-sfb-integral-quotient-pullback-face-model). -/
def CommonModel (sq : ChosenCartesianSquare h f' f g)
    (P : CochainComplex (QuotientChange.Modules (integral l E) Y) ℤ) : Prop :=
  (start l E n f' g).vertices P ∧
  (afterG l E n f' g).vertices P ∧
  (beforeSquare l E n f' g).vertices P ∧
  (finish l E n h f).vertices P ∧
  (afterSquare l E n h f).vertices P ∧
  (afterF l E n h f).vertices P ∧
  SixFaces l E n χ sq P ∧
  ∀ (P' : CochainComplex (QuotientChange.Modules (integral l E) Y) ℤ),
    FlatRepresentative (integral l E) Y P' → ∀ b : P ⟶ P',
    (start l E n f' g).NaturalAt b ∧
    (afterG l E n f' g).NaturalAt b ∧
    (beforeSquare l E n f' g).NaturalAt b ∧
    (finish l E n h f).NaturalAt b ∧
    (afterSquare l E n h f).NaturalAt b ∧
    (afterF l E n h f).NaturalAt b

/-- Actual finite projections commute with the point-pullback coefficient maps;
these maps satisfy their identity and composition laws. Every unbounded integral
object has a flat-term K-flat representative, and every such representative supplies
one simultaneous model for the six specified derived faces. Here quotient level n
means exponent n+1; section reconstruction is the fixed dependency equivalence.

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 06YS, 0G7E, 06YY, 0D6D and 03EL
(blueprint: lem-sfb-integral-quotient-pullback-face-model).

Proof:
1. Apply naturality of upperStarFromPointComp to the actual condensed reduction map.
Its component gives the coefficient square at every finite exponent. The integral
limit identification is normalized by these actual projections; no preservation of
an infinite limit by inverse image is asserted.
2. Transpose eta-id and eta-comp through the inverse-image adjunction. Mate pasting
and injectivity of its Hom equivalence give CoefficientCoherence for both rings.
3. Resolve a complex representing M by the flat-term K-flat resolution theorem and
transport through section reconstruction. Ringed pullback preserves this class,
including scalar extension along the nonflat quotient. Apply this successively to
every prefix in the six routes, obtaining their intermediate vertex conditions.
4. The ringed pullback and change-of-rings universal computation counits are
invertible on this class. Compose and whisker those counits, exactly as Route.comp,
to obtain all representative identifications, natural at every chain map.
5. Scalar comparison normalization identifies the inverse scalar-adjunction mate
with localization of the ordinary balanced comparison. Balancing is valid because
of the coefficient square from step 1. Tensor generator extensionality makes this
comparison unique, including after module sheafification.
6. Pullback-composition normalization identifies the two geometric square faces
with localization of the ordinary compositors. Their coefficient identifications
agree by step 2 and the commutativity of the chosen Cartesian square.
7. Whisker these four scalar faces and two square faces by the indicated remaining
edge. Normalized K-flat word-comparison descent gives exactly SixFaces, in its
written order, with the same P and the computation maps of step 4 at shared vertices.
8. Naturality of each edge counit gives NaturalAt for the composite words. Ordinary
faces are natural transformations, so their localizations commute with all chain
maps. No boundedness, flatness of the quotient, properness or completeness is used. -/
theorem integral_quotient_pullback_face_model (sq : ChosenCartesianSquare h f' f g) :
    CoefficientCoherence (integral l E) ∧
    (∀ m : ℕ, CoefficientCoherence (finite l E m)) ∧
    (∀ (m : ℕ) {U V : Scheme.{u}} (a : U ⟶ V),
      (upperStar Ab.{u + 1} a).map (coefficientMap (reduction l E m) V) ≫
          condensedPullbackHom (finite l E m) a =
        condensedPullbackHom (integral l E) a ≫ coefficientMap (reduction l E m) U) ∧
    (∀ M : DerivedCategory (QuotientChange.Modules (integral l E) Y),
      ∃ P : CochainComplex (QuotientChange.Modules (integral l E) Y) ℤ,
        FlatRepresentative (integral l E) Y P ∧ Nonempty (DerivedCategory.Q.obj P ≅ M)) ∧
    ∃ χ : ∀ {U V : Scheme.{u}} (a : U ⟶ V),
        (scalar l E n V).derived ⋙ (pull (finite l E n) a).derived ≅
          (pull (integral l E) a).derived ⋙ (scalar l E n U).derived,
      (∀ {U V : Scheme.{u}} (a : U ⟶ V), (χ a).inv = scalarMate l E n a) ∧
      ∀ P : CochainComplex (QuotientChange.Modules (integral l E) Y) ℤ,
        FlatRepresentative (integral l E) Y P → CommonModel l E n χ sq P := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralQuotient.PullbackFace
