/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.CategoryTheory.Abelian.DerivedBottomComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Condensed coefficient restriction calculus on a smooth curve

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-heart/
thm-a1-curve-perverse-heart.proof.md, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus).

All cohomology and truncations belong to the ordinary derived category of actual
modules over the pulled-back finite-subextension-valued condensed coefficient ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open Opposite AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.CondensedCurve

/-- The existing pulled-back finite-subextension-valued coefficient ring.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev coefficients (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u}) :=
  condensedRingObj (Profinite.padicAlgClRingObj ell) T

-- Module sheaves over the pulled-back Omega coefficients: the actual internal-module
-- category, written out by a local notation. No declaration is added, so the generic
-- category of `sk-lem-wft-curve-heart` (a consumer of this node) is not imported.
local notation "ModΩ[" ell ", " T "]" =>
  Mod (Sheaf (Scheme.ProEt.topology T) Ab) (coefficients ell T)

/-- The ordinary ambient derived category of these module sheaves.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev Ambient (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u}) :=
  DerivedCategory (ModΩ[ell, T])

/-- The existing bounded constructibility predicate in the ambient derived category.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev boundedConstructible (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u}) :=
  constantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) T

/-- The full category of bounded complexes with constructible ordinary cohomology.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev Bounded (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u}) :=
  ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ell) T

/-- The total derived functor of the full module pullback composite.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev derivedPull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  CondensedRing.moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ell) f

/-- The total derived functor of the full module pushforward composite.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev derivedPush (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell) f

/-- Ordinary module-sheaf cohomology, with no completion or coefficient localization.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev ordinaryCohomology (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u}) (m : ℤ) :=
  DerivedCategory.homologyFunctor (ModΩ[ell, T]) m

/-- The specified bottom comparison, composed with the actual lower-truncation unit.
It is defined on all ambient objects; it is invertible when the object is in degrees ≥ m.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
def bottomMap (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : ℤ) (K : Ambient ell X) :
    (ordinaryCohomology ell Y m).obj ((derivedPush ell f).obj K) ⟶
      (push ell f).obj ((ordinaryCohomology ell X m).obj K) :=
  (ordinaryCohomology ell Y m).map ((derivedPush ell f).map
    ((DerivedCategory.TStructure.t.truncGEπ m).app K)) ≫
      ((push ell f).rightDerivedFunctorTruncatedBottomIso m).hom.app K

/-- The canonical cohomology comparison for the exact pullback, transported to its
total left derived functor by the published exact-functor comparison.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
def pullCohomology (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : ℤ) :
    ordinaryCohomology ell Y m ⋙ pull ell f ≅ derivedPull ell f ⋙ ordinaryCohomology ell X m :=
  (pull ell f).mapDerivedCategoryHomologyFunctorIso m ≪≫
    Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj ell) f).symm (ordinaryCohomology ell X m)

/-- Closure in all module sheaves, including extensions of arbitrary short exact sequences.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
def HeartClosure (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u}) : Prop :=
  (∀ (M N : ModΩ[ell, T]) (f : M ⟶ N),
    constructible ell T M → constructible ell T N →
      constructible ell T (kernel f) ∧ constructible ell T (cokernel f)) ∧
  (∀ S : ShortComplex (ModΩ[ell, T]), S.ShortExact →
    constructible ell T S.X₁ → constructible ell T S.X₃ → constructible ell T S.X₂)

/-- The induced standard bounded t-structure and its actual ambient truncations.
The inherited triangulated structure is supplied as conclusion data, not as a hypothesis.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
structure Standard (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u}) where
  [triangulated : (boundedConstructible ell T).IsTriangulated]
  t : TStructure (Bounded ell T)
  le (K : Bounded ell T) (m : ℤ) :
    t.IsLE K m ↔ DerivedCategory.TStructure.t.IsLE K.obj m
  ge (K : Bounded ell T) (m : ℤ) :
    t.IsGE K m ↔ DerivedCategory.TStructure.t.IsGE K.obj m
  bounded (K : Bounded ell T) : t.bounded K
  heart : t.Heart (ConstantModelConstructible (Profinite.padicAlgClRingObj ell) T)
  heart_normalization : Nonempty (heart.ι ⋙ (boundedConstructible ell T).ι ≅
    ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj ell) T) ⋙
      DerivedCategory.singleFunctor (ModΩ[ell, T]) 0)
  truncLE (m : ℤ) : ∃ α : t.truncLE m ⋙ (boundedConstructible ell T).ι ≅
      (boundedConstructible ell T).ι ⋙ DerivedCategory.TStructure.t.truncLE m,
    ∀ K : Bounded ell T,
      α.hom.app K ≫ (DerivedCategory.TStructure.t.truncLEι m).app K.obj =
        (boundedConstructible ell T).ι.map ((t.truncLEι m).app K)
  truncGE (m : ℤ) : ∃ α : t.truncGE m ⋙ (boundedConstructible ell T).ι ≅
      (boundedConstructible ell T).ι ⋙ DerivedCategory.TStructure.t.truncGE m,
    ∀ K : Bounded ell T,
      (boundedConstructible ell T).ι.map ((t.truncGEπ m).app K) ≫ α.hom.app K =
        (DerivedCategory.TStructure.t.truncGEπ m).app K.obj

/-- The open--closed module calculus and preservation of the specified full categories.
Source: curve-heart proof, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
def ImmersionCalculus (ell : ℕ) [Fact ell.Prime] {C U Z : Scheme.{u}}
    (j : U ⟶ C) (i : Z ⟶ C) [IsClosedImmersion i] : Prop :=
  PreservesFiniteLimits (pull ell j) ∧ PreservesFiniteColimits (pull ell j) ∧
  PreservesFiniteLimits (pull ell i) ∧ PreservesFiniteColimits (pull ell i) ∧
  (∀ M : ModΩ[ell, C],
    IsZero ((pull ell j).obj M) → IsZero ((pull ell i).obj M) → IsZero M) ∧
  PreservesFiniteLimits (push ell i) ∧ PreservesFiniteColimits (push ell i) ∧
  (push ell i).Full ∧ (push ell i).Faithful ∧
  (∀ N : ModΩ[ell, Z],
    IsIso ((CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj ell) i).counit.app N)) ∧
  (∀ M : ModΩ[ell, C],
    (push ell i).essImage M ↔ IsZero ((pull ell j).obj M)) ∧
  (∀ N : ModΩ[ell, U],
    IsIso ((CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj ell) j).counit.app N)) ∧
  (∀ N : ModΩ[ell, U], lisse ell N
    → constructible ell C ((push ell j).obj N)) ∧
  (∀ M : ModΩ[ell, C], constructible ell C M →
    constructible ell U ((pull ell j).obj M) ∧
    constructible ell Z ((pull ell i).obj M)) ∧
  (∀ N : ModΩ[ell, Z], constructible ell Z N
    → constructible ell C ((push ell i).obj N)) ∧
  (∀ K : Bounded ell C,
    boundedConstructible ell U ((derivedPull ell j).obj K.obj) ∧
    boundedConstructible ell Z ((derivedPull ell i).obj K.obj)) ∧
  (∀ K : Bounded ell Z,
    boundedConstructible ell C ((derivedPush ell i).obj K.obj)) ∧
  (∀ K : Bounded ell U, boundedConstructible ell C ((derivedPush ell j).obj K.obj))

/-- Coefficient-heart, common lisse open, standard t-structure, exact immersion calculus,
and the canonical bottom-cohomology and unit comparisons.

Source: latest curve-heart proof, Steps 0(ii), 1, 3 and 4
(blueprint: lem-per-condensed-curve-restriction-calculus).

Proof: C, U and Z are Noetherian; j is quasi-compact. Apply coefficient-heart closure
with Omega. A common adapted stratification gives lissity near every generic point:
use the generic-neighborhood lemma and descent along its surjective closed immersion.
The union is dense with finite closed complement. Reduced Z is finite discrete, so its
constructible modules are lisse. Good truncations retain surviving cohomology and replace
the other cohomology by zero. Heart closure gives closure under cones, hence the inherited
triangulation, restricted bounded standard t-structure, and its constructible heart.
Open/closed recollement gives exact restrictions and closed direct image, full faithfulness,
the counits, joint detection, and the supported essential image. Constructible pullback and
closed images give bounded preservation for these exact functors.
For Rj_* use the integral generators: integral open finiteness and localization comparison,
then finite-field-to-Omega comparison, give bounded constructibility on generators. Exact
scalar extension, cones and shifts give it for every bounded constructible object. Left
exactness and a bounded-below injective resolution give the lower vanishing and the specified
bottom comparison. Degree zero then gives constructibility of j_* on lisse modules.
Represent the derived adjunction unit by the termwise ordinary unit followed by the
right-derived comparison. The bottom normalization on cycles and their boundary quotients,
together with exact pullback, gives precisely the displayed ordinary unit. Only j^*K
needs the lower bound. These arguments include empty schemes, zero ranks and empty families. -/
theorem condensed_curve_restriction_calculus
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [PerfectField k]
    (hEll : IsUnit (ell : k))
    (C : Scheme.{u}) (s : C ⟶ Spec (.of k))
    [Smooth s] [QuasiCompact s] [IsSeparated s] (hPure : C.IsPureDimension 1)
    {U Z : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (i : Z ⟶ C) [IsClosedImmersion i] [IsReduced Z]
    (hDense : Dense (Set.range j)) (hComplement : Set.range j = (Set.range i)ᶜ) :
    (∀ T : Scheme.{u}, T = C ∨ T = U ∨ T = Z →
      HeartClosure ell T ∧ Nonempty (Standard ell T)) ∧
    (∀ (n : ℕ) (F : Fin n → ModΩ[ell, C]),
      (∀ a : Fin n, constructible ell C (F a)) →
      ∃ W : C.Opens, Dense (W : Set C) ∧ Set.Finite ((W : Set C)ᶜ) ∧
        (∀ x : C, x ∉ W → IsClosed ({x} : Set C)) ∧
        ∀ a : Fin n, lisse ell ((pull ell W.ι).obj (F a))) ∧
    (∀ F : ModΩ[ell, Z], constructible ell Z F → lisse ell F) ∧
    ImmersionCalculus ell j i ∧
    (∀ (m : ℤ) (M : Bounded ell U),
      (∀ a : ℤ, a < m → IsZero ((ordinaryCohomology ell U a).obj M.obj)) →
      (∀ a : ℤ, a < m →
        IsZero ((ordinaryCohomology ell C a).obj ((derivedPush ell j).obj M.obj))) ∧
      IsIso (bottomMap ell j m M.obj)) ∧
    (∀ (m : ℤ) (K : Bounded ell C),
      DerivedCategory.TStructure.t.IsGE ((derivedPull ell j).obj K.obj) m →
      (ordinaryCohomology ell C m).map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction
            (Profinite.padicAlgClRingObj ell) j).unit.app K.obj) ≫
        bottomMap ell j m ((derivedPull ell j).obj K.obj) ≫
        (push ell j).map ((pullCohomology ell j m).inv.app K.obj) =
      (CondensedRing.upperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj ell) j).unit.app
          ((ordinaryCohomology ell C m).obj K.obj)) := by
  sorry




/-- A finite coefficient field in Omega and an equivalent coefficient-sized presentation.
The presentation changes only universes. The scheme hypotheses are exactly Weil II (0.1).
Source: curve-heart proof Step 0(i), Weil II (1.1.1)
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
structure LatticeBase (ell : ℕ) [Fact ell.Prime] where
  E : Type (u + 1)
  field : Field E
  algebra : Algebra ℚ_[ell] E
  finiteDimensional : FiniteDimensional ℚ_[ell] E
  subfield : PadicAlgCl.FiniteIntermediateField ell
  identification : E ≃ₐ[ℚ_[ell]] subfield
  X : Scheme.{u}
  noetherian : IsNoetherian X
  separated : X.IsSeparated
  invertible : ∀ x : X, Invertible (ell : X.residueField x)

attribute [instance] LatticeBase.field LatticeBase.algebra LatticeBase.finiteDimensional
  LatticeBase.noetherian LatticeBase.separated LatticeBase.invertible

/-- Exact automorphism inverse image is the published action used for strict Weil pairs.
Source: curve-heart proof, automorphism paragraph
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
abbrev action (ell : ℕ) [Fact ell.Prime] {T : Scheme.{u}} (g : T ≅ T) :=
  CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj ell) g

/-- The canonical square of ordinary inverse images from composition and the given square.
Source: curve-heart proof, automorphism paragraph
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
def pullSquare (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ≅ X) (gY : Y ≅ Y) (h : gX.hom ≫ f = f ≫ gY.hom) :
    pull ell gY.hom ⋙ pull ell f ≅ pull ell f ⋙ pull ell gX.hom :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell) f gY.hom).symm ≪≫
    CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj ell) h.symm ≪≫
    CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell) gX.hom f

/-- The same canonical square on total derived pullback and exact automorphism actions.
Source: curve-heart proof, automorphism paragraph
(blueprint: lem-per-condensed-curve-restriction-calculus). -/
def derivedPullSquare (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ≅ X) (gY : Y ≅ Y) (h : gX.hom ≫ f = f ≫ gY.hom) :
    action ell gY ⋙ derivedPull ell f ≅ derivedPull ell f ⋙ action ell gX :=
  Functor.isoWhiskerLeft (action ell gY)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj ell) f) ≪≫
    (Functor.mapDerivedCategoryCompIso (pull ell gY.hom) (pull ell f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pullSquare ell f gX gY h) ≪≫
    Functor.mapDerivedCategoryCompIso (pull ell f) (pull ell gX.hom) ≪≫
    Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj ell) f).symm (action ell gX)

end AlgebraicGeometry.ProEtale.CondensedCurve
