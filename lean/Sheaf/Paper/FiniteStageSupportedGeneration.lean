/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.NormAlgclCohomologyTopologyComparison
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.InternalScalarPullbackNormalization
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.SixFunctors.OpenTensorNormalizationData
import Sheaf.Paper.CoefficientHeartGeneration
import Sheaf.Paper.CoefficientHeartTriangulated
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.Algebra.Homology.KFlatHomotopyTriangulated
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite-stage supported generators and their derived scalar images

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
coefficient-change obligation, and the nine-step extracted proof.
(blueprint: lem-sfb-finite-stage-supported-generation).

The algebraic closure is the library's chosen PadicAlgCl. The rings C and B are
respectively finite-subextension-valued and all norm-continuous sections. Scalars
are the existing ordinary unbounded total left derived functors. Support uses
open extension by zero followed by closed direct image; its total right derived
closed factor is identified with the termwise exact factor in the assertions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteStageGeneration

open QuotientChange

variable {R R' R'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj R'] [IsCommMonObj R']
  [MonObj R''] [IsCommMonObj R'']

/-- Open-then-closed extension on the ordinary unbounded derived categories.
Source: direct-images proof (3), support factorization; the closed factor is exact
under the standing Noetherian hypotheses.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def support (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S Z X : Scheme.{u}}
    (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) :
    DerivedCategory (Modules Λ S) ⥤ DerivedCategory (Modules Λ X) :=
  (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
    (CondensedRing.lowerStar Λ i).rightDerivedFunctor

/-- The universal derived counit followed by the termwise single-object comparison.
This is the actual map to ordinary scalar extension in degree zero.
Source: direct-images proof (3), lisse degree-zero comparison; Stacks 06YY.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def singleComparison (φ : R ⟶ R') [IsMonHom φ] (T : Scheme.{u})
    (M : Modules R T) :
    (D φ T).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((extension φ T).obj M) :=
  compute φ T ((CochainComplex.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Q.map (((extension φ T).mapCochainComplexSingleFunctor 0).hom.app M)

/-- Triangulated scalar extension with its shift-compatible specified scalar unit.
The shift structure is part of the assertion, rather than a flatness hypothesis.
Source: extracted proof, step 2; Stacks 06YY and 07A6.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def ExactScalarUnit (φ : R ⟶ R') [IsMonHom φ] (T : Scheme.{u})
    (s : (D φ T).CommShift ℤ) : Prop :=
  letI := s
  (D φ T).IsTriangulated ∧ (V φ T).IsTriangulated ∧
    NatTrans.CommShift (scalarAdj φ T).unit ℤ ∧
    NatTrans.CommShift (scalarCounit φ T) ℤ

/-- Section-module agreement uses the existing normalized reconstruction interface.
The section localizations are asserted to exist in the internal Hom universe,
and to intertwine the actual scalar functor and its K-flat computation. This adds
no hypothesis on the rings or the scheme.
Source: extracted proof, step 2; Stacks 03EK, 06YY and 07A6.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def SectionAgreement (φ : R ⟶ R') [IsMonHom φ] (T : Scheme.{u}) : Prop :=
  ∃ (hR : ∀ S : Scheme.{u},
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R S))
    (hR' : ∀ S : Scheme.{u},
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R' S)),
    letI := hR
    letI := hR'
    ∃ s : SectionScalarComparison φ T, SectionScalarNormalized φ T s

/-- All scalar assertions at a scheme, including K-flat computation, the actual
ordinary unit on every representative, and the lisse degree-zero comparison.
Source: extracted proof, steps 2 and 3; Stacks 06YY, 07A6 and 0GN1.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def ScalarAssertions (φ : R ⟶ R') [IsMonHom φ] (T : Scheme.{u}) : Prop :=
  (∃ s : (D φ T).CommShift ℤ, ExactScalarUnit φ T s) ∧
  PreservesFiniteLimits (V₀ φ T) ∧ PreservesFiniteColimits (V₀ φ T) ∧
  (∀ P : CochainComplex (Modules R T) ℤ,
    (HomologicalComplex.quasiIso (Modules R T) (.up ℤ)).kFlat P →
      IsIso (compute φ T P)) ∧
  (∀ P : CochainComplex (Modules R T) ℤ,
    (scalarAdj φ T).unit.app (DerivedCategory.Q.obj P) ≫
        (V φ T).map (compute φ T P) ≫
        (V₀ φ T).mapDerivedCategoryFactors.hom.app
          (((extension φ T).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction (coefficientMap φ T)).mapHomologicalComplex
          (.up ℤ)).unit.app P)) ∧
  SectionAgreement φ T ∧
  ∀ M : Modules R T, IsLisseCoefficientModule R M →
    IsIso (singleComparison φ T M) ∧
      IsLisseCoefficientModule R' ((extension φ T).obj M)

/-- The normalized inverse-image comparison, together with support comparisons
for every open-then-closed factorization into the specified ambient scheme.
Source: extracted proof, steps 3--5; Stacks 09AA, 09BN and 09AH.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
structure Comparisons (φ : R ⟶ R') [IsMonHom φ] (X : Scheme.{u}) where
  source_closed_exact {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (CondensedRing.lowerStar R i)
  target_closed_exact {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (CondensedRing.lowerStar R' i)
  pull {S T : Scheme.{u}} (f : S ⟶ T) : D φ T ⋙ L R' f ≅ L R f ⋙ D φ S
  pull_normalized {S T : Scheme.{u}} (f : S ⟶ T) : PullNormalized φ f (pull f)
  supported {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    support R j i ⋙ D φ X ≅ D φ S ⋙ support R' j i

/-- The identity composition of termwise restrictions, localized canonically.
Source: extracted proof, step 6, scalar transitivity.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def restrictionTower (φ : R ⟶ R') [IsMonHom φ] (ψ : R' ⟶ R'') [IsMonHom ψ]
    (T : Scheme.{u}) : V ψ T ⋙ V φ T ≅ V (φ ≫ ψ) T :=
  (Functor.mapDerivedCategoryCompIso (V₀ ψ T) (V₀ φ T)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp (coefficientMap φ T) (coefficientMap ψ T)).symm ≪≫
        Mod.comapCongr (coefficientMap_comp φ ψ T).symm)

/-- Coherence of the three actual scalar functors and the same support/pullback
comparisons. The tower is normalized by the composite scalar units; on balanced
representatives its inverse contracts c tensor (b tensor v) to cb tensor v.
Source: extracted proof, step 6; scalar-six pullback proof (3).
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def TowerCompatible (φ : R ⟶ R') [IsMonHom φ] (ψ : R' ⟶ R'') [IsMonHom ψ]
    (X : Scheme.{u}) (a : Comparisons φ X) (b : Comparisons ψ X)
    (c : Comparisons (φ ≫ ψ) X) : Prop :=
  ∃ τ : ∀ T : Scheme.{u}, D (φ ≫ ψ) T ≅ D φ T ⋙ D ψ T,
    (∀ T : Scheme.{u}, SuccessiveNormalized φ ψ (φ ≫ ψ) rfl T (τ T).symm) ∧
    (∀ (T : Scheme.{u}) (M : DerivedCategory (Modules R T)),
      (scalarAdj (φ ≫ ψ) T).unit.app M ≫
          (V (φ ≫ ψ) T).map ((τ T).hom.app M) =
        (scalarAdj φ T).unit.app M ≫
          (V φ T).map ((scalarAdj ψ T).unit.app ((D φ T).obj M)) ≫
          (restrictionTower φ ψ T).hom.app ((D ψ T).obj ((D φ T).obj M))) ∧
    (∀ {S T : Scheme.{u}} (f : S ⟶ T) (K : DerivedCategory (Modules R T)),
      (c.pull f).hom.app K =
        (L R'' f).map ((τ T).hom.app K) ≫
          (b.pull f).hom.app ((D φ T).obj K) ≫
          (D ψ S).map ((a.pull f).hom.app K) ≫
          (τ S).inv.app ((L R f).obj K)) ∧
    (∀ {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
        (i : Z ⟶ X) [IsClosedImmersion i] (K : DerivedCategory (Modules R S)),
      (c.supported j i).hom.app K =
        (τ X).hom.app ((support R j i).obj K) ≫
          (D ψ X).map ((a.supported j i).hom.app K) ≫
          (b.supported j i).hom.app ((D φ S).obj K) ≫
          (support R'' j i).map ((τ S).inv.app K)) ∧
    ∀ (T : Scheme.{u}) (M : Modules R T), IsLisseCoefficientModule R M →
      singleComparison (φ ≫ ψ) T M =
        (τ T).hom.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
          (D ψ T).map (singleComparison φ T M) ≫
          singleComparison ψ T ((extension φ T).obj M) ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((ordinaryComp φ ψ (φ ≫ ψ) rfl T).hom.app M)

/-- The specified generator, with its finite-field lisse input derived before support.
Source: extracted proof, step 7, displayed G_{a,E,L}.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def generator (ℓ : ℕ) [Fact ℓ.Prime] {S Z X : Scheme.{u}}
    (j : S ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (M : Modules (Profinite.continuousMapRingObj E) S) :
    DerivedCategory (Modules (Profinite.padicAlgClRingObj ℓ) X) :=
  (support (Profinite.padicAlgClRingObj ℓ) j i).obj
    ((D (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) S).obj
      ((DerivedCategory.singleFunctor _ 0).obj M))

/-- Replete class of all the specified constructible locally closed generators.
Source: extracted proof, step 7; finite fields and rank zero are unrestricted.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def IsGenerator (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Modules (Profinite.padicAlgClRingObj ℓ) X)) :=
  fun K ↦ ∃ (S Z : Scheme.{u}) (j : S ⟶ Z) (hj : IsOpenImmersion j)
    (i : Z ⟶ X), IsClosedImmersion i ∧ Topology.IsConstructible (Set.range (j ≫ i)) ∧
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (M : Modules (Profinite.continuousMapRingObj E) S),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj E) M ∧
          Nonempty (K ≅ @generator ℓ _ S Z X j hj i E M)

/-- A finite construction from zero and generators by shifts and triangle extensions.
Every operation uses strictly earlier entries, so this records finite generation
without allowing coproducts, infinite extensions or retracts.
Source: extracted proof, steps 7 and 8.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def FiniteConstruction (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    (K : DerivedCategory (Modules (Profinite.padicAlgClRingObj ℓ) X)) : Prop :=
  ∃ (N : ℕ) (F : Fin (N + 1) →
      DerivedCategory (Modules (Profinite.padicAlgClRingObj ℓ) X)),
    Nonempty (F (Fin.last N) ≅ K) ∧ ∀ r : Fin (N + 1),
      IsZero (F r) ∨ IsGenerator ℓ X (F r) ∨
      (∃ (s : Fin (N + 1)) (n : ℤ), s < r ∧ Nonempty (F r ≅ (F s)⟦n⟧)) ∨
      ∃ s t : Fin (N + 1), s < r ∧ t < r ∧
        ∃ (f : F s ⟶ F r) (g : F r ⟶ F t) (h : F t ⟶ (F s)⟦(1 : ℤ)⟧),
          Triangle.mk f g h ∈ distTriang _

/-- Generator membership, the smallest full replete triangulated subcategory, and
an explicit finite-construction characterization of every object of Dbc(X,C).
Source: extracted proof, steps 7 and 8; coefficient-heart generation proof.
(blueprint: lem-sfb-finite-stage-supported-generation). -/
def GenerationAssertions (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) : Prop :=
  (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X).IsTriangulated ∧
  (constantModelBoundedConstructible
    (Profinite.padicAlgClRingObj ℓ) X).IsClosedUnderIsomorphisms ∧
  (∀ K, IsGenerator ℓ X K →
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K) ∧
  (∀ P : ObjectProperty (DerivedCategory (Modules (Profinite.padicAlgClRingObj ℓ) X)),
    P.IsClosedUnderIsomorphisms → P.IsTriangulated →
    (∀ G, IsGenerator ℓ X G → P G) →
    ∀ K, constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K → P K) ∧
  ∀ K, constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K ↔
    FiniteConstruction ℓ X K

/-- The full finite-stage supported-generation statement for the actual coefficient maps.

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md (3), extracted
nine-step proof (blueprint: lem-sfb-finite-stage-supported-generation).

Proof plan:
1. Finite-type affine coordinate rings over k are Noetherian. Quasi-compactness gives
Noetherian X; affine quotient and localization charts show that every locally closed
S is finite type and separated over k, including arbitrary subscheme structures.
2. Transport the normalized scalar adjunction through internal/section reconstruction.
Derived change of rings gives the total K-flat scalar functor and exact termwise
restriction. On P[n] the unit is the same v to 1 tensor v map in degree q+n;
both differentials acquire the same sign. Thus its unit commutes with shifts.
3. On a trivializing cover a lisse module is finite free, so its degree-zero complex
is K-flat and extension is finite free of the same rank. The normalized balanced
pullback comparison descends this calculation and commutes with inverse image.
4. For open j use the scalar and open adjunctions: both scalar-after-j! and
j!-after-scalar are left adjoint to the same restriction/pullback composite.
The unique unit-compatible conjugate gives the natural linear comparison.
5. For closed i, scalar/pullback compatibility makes scalar(i_*K) vanish on the
complementary open. Unbounded support localization identifies its closed unit with
an isomorphism. Follow it by the pullback comparison and closed counit. Compose
with step 4 for an arbitrary open-then-closed factorization.
6. Restrictions compose identically. Uniqueness of adjoints with their composite
units supplies scalar transitivity. Mate pasting proves its support and inverse-
image compatibilities; on balanced representatives contraction multiplies scalars.
7. Lisse derived extension computes ordinary extension. Lisse support extension is
bounded constructible. Conversely coefficient-heart generation expresses every
bounded constructible complex by finitely many supported lisse objects, shifts and
cones. Finite-coefficient descent replaces each lisse C-model by one over finite E.
8. The constructible predicate is replete and triangulated. The finite constructions
lie in any such subcategory containing the generators. Rotate cone triangles to
express them as triangle extensions. Start with zero, also on empty X.
9. Apply support comparison to C to B, contract A_E to C to B, and use the lisse
single comparison. This gives the displayed isomorphism in D(B_X). Zero ranks and
empty supports give zero throughout; no coefficient map is assumed flat. -/
theorem finite_stage_supported_generation
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] :
    IsNoetherian X.left ∧
    (∀ (S : Scheme.{u}) (a : S ⟶ X.left), IsImmersion a →
      IsNoetherian S ∧ LocallyOfFiniteType (a ≫ X.hom) ∧
        QuasiCompact (a ≫ X.hom) ∧ IsSeparated (a ≫ X.hom)) ∧
    (∀ T : Scheme.{u}, ScalarAssertions (NormAlgclComparison.coefficientInclusion ℓ) T) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ) (T : Scheme.{u}),
      ScalarAssertions (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T ∧
      ScalarAssertions (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E ≫
        NormAlgclComparison.coefficientInclusion ℓ) T) ∧
    (∃ b : Comparisons (NormAlgclComparison.coefficientInclusion ℓ) X.left,
      ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        ∃ (a : Comparisons (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X.left)
          (c : Comparisons (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E ≫
            NormAlgclComparison.coefficientInclusion ℓ) X.left),
          TowerCompatible (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
            (NormAlgclComparison.coefficientInclusion ℓ) X.left a b c) ∧
    GenerationAssertions ℓ X.left ∧
    ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) [IsOpenImmersion j]
      (i : Z ⟶ X.left) [IsClosedImmersion i],
      Topology.IsConstructible (Set.range (j ≫ i)) →
      ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (M : Modules (Profinite.continuousMapRingObj E) S),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj E) M →
        Nonempty ((D (NormAlgclComparison.coefficientInclusion ℓ) X.left).obj
          (generator ℓ j i E M) ≅
            (DerivedCategory.singleFunctor _ 0).obj
              ((CondensedRing.lowerStar
                (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) i).obj
                ((CondensedRing.openImmersionLowerShriek
                  (Profinite.continuousMapRingObj (PadicAlgCl ℓ)) j).obj
                  ((extension (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E ≫
                    NormAlgclComparison.coefficientInclusion ℓ) S).obj M)))) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteStageGeneration
