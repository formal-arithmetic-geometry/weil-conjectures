/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralPullbackComposition
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.Paper.CompletedOpenExchangeTransport

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Pullback and finite descent for constructible Weil pairs

Source: blueprint main-20261015, Restriction in
`lem-zl-immersion-weil-local-behavior`.

This is the unchanged pullback and descent interface extracted from
`ImmersionWeilLocalBehavior`. It depends on pullback and local Frobenius, so its
consumers can use it before the separate compact-support interface is restored.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genInjectivity false
universe u v uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Clauses of t-exactness, exactness on Weil hearts, and the natural Weil cohomology
comparison. Its underlying comparison is the normalized truncation comparison.
Source: blueprint Restriction and Part 2
(blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ImmersionWeilExactComparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (t : TStructure C) (s : TStructure B)
    (P : ObjectProperty C) (Q : ObjectProperty B)
    (Φ : C ⥤ C) (Ψ : B ⥤ B) (F : C ⥤ B) where
  sourceFrobenius : ConstructiblePullbackComparison t t P P Φ
  targetFrobenius : ConstructiblePullbackComparison s s Q Q Ψ
  underlying : ConstructiblePullbackComparison t s P Q F
  frobenius : F ⋙ Ψ ≅ Φ ⋙ F
  heart : (P.inverseImage (IsoAlgebra.forget Φ)).FullSubcategory ⥤
    (Q.inverseImage (IsoAlgebra.forget Ψ)).FullSubcategory
  heart_fac : heart ⋙ (Q.inverseImage (IsoAlgebra.forget Ψ)).ι =
    (P.inverseImage (IsoAlgebra.forget Φ)).ι ⋙ IsoAlgebra.mapOfNatIso frobenius
  heart_limits : PreservesFiniteLimits heart
  heart_colimits : PreservesFiniteColimits heart
  cohomology : ∀ a : ℤ,
    IsoAlgebra.mapOfNatIso (sourceFrobenius.cohomology a) ⋙
        IsoAlgebra.mapOfNatIso frobenius ≅
      IsoAlgebra.mapOfNatIso frobenius ⋙
        IsoAlgebra.mapOfNatIso (targetFrobenius.cohomology a)
  cohomology_underlying : ∀ (a : ℤ) (K : IsoAlgebra Φ),
    HEq ((IsoAlgebra.forget Ψ).map ((cohomology a).hom.app K))
      ((underlying.cohomology a).hom.app K.carrier)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [prime : Fact l.Prime] (hl : l ≠ D.p)
  (X₀ W₀ : Over (Spec (.of D.k₀)))
  [hftX : LocallyOfFiniteType X₀.hom] [hqcX : QuasiCompact X₀.hom] [hsepX : IsSeparated X₀.hom]
  [hftW : LocallyOfFiniteType W₀.hom] [hqcW : QuasiCompact W₀.hom] [hsepW : IsSeparated W₀.hom]
  (h₀ : W₀ ⟶ X₀) [himm : IsImmersion h₀.left]

/-- The finite-type structure on the actual geometric fibre is inherited by base change.
Source: blueprint geometric-base-change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilOverPullback_locallyOfFiniteType {B T : Scheme.{u}} (f : T ⟶ B)
    (Y : Over B) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (((Over.pullback f).obj Y).left ↘ T) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd Y.hom f))

/-- Quasi-compactness on a geometric fibre is inherited by base change.
Source: blueprint geometric-base-change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilOverPullback_quasiCompact {B T : Scheme.{u}} (f : T ⟶ B)
    (Y : Over B) [QuasiCompact Y.hom] :
    QuasiCompact (((Over.pullback f).obj Y).left ↘ T) :=
  inferInstanceAs (QuasiCompact (pullback.snd Y.hom f))

/-- Finite type on the named geometric fibre, before unfolding its bundled object.
Source: blueprint geometric-base-change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilFiber_locallyOfFiniteType :
    LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness on the named geometric fibre, before unfolding its bundle.
Source: blueprint geometric-base-change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilFiber_quasiCompact :
    QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (QuasiCompact
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

include hftX hqcX hsepX hftW hqcW hsepW himm in
/-- Closed points and the *canonical* residue-field map for a locally closed immersion.
Source: blueprint Restriction (blueprint: lem-zl-immersion-weil-local-behavior).
Proof: factor the immersion into closed then open. The open factor identifies local
rings; the closed factor is a quotient on local rings and identifies their residue
fields. A closed point of a finite-type finite-field scheme has finite residue field
(lem-kun-closed-point-field). The converse on X₀ shows that its image is closed. -/
theorem immersionWeil_closed_point (z : W₀.left) (hz : z ∈ closedPoints W₀.left) :
    h₀.left z ∈ closedPoints X₀.left ∧ IsIso (h₀.left.residueFieldMap z) := by
  sorry

variable (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The rational pullback clauses, with the Frobenius comparison fixed by the
specified pullback-composition maps, and the stalk map fixed by composition too.
Source: blueprint Restriction (blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ImmersionWeilRationalPullback where
  comparison : ImmersionWeilExactComparison
    (sfRationalStandardTStructure l E (D.geometricFiber X₀).left D hl)
    (sfRationalStandardTStructure l E (D.geometricFiber W₀).left D hl)
    (sfRationalHeartProperty l E (D.geometricFiber X₀).left)
    (sfRationalHeartProperty l E (D.geometricFiber W₀).left)
    (sfWeilFrobeniusPullback D l hl X₀ E) (sfWeilFrobeniusPullback D l hl W₀ E)
    (@rationalDerivedPullback l _ E _ _ _ _ _ (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left)
      (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀))
  commutes : (D.geometricFrobenius W₀).hom ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left =
    ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left ≫
      (D.geometricFrobenius X₀).hom
  frobenius_formula : ∀ K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left,
    HEq (comparison.frobenius.app K)
      ((@localPullbackComposition l _ E _ _ _ _ _ _
          (D.geometricFrobenius W₀).hom (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left)
          (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl W₀)
          (sfWeilPrimeInvertible D l hl X₀) K).symm ≪≫
        eqToIso (congrArg
          (fun f ↦ (@rationalDerivedPullback l _ E _ _ _ _ _ f
            (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)).obj K)
          commutes) ≪≫
        @localPullbackComposition l _ E _ _ _ _ _ _ (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left)
          (D.geometricFrobenius X₀).hom
          (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)
          (sfWeilPrimeInvertible D l hl X₀) K)

  stalk : ∀ (F : sfWeilSheaf D l hl X₀ E)
    (zbar : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left),
    (DerivedCategory.coefficientFdCohomology E 0).obj
        (localPointComplex l E D hl W₀
          ((IsoAlgebra.mapOfNatIso comparison.frobenius).obj F.obj) zbar) ≅
      (DerivedCategory.coefficientFdCohomology E 0).obj
        (localPointComplex l E D hl X₀ F.obj (zbar ≫ ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left))
  stalk_formula : ∀ (F : sfWeilSheaf D l hl X₀ E)
    (zbar : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left),
    HEq (stalk F zbar).hom
      ((DerivedCategory.coefficientFdCohomology E 0).map
        ((pointRationalFibre D l hl E).map
        (@localPullbackComposition l _ E _ _ _ _ _ _ zbar (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left)
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl W₀)
          (sfWeilPrimeInvertible D l hl X₀) F.obj.carrier).inv))
  stalk_frobenius : ∀ (F : sfWeilSheaf D l hl X₀ E)
    (z : {z : W₀.left // z ∈ closedPoints W₀.left})
    (ι : W₀.left.residueField z.val →+* D.k)
    (hι : ι.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k),
    ∃ hx : (localClosedPoint D W₀ z ι hι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left) ≫
        localPositivePower (D.geometricFrobenius X₀).hom
          (localClosedPointDegree D W₀ z - 1) =
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1) ≫
        (localClosedPoint D W₀ z ι hι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left),
      localClosedFrobeniusCohomology l E D hl W₀
          ((IsoAlgebra.mapOfNatIso comparison.frobenius).obj F.obj) z ι hι 0 ≫
        (stalk F (localClosedPoint D W₀ z ι hι)).hom =
      (stalk F (localClosedPoint D W₀ z ι hι)).hom ≫
        localFrobeniusCohomology l E D hl X₀ F.obj
          (localClosedPoint D W₀ z ι hι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left)
          (localClosedPointDegree D W₀ z - 1) hx 0

variable (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Common-stage pullback, together with its finite-stage normalization. The identity
underlying the last isomorphism identifies the two literal pulled-back stage pairs;
its existence asserts equivariance for precisely that identification.
Source: blueprint Restriction, common-stage convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ImmersionWeilCommonStagePullback where
  stages : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ImmersionWeilRationalPullback D l hl X₀ W₀ h₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
  comparison : ImmersionWeilExactComparison
    (sfCommonStageStandardTStructure l (D.geometricFiber X₀).left Ω D hl)
    (sfCommonStageStandardTStructure l (D.geometricFiber W₀).left Ω D hl)
    (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω)
    (sfCommonStageHeartProperty l (D.geometricFiber W₀).left Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl W₀ Ω)
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _ (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left)
      (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀))
  stage_comparison : ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
    ∃ c : (IsoAlgebra.mapOfNatIso comparison.frobenius).obj
          (sfWeilStageObject D l hl X₀ Ω L K) ≅
        sfWeilStageObject D l hl W₀ Ω L
          ((IsoAlgebra.mapOfNatIso (stages L).comparison.frobenius).obj K),
      HEq ((sfCommonStageWeilForget D l hl W₀ Ω).map c.hom)
        (𝟙 ((IsoAlgebra.mapOfNatIso comparison.frobenius).obj
          (sfWeilStageObject D l hl X₀ Ω L K)).carrier)
  complex_descent : ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
    ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
      Nonempty (K ≅ sfWeilStageObject D l hl X₀ Ω L M)
  sheaf_descent : ∀ F : sfCommonStageWeilSheaf D l hl X₀ Ω,
    ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : sfWeilSheaf D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
      Nonempty (F.obj ≅ sfWeilStageObject D l hl X₀ Ω L M.obj)

include hftX hqcX hsepX hftW hqcW hsepW himm in
/-- Pullback is t-exact, is exact on constructible Weil sheaves, commutes naturally
with cohomology, and has the canonical Frobenius-equivariant stalk comparisons.
Source: blueprint Restriction (blueprint: lem-zl-immersion-weil-local-behavior).
Proof: (1) represent the finitely many Weil arrows and their inverse equations over
one finite coefficient field, enlarging that field if necessary. No stable integral
Frobenius lattice is required. (2) Apply lem-a1-constructible-pullback-t-exact to the
geometric base change. Pullback composition (lem-pod-integral-pullback-composition)
and Frobenius naturality give the displayed normalized commutation comparison;
IsoAlgebra.mapOfNatIso equips pullback with its induced Weil structure. (3) Uniqueness
of truncation triangles (lem-weil-heart-short-exact-triangles) makes the canonical
cohomology comparisons Weil-equivariant. (4) Closed-then-open factorization identifies
residue fields and closed points, as in immersionWeil_closed_point. (5) The inverse
pullback-composition comparison followed by the point fibre gives the displayed
stalk identification. (6) Iterate the Weil structure using pullback associativity.
At the common residue degree, the point-return comparisons agree. Naturality of
point transport (lem-weil-frobenius-point-transport-natural), applied successively,
commutes with that stalk identification. Each of the three defining factors of
local Frobenius therefore commutes with it. Degree-zero cohomology is the sheaf
stalk formula. (11) Kernels and cokernels in the constructible heart inherit invertible
Weil structures from exact Frobenius pullback; the exact underlying pullback preserves
their universal maps. All constructions descend using the recorded scalar comparisons. -/
theorem immersionWeil_pullback_local_behavior :
    Nonempty (ImmersionWeilCommonStagePullback D l hl X₀ W₀ h₀ Ω) := by
  sorry

end WeilConjectures
