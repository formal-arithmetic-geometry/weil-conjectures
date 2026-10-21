/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Sheaf.Paper.CompactSupportCoefficientAction
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
import Sheaf.Paper.CompactSupportFiniteFieldIndependence
import Sheaf.Paper.CompletedOpenExchangeTransport

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Immersion operations on constructible Weil pairs

Source: blueprint main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction and Part 2
(blueprint: lem-zl-immersion-weil-local-behavior).

The clause packages retain the canonical underlying comparisons. Weil complexes are
fixed pairs, and no triangulated structure on their category is asserted.

## Main statements

* `immersionWeil_closed_point`: closed images and canonical residue-field isomorphisms.
* `immersionWeil_pullback_local_behavior`: exact pullback and Frobenius-equivariant stalks.
* `immersionWeil_open_local_behavior`: exact open compact support and its stalk formulas.
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

include prime hl in
/-- The excluded characteristic makes the coefficient prime a unit in the closure.
Source: blueprint finite-field hypotheses
(blueprint: lem-zl-immersion-weil-local-behavior).
Proof: D.k has characteristic D.p; distinct primes have nonzero images in that field,
so l is a unit. This is the coefficient-invertibility assumption of compact support. -/
theorem immersionWeil_coefficient_unit : IsUnit (l : D.k) := by
  sorry

/-- Open immersions remain open on the specified geometric fibre.
Source: blueprint Part 2, geometric base change
(blueprint: lem-zl-immersion-weil-local-behavior).
Proof: the underlying fibre morphism is the base change of the open immersion.
Open immersions are stable under base change (def-weil-open-immersion). -/
@[instance] theorem immersionWeilFiberMap_open (j₀ : W₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    IsOpenImmersion (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left) := by
  sorry

/-- The geometric-fibre map is over the algebraic closure by its second projection.
Source: blueprint base change convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance immersionWeilFiberMap_isOver (j₀ : W₀ ⟶ X₀) :
    (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left).IsOver
      (Spec (.of D.k)) :=
  inferInstanceAs ((((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left).IsOver _)

include hftX hqcX hsepX hftW hqcW hsepW in
/-- An open between these finite-type schemes is quasi-compact.
Source: blueprint Part 2, proof step 7
(blueprint: lem-zl-immersion-weil-local-behavior).
Proof: the target is Noetherian (lem-weil-pbc-finite-type-over-noetherian).
Every open of a Noetherian affine is quasi-compact, by
lem-weil-pbc-noetherian-open-subscheme-noetherian, giving the affine-cover criterion. -/
@[instance] theorem immersionWeilFiberMap_quasiCompact (j₀ : W₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    QuasiCompact (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left) := by
  sorry

/-- The already normalized rational compact-support functor for the open compactification.
Source: blueprint Part 2; compact-support definition order 1490
(blueprint: lem-zl-immersion-weil-local-behavior). -/
@[irreducible] def immersionWeilOpenRationalFunctor
    (j₀ : W₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    sfRationalConstructibleCategory l E (D.geometricFiber W₀).left ⥤
      sfRationalConstructibleCategory l E (D.geometricFiber X₀).left :=
  sfCompactSupportFiniteFunctor l D.k (immersionWeil_coefficient_unit D l hl)
    (Compactification.ofIsOpenImmersion (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)) E

/-- The published normalized common-stage action for the open compactification.
This is a specialization, retaining all strict-tower maps and scalar comparisons.
Source: blueprint Part 2; compact-support definition order 1490
(blueprint: lem-zl-immersion-weil-local-behavior). -/
abbrev ImmersionWeilOpenAction (j₀ : W₀ ⟶ X₀) [IsOpenImmersion j₀.left] :=
  SfCompactSupportCoefficientAction l D.k (immersionWeil_coefficient_unit D l hl) Ω
    (Compactification.ofIsOpenImmersion (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left))

/-- The normalized common-stage compact-support functor, with its implementation
kept behind its functor type so statement elaboration does not expand the Roos data.
Source: blueprint Part 2; compact-support definition order 1490
(blueprint: lem-zl-immersion-weil-local-behavior). -/
@[irreducible] def immersionWeilOpenCommonStageFunctor
    (j₀ : W₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    (S : ImmersionWeilOpenAction D l hl X₀ W₀ Ω j₀) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber W₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left :=
  S.system.functor

variable (j₀ : W₀ ⟶ X₀) [IsOpenImmersion j₀.left]

/-- The finite-stage open clauses. The unit equation specifies the Frobenius mate;
the inverse stalk formula is the open unit followed by inverse pullback composition.
The complement clause is degree-zero cohomology of the recorded point fibre.
Source: blueprint Part 2 (blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ImmersionWeilRationalOpenExtension where
  pullback : ImmersionWeilRationalPullback D l hl X₀ W₀ j₀ E
  comparison : ImmersionWeilExactComparison
    (sfRationalStandardTStructure l E (D.geometricFiber W₀).left D hl)
    (sfRationalStandardTStructure l E (D.geometricFiber X₀).left D hl)
    (sfRationalHeartProperty l E (D.geometricFiber W₀).left)
    (sfRationalHeartProperty l E (D.geometricFiber X₀).left)
    (sfWeilFrobeniusPullback D l hl W₀ E) (sfWeilFrobeniusPullback D l hl X₀ E)
    (immersionWeilOpenRationalFunctor D l hl X₀ W₀ E j₀)
  adjunction : immersionWeilOpenRationalFunctor D l hl X₀ W₀ E j₀ ⊣
    @rationalDerivedPullback l _ E _ _ _ _ _ (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
      (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)
  unit_isIso : IsIso adjunction.unit
  frobenius_unit : ∀ K : sfRationalConstructibleCategory l E (D.geometricFiber W₀).left,
    (sfWeilFrobeniusPullback D l hl W₀ E).map (adjunction.unit.app K) ≫
      pullback.comparison.frobenius.hom.app
        ((immersionWeilOpenRationalFunctor D l hl X₀ W₀ E j₀).obj K) ≫
      (@rationalDerivedPullback l _ E _ _ _ _ _ (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
        (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)).map
          (comparison.frobenius.hom.app K) =
      adjunction.unit.app ((sfWeilFrobeniusPullback D l hl W₀ E).obj K)
  unit_weil : 𝟭 (sfWeilComplex D l hl W₀ E) ≅
    IsoAlgebra.mapOfNatIso comparison.frobenius ⋙
      IsoAlgebra.mapOfNatIso pullback.comparison.frobenius
  unit_underlying : ∀ K : sfWeilComplex D l hl W₀ E,
    HEq ((sfWeilForget D l hl W₀ E).map (unit_weil.hom.app K))
      (adjunction.unit.app K.carrier)
  stalk : ∀ (G : sfWeilSheaf D l hl W₀ E)
    (zbar : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left),
    (DerivedCategory.coefficientFdCohomology E 0).obj
        (localPointComplex l E D hl X₀
          ((IsoAlgebra.mapOfNatIso comparison.frobenius).obj G.obj)
          (zbar ≫ ((Over.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)) ≅
      (DerivedCategory.coefficientFdCohomology E 0).obj
        (localPointComplex l E D hl W₀ G.obj zbar)
  stalk_formula : ∀ (G : sfWeilSheaf D l hl W₀ E)
    (zbar : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left),
    HEq (stalk G zbar).inv
      ((DerivedCategory.coefficientFdCohomology E 0).map
        ((pointRationalFibre D l hl E).map
        ((@rationalDerivedPullback l _ E _ _ _ _ _ zbar
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl W₀)).map
            (adjunction.unit.app G.obj.carrier)) ≫
        (pointRationalFibre D l hl E).map
          (@localPullbackComposition l _ E _ _ _ _ _ _ zbar (((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
            (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl W₀)
            (sfWeilPrimeInvertible D l hl X₀)
            ((immersionWeilOpenRationalFunctor D l hl X₀ W₀ E j₀).obj G.obj.carrier)).inv))
  stalk_frobenius : ∀ (G : sfWeilSheaf D l hl W₀ E)
    (z : {z : W₀.left // z ∈ closedPoints W₀.left})
    (ι : W₀.left.residueField z.val →+* D.k)
    (hι : ι.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k),
    ∃ hx : (localClosedPoint D W₀ z ι hι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left) ≫
        localPositivePower (D.geometricFrobenius X₀).hom
          (localClosedPointDegree D W₀ z - 1) =
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1) ≫
        (localClosedPoint D W₀ z ι hι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left),
      localFrobeniusCohomology l E D hl X₀
          ((IsoAlgebra.mapOfNatIso comparison.frobenius).obj G.obj)
          (localClosedPoint D W₀ z ι hι ≫ ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
          (localClosedPointDegree D W₀ z - 1) hx 0 ≫
        (stalk G (localClosedPoint D W₀ z ι hι)).hom =
      (stalk G (localClosedPoint D W₀ z ι hι)).hom ≫
        localClosedFrobeniusCohomology l E D hl W₀ G.obj z ι hι 0
  zero_stalk : ∀ (G : sfWeilSheaf D l hl W₀ E)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left}),
    x.val ∉ Set.range j₀.left →
    ∀ (ι : X₀.left.residueField x.val →+* D.k)
      (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
      IsZero ((DerivedCategory.coefficientFdCohomology E 0).obj
        (localPointComplex l E D hl X₀
          ((IsoAlgebra.mapOfNatIso comparison.frobenius).obj G.obj)
          (localClosedPoint D X₀ x ι hι)))

/-- All open clauses on the actual common-stage category, with every finite-stage
comparison fixed by the normalized compact-support action. Descent includes arbitrary
complexes and heart objects, so the finite-stage stalk formulas apply to every
algebraically closed Weil sheaf, after the coefficient extension prescribed by the
common-stage point-fibre convention.
Source: blueprint Part 2 (blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ImmersionWeilCommonStageOpenExtension
    (S : ImmersionWeilOpenAction D l hl X₀ W₀ Ω j₀) where
  stages : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ImmersionWeilRationalOpenExtension D l hl X₀ W₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) j₀
  comparison : ImmersionWeilExactComparison
    (sfCommonStageStandardTStructure l (D.geometricFiber W₀).left Ω D hl)
    (sfCommonStageStandardTStructure l (D.geometricFiber X₀).left Ω D hl)
    (sfCommonStageHeartProperty l (D.geometricFiber W₀).left Ω)
    (sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl W₀ Ω)
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (immersionWeilOpenCommonStageFunctor D l hl X₀ W₀ Ω j₀ S)
  stage_comparison : ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfWeilComplex D l hl W₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
    ∃ c : (IsoAlgebra.mapOfNatIso comparison.frobenius).obj
          (sfWeilStageObject D l hl W₀ Ω L K) ≅
        sfWeilStageObject D l hl X₀ Ω L
          ((IsoAlgebra.mapOfNatIso (stages L).comparison.frobenius).obj K),
      HEq ((sfCommonStageWeilForget D l hl X₀ Ω).map c.hom)
        (𝟙 ((IsoAlgebra.mapOfNatIso comparison.frobenius).obj
          (sfWeilStageObject D l hl W₀ Ω L K)).carrier)
  complex_descent : ∀ K : sfCommonStageWeilComplex D l hl W₀ Ω,
    ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : sfWeilComplex D l hl W₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
      Nonempty (K ≅ sfWeilStageObject D l hl W₀ Ω L M)
  sheaf_descent : ∀ G : sfCommonStageWeilSheaf D l hl W₀ Ω,
    ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : sfWeilSheaf D l hl W₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
      Nonempty (G.obj ≅ sfWeilStageObject D l hl W₀ Ω L M.obj)

include hftX hqcX hsepX hftW hqcW hsepW in
/-- Open compact support is t-exact and restricts to exact extension by zero on
constructible Weil sheaves. Its canonical cohomology comparisons are Weil isomorphisms;
stalks are the original Frobenius modules on the open and zero on its complement.
Source: blueprint Part 2 (blueprint: lem-zl-immersion-weil-local-behavior).
Proof: (1) represent all finite diagrams, including the Weil isomorphism and its
inverse equations, over one coefficient field. (7) The geometric open immersion is
quasi-compact since the target is Noetherian. For the compactification (j,id), the
finite-level operation is exact extension by zero. The normalized integral open
reduction comparison identifies the completed compact-support operation with termwise
extension by zero, preserving completeness. Exactness of localized-site extension and
lem-weil-pbc-exact-functor-complex-cohomology give the cohomology comparison. Integral
compact-support constructibility gives the claimed constructible range. (8) Rationalize;
the standard halves are isomorphism closures of integral halves. Truncation uniqueness
gives the normalized cohomology isomorphism. The open tensor normalization and
extension-by-zero product/limit preservation make these comparisons compatible with
scalar extension. The published normalized coefficient action gives common-stage maps.
(9) Completed open base change along geometric Frobenius gives the displayed mate.
Its open unit normalization is exactly frobenius_unit, so unit_weil is equivariant.
Truncation uniqueness makes the cohomology maps equivariant too. (10) On the open,
compose inverse pullback composition with the inverse open unit, giving stalk_formula.
The pullback Frobenius calculation gives stalk_frobenius with the same residue degree.
On the complement base change to the point gives extension from the empty site, zero;
rationalize and extend coefficients to obtain zero_stalk. (11) Exact Frobenius preserves
kernels and cokernels in the constructible heart. The exact underlying extension by
zero preserves their universal maps, proving exactness on Weil sheaves. -/
theorem immersionWeil_open_local_behavior :
    ∃ S : ImmersionWeilOpenAction D l hl X₀ W₀ Ω j₀,
      Nonempty (ImmersionWeilCommonStageOpenExtension D l hl X₀ W₀ Ω j₀ S) := by
  sorry

end WeilConjectures
