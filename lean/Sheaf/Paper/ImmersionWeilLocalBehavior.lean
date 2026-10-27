/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.ImmersionWeilPullbackLocalBehavior

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

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [prime : Fact l.Prime] (hl : l ≠ D.p)
  (X₀ W₀ : Over (Spec (.of D.k₀)))
  [hftX : LocallyOfFiniteType X₀.hom] [hqcX : QuasiCompact X₀.hom] [hsepX : IsSeparated X₀.hom]
  [hftW : LocallyOfFiniteType W₀.hom] [hqcW : QuasiCompact W₀.hom] [hsepW : IsSeparated W₀.hom]
  (h₀ : W₀ ⟶ X₀) [himm : IsImmersion h₀.left]

variable (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

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
