/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionComparisons
import WeilConjectures.WeilSheaf.Native.Proper.NativeProperSectionTensorModels
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.WeilSheaf.Native.NativePullSheafTensor
public import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperKFlatPullTensorSquare
public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperSectionAdjunctionModels
public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperSectionTensorDescent

/-! # Resolution models for native proper projection

Source: BS 6.8.14--6.8.15; Stacks 070I, 08BJ, 07A4 and 0G7E.
(blueprint: lem-sf-native-proper-projection-models).

These comparisons concern resolutions and tensor pullback; no projection-formula
isomorphism or invertibility assertion is included.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 800000 in
-- The representative and adjunction squares require more than 200000 heartbeats.

private theorem models_of_kflat_tensor_square
    (J : NativeProperSectionAdjunctionModels k₀ l p R S O)
    (hz : Nonempty (ProperSectionTensor k₀ l Z R A))
    (hy : Nonempty (ProperSectionTensor k₀ l Y S B))
    (hflat : ∀ (TZ : ProperSectionTensor k₀ l Z R A)
      (TY : ProperSectionTensor k₀ l Y S B),
      ∃ balanced : NativeProjectionTensorComparison k₀ l p,
      ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ),
      NativeIsKFlat k₀ l Y P → NativeIsKFlat k₀ l Y Q →
      (properSectionDerived k₀ l Z R).map
          (balanced.mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        TZ.tensor.hom.app
          ((nativeOpenPull k₀ l p).obj (DerivedCategory.Q.obj P),
            (nativeOpenPull k₀ l p).obj (DerivedCategory.Q.obj Q)) ≫
        A.closed.tensor.map (Prod.mkHom
          (J.pull.hom.app (DerivedCategory.Q.obj P))
          (J.pull.hom.app (DerivedCategory.Q.obj Q))) =
      J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
            (TY.tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        C.tensor.hom.app
          ((properSectionDerived k₀ l Y S).obj (DerivedCategory.Q.obj P),
            (properSectionDerived k₀ l Y S).obj (DerivedCategory.Q.obj Q))) :
    ∃ (TZ : ProperSectionTensor k₀ l Z R A) (TY : ProperSectionTensor k₀ l Y S B)
      (balanced : NativeProjectionTensorComparison k₀ l p),
    ∀ M N,
    (properSectionDerived k₀ l Z R).map (balanced.mu.hom.app (M, N)) ≫
      TZ.tensor.hom.app
        ((nativeOpenPull k₀ l p).obj M, (nativeOpenPull k₀ l p).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (J.pull.hom.app M) (J.pull.hom.app N)) =
    J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      (ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          (TY.tensor.hom.app (M, N)) ≫
      C.tensor.hom.app
        ((properSectionDerived k₀ l Y S).obj M,
          (properSectionDerived k₀ l Y S).obj N) := by
  obtain ⟨TZ⟩ := hz
  obtain ⟨TY⟩ := hy
  obtain ⟨balanced, hb⟩ := hflat TZ TY
  refine ⟨TZ, TY, balanced, ?_⟩
  exact tensor_square_of_representatives
    (fun P ↦ DerivedCategory.Q.obj P) (NativeIsKFlat k₀ l Y)
    (native_two_sided_kflat_representatives k₀ l Y)
    (nativeOpenPull k₀ l p) (properSectionDerived k₀ l Z R)
    (properSectionDerived k₀ l Y S)
    (ContinuousRational.derivedPull (NativeBaseChange.geometricMap k₀ p) O.coefficient)
    (nativeDerivedTensor k₀ l Y) (nativeDerivedTensor k₀ l Z)
    B.closed.tensor A.closed.tensor balanced.mu TZ.tensor TY.tensor J.pull C.tensor hb

/-- The tensor part of the native proper-projection resolution calculation.
Source: Stacks 07A4, 0G7E and BS 6.8.14--6.8.15; native proper-projection model
proof, step 4 (blueprint: lem-sf-native-proper-section-tensor-models).

Proof: construct the section tensor comparison on sheaves from the identity on
underlying balanced tensors. For complexes, take the direct sum of these maps on
all (i,j) summands. Its generator formula is precisely ProperSectionTensor.generators;
both differentials are d tensor 1 plus (-1)^i 1 tensor d. The inverse is obtained
by the same underlying tensor universal property. The exact section equivalence
and the exact orbit-induction adjunction transfer both quasi-isomorphism tests for
K-flatness. Forgetting native K-flat complexes is K-flat: test against an ordinary
acyclic complex Q by its exact orbit induction, whose underlying complex is the
direct sum of all Frobenius translates of Q. The ordinary tensor with Q is the
split degree-zero summand of the forgotten acyclic total tensor. Thus it too is
acyclic. Apply the same argument in the other tensor variable. Tensor descent
therefore gives TZ and TY, with the stated representative equation on every
K-flat pair, by uniqueness of the tensor-Hom adjunction comparisons.

For p, use the balanced sheaf maps b tensor (x tensor y) maps to
(b tensor x) tensor (1 tensor y), and the inverse multiplies coefficients.
They commute with Frobenius by the coefficient precomposition equation. Their
termwise totalizations retain each summand insertion. For arbitrary K-flat inputs,
use the enough-points stalk criterion and
the inverse-image theorem for ringed sites with enough points; the small pro-etale
site has enough points. The flat-term preservation theorem applies separately to
the chosen flat-term resolutions. The ordinary section coordinates and exact
forgetting identify the required native K-flat tests. Localization constructs
balanced with its presentation, compatibility,
sheaf_forget and representative normalizations. Compute the square on simultaneous
K-flat resolutions. C.representative and TZ.representative and TY.representative
identify its four sides with these same balanced sheaf maps; no extra signs appear.
The pull in J is the canonical one: pushSections and pushRepresentative fix its
right comparison on K-injectives, and J.counit fixes its left adjoint mate. Thus it
is this localized sheaf pull comparison. The two insertion formulas agree on every
pure tensor, proving the square; localization and naturality give it for arbitrary
M and N. Empty sites, zero inputs and identity p use the same formulas. -/
private theorem native_proper_section_tensor_models_legacy
    (J : NativeProperSectionAdjunctionModels k₀ l p R S O)
    (hR : (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence)
    (hS : (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).IsEquivalence) :
    ∃ (TZ : ProperSectionTensor k₀ l Z R A) (TY : ProperSectionTensor k₀ l Y S B)
      (balanced : NativeProjectionTensorComparison k₀ l p),
    ∀ M N,
    (properSectionDerived k₀ l Z R).map (balanced.mu.hom.app (M, N)) ≫
      TZ.tensor.hom.app
        ((nativeOpenPull k₀ l p).obj M, (nativeOpenPull k₀ l p).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (J.pull.hom.app M) (J.pull.hom.app N)) =
    J.pull.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      (ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).map
          (TY.tensor.hom.app (M, N)) ≫
      C.tensor.hom.app
        ((properSectionDerived k₀ l Y S).obj M,
          (properSectionDerived k₀ l Y S).obj N) := by
  have hz : Nonempty (ProperSectionTensor k₀ l Z R A) := by
    obtain ⟨cochain, tensor, generators, representative⟩ :=
      native_proper_section_tensor_descent k₀ l Z R A hR
    exact ⟨{
      cochain := cochain
      generators := generators
      kflat := native_two_sided_kflat_sections k₀ l Z R
      tensor := tensor
      representative := representative }⟩
  have hy : Nonempty (ProperSectionTensor k₀ l Y S B) := by
    obtain ⟨cochain, tensor, generators, representative⟩ :=
      native_proper_section_tensor_descent k₀ l Y S B hS
    exact ⟨{
      cochain := cochain
      generators := generators
      kflat := native_two_sided_kflat_sections k₀ l Y S
      tensor := tensor
      representative := representative }⟩
  obtain ⟨rho, hrho⟩ := native_pull_sheaf_tensor k₀ l p
  exact models_of_kflat_tensor_square k₀ l p R S O A B C J hz hy
    (fun TZ TY ↦ native_proper_kflat_pull_tensor_square
      k₀ l p R S O A B C J hR hS rho hrho TZ TY)

/-- Resolution and tensor comparison data before taking the projection mate.
Source: Steps 1--4 of lem-sf-native-proper-projection-realization;
BS 6.8.14--6.8.15 and Stacks 08BJ, 07A4, 0G7E
(blueprint: lem-sf-native-proper-projection-models). -/
structure NativeProperProjectionModels where
  source : LocallyFiniteAdicRealization.Realization l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
  target : LocallyFiniteAdicRealization.Realization l
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
  [sourceUnits : ∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
  [targetUnits : ∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
    Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
  sourceAt : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source
  targetAt : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target
  sourcePresentation :
    (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source).IsEquivalence
  targetPresentation :
    (sectionFunctor l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target).IsEquivalence
  sourceFinite : ∀ E,
    FiniteNormalization l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source sourceAt E
  targetFinite : ∀ E,
    FiniteNormalization l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target targetAt E
  sourceHom : HomLaws l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber source sourceAt
  targetHom : HomLaws l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber target targetAt
  primeUnit : IsUnit (l : AlgebraicClosure k₀)
  comparison : Proper.Comparison l (NativeBaseChange.geometricMap k₀ p) source target
    (AlgebraicClosure k₀) primeUnit sourceAt targetAt
  sourceTensor : ProperSectionTensor k₀ l Z source sourceAt
  targetTensor : ProperSectionTensor k₀ l Y target targetAt
  balanced : NativeProjectionTensorComparison k₀ l p
  pull : nativeOpenPull k₀ l p ⋙ properSectionDerived k₀ l Z source ≅
    properSectionDerived k₀ l Y target ⋙
      ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient
  pushSheaf : lowerStar k₀ l p ⋙ properSectionForget k₀ l Y target ≅
    properSectionForget k₀ l Z source ⋙
      ContinuousRational.DirectImage.modulePush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient
  pushSections : ∀ M V x, HEq ((pushSheaf.hom.app M).val.app V x) x
  push : (lowerStar k₀ l p).rightDerivedFunctor ⋙ properSectionDerived k₀ l Y target ≅
    properSectionDerived k₀ l Z source ⋙
      ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient
  injective : ∀ I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ,
    I.IsKInjective → CochainComplex.IsKInjective
      ((properSectionCochain k₀ l Z source).obj I)
  pushRepresentative : ∀ (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
      (_hI : I.IsKInjective),
    (properSectionDerived k₀ l Y target).map (properNativePushUnit k₀ l p I) ≫
      push.hom.app (DerivedCategory.Q.obj I) ≫
      (ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
          ((properSectionFactors k₀ l Z source).hom.app I) =
    (properSectionFactors k₀ l Y target).hom.app
        (((lowerStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((properPushSheafCochain k₀ l p source target comparison.operations pushSheaf).hom.app I) ≫
      ContinuousRational.DirectImage.pushUnit (NativeBaseChange.geometricMap k₀ p)
        comparison.operations.coefficient
        ((properSectionCochain k₀ l Z source).obj I)
  counit : ∀ A,
    (properSectionDerived k₀ l Z source).map
        ((derivedUpperStarLowerStarAdjunction k₀ l p).counit.app A) =
      pull.hom.app ((lowerStar k₀ l p).rightDerivedFunctor.obj A) ≫
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
          (push.hom.app A) ≫
        comparison.operations.adjunction.counit.app
          ((properSectionDerived k₀ l Z source).obj A)
  pullTensor : ∀ M N,
    (properSectionDerived k₀ l Z source).map (balanced.mu.hom.app (M, N)) ≫
      sourceTensor.tensor.hom.app
        ((nativeOpenPull k₀ l p).obj M, (nativeOpenPull k₀ l p).obj N) ≫
      sourceAt.closed.tensor.map (Prod.mkHom (pull.hom.app M) (pull.hom.app N)) =
    pull.hom.app ((nativeDerivedTensor k₀ l Y).obj (M, N)) ≫
      (ContinuousRational.derivedPull
        (NativeBaseChange.geometricMap k₀ p) comparison.operations.coefficient).map
          (targetTensor.tensor.hom.app (M, N)) ≫
      comparison.tensor.tensor.hom.app
        ((properSectionDerived k₀ l Y target).obj M,
          (properSectionDerived k₀ l Y target).obj N)

omit [Fact (ringChar k₀ ≠ l)] [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] in
private theorem properSectionCochain_isKInjective
    (R : LocallyFiniteAdicRealization.Realization l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hR : (sectionFunctor l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective ((properSectionCochain k₀ l Z R).obj I) := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let := hI
  let := R.commutative
  let : (sectionFunctor l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).Additive :=
    R.sectionsAdditive
  let : (sectionFunctor l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).IsEquivalence :=
    hR
  change CochainComplex.IsKInjective
    (((properSectionForget k₀ l Z R).mapHomologicalComplex (.up ℤ)).obj I)
  infer_instance

/-- The native and ordinary operations have compatible resolution models.
Source: Steps 1--4 of lem-sf-native-proper-projection-realization;
BS 6.8.14--6.8.15 and Stacks 070I, 08BJ, 07A4, 0G7E
(blueprint: lem-sf-native-proper-projection-models).

Proof: apply the proper-adjunction realization theorem to the geometric base
change of p and retain the source and target realization, finite normalization,
and Hom data of its family. The coefficient-ring comparison identifies both
coefficient maps with precomposition. Compose native forgetting with the section
presentation equivalences. The lifted sheaf adjunction and Frobenius mate give
pull and pushSheaf; on sections pushSheaf is the identity. Exact pullback and
exact forgetting preserve the required acyclicity. Equivariant K-injective
resolutions stay K-injective after forgetting; both pushforwards on such a
resolution are the same ordinary complex. The normalized fixed-pair derived
comparison gives push and pushRepresentative. Computing the derived counit on
that resolution gives counit, independently of the resolution.
For tensors use equivariant K-flat flat-term resolutions. On sheaves the balanced
map sends b tensor (x tensor y) to (b tensor x) tensor (1 tensor y); its inverse
multiplies coefficients. These maps commute with Frobenius. Totalize with the
signed differential and retain each coproduct insertion. Ringed pullback preserves
K-flatness, and conservative forgetting detects acyclicity. Localization of these
maps gives balanced, sourceTensor and targetTensor, including their generator
and representative equations. The same insertion formulas give pullTensor.
None of these constructions uses invertibility of a projection mate. Zero inputs,
empty schemes and identity maps use exactly the same resolution formulas. -/
theorem native_proper_projection_models [IsProper p] :
    Nonempty (NativeProperProjectionModels k₀ l p) := by
  classical
  let : Fintype k₀ := Fintype.ofFinite k₀
  obtain ⟨n, hp, hn⟩ := FiniteField.card k₀ (ringChar k₀)
  let D : FiniteFieldDatum.{u} :=
    { p := ringChar k₀, a := n, q := Nat.card k₀, prime := hp
      exponent_pos := n.pos
      cardinality_eq := by simpa only [Nat.card_eq_fintype_card] using hn
      k₀ := k₀, card_base := rfl, k := AlgebraicClosure k₀ }
  have hl : l ≠ D.p := Ne.symm (Fact.out : ringChar k₀ ≠ l)
  let Zg : GeometricSpace D :=
    { base := Over.mk (Z ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      separated := by
        change IsSeparated (pullback.snd (Z ↘ Spec (CommRingCat.of k₀))
          (Scheme.specAlgebraicClosure k₀).hom)
        infer_instance
      finiteType := by
        change LocallyOfFiniteType (pullback.snd (Z ↘ Spec (CommRingCat.of k₀))
          (Scheme.specAlgebraicClosure k₀).hom)
        infer_instance
      quasiCompact := by
        change QuasiCompact (pullback.snd (Z ↘ Spec (CommRingCat.of k₀))
          (Scheme.specAlgebraicClosure k₀).hom)
        infer_instance }
  let Yg : GeometricSpace D :=
    { base := Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      separated := by
        change IsSeparated (pullback.snd (Y ↘ Spec (CommRingCat.of k₀))
          (Scheme.specAlgebraicClosure k₀).hom)
        infer_instance
      finiteType := by
        change LocallyOfFiniteType (pullback.snd (Y ↘ Spec (CommRingCat.of k₀))
          (Scheme.specAlgebraicClosure k₀).hom)
        infer_instance
      quasiCompact := by
        change QuasiCompact (pullback.snd (Y ↘ Spec (CommRingCat.of k₀))
          (Scheme.specAlgebraicClosure k₀).hom)
        infer_instance }
  let pg : Zg.base ⟶ Yg.base := Over.homMk (NativeBaseChange.geometricMap k₀ p)
    (Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure p
      (comp_over p (Spec (CommRingCat.of k₀))))
  have hpg : IsProper pg.left := by
    change IsProper (NativeBaseChange.geometricMap k₀ p)
    exact Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
      (P := @IsProper) p (comp_over p (Spec (CommRingCat.of k₀))) inferInstance
  obtain ⟨F, hF⟩ := Proper.adic_proper_adjunction_realization D l hl
  obtain ⟨C⟩ := hF Zg Yg pg hpg
  let := (F.data Zg).units
  let := (F.data Yg).units
  change Proper.Comparison l (NativeBaseChange.geometricMap k₀ p)
    (F.data Zg).realization (F.data Yg).realization (AlgebraicClosure k₀)
    (finiteFieldDatumPrimeUnit D l hl) (F.data Zg).tensor (F.data Yg).tensor at C
  obtain ⟨N⟩ := native_proper_section_adjunction_models k₀ l p
    (F.data Zg).realization (F.data Yg).realization C.operations
    (F.data Zg).presentation (F.data Yg).presentation
  obtain ⟨TZ, TY, balanced, hTensor⟩ := native_proper_section_tensor_models_legacy k₀ l p
    (F.data Zg).realization (F.data Yg).realization C.operations
    (F.data Zg).tensor (F.data Yg).tensor C.tensor N
    (F.data Zg).presentation (F.data Yg).presentation
  refine ⟨{
    source := (F.data Zg).realization
    target := (F.data Yg).realization
    sourceUnits := (F.data Zg).units
    targetUnits := (F.data Yg).units
    sourceAt := (F.data Zg).tensor
    targetAt := (F.data Yg).tensor
    sourcePresentation := (F.data Zg).presentation
    targetPresentation := (F.data Yg).presentation
    sourceFinite := (F.data Zg).finite
    targetFinite := (F.data Yg).finite
    sourceHom := (F.data Zg).hom
    targetHom := (F.data Yg).hom
    primeUnit := finiteFieldDatumPrimeUnit D l hl
    comparison := C
    sourceTensor := TZ
    targetTensor := TY
    balanced := balanced
    pull := N.pull
    pushSheaf := N.pushSheaf
    pushSections := N.pushSections
    push := N.push
    injective := ?_
    pushRepresentative := N.pushRepresentative
    counit := N.counit
    pullTensor := hTensor }⟩
  exact properSectionCochain_isKInjective k₀ l (F.data Zg).realization
    (F.data Zg).presentation

end AlgebraicGeometry.ProEtaleWeilSheaf
