/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.AdicPunctualWeights
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorCoproduct
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralPointTransportTowerPowers
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.Paper.WeilPullbackLocalFrobenius
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.TraceFormula.PointTransportComposition

/-! # Constant extension and the two constructible Weil hearts

Source: Deligne, Weil II, (1.1.7)--(1.1.10), pp. 150--152; blueprint
main-20261015, thm-zl-real-mixed-by-curves, proof paragraphs 1 and 5
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)

/-- The fixed subfield k_m has q^m elements and the same algebraic closure k.
Source: Deligne, Weil II, p. 152, change of finite base field
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the unique-subfield theorem gives cardinality q^m, which is nonzero,
so the subfield is finite. The closure k is algebraically closed and algebraic
also over this intermediate finite field, hence is its algebraic closure. -/
theorem constantExtensionField_properties :
    Finite (D.extensionSubfield m hm) ∧
      Nat.card (D.extensionSubfield m hm) = D.q ^ m ∧
      IsAlgClosure (D.extensionSubfield m hm) D.k := by
  sorry

/-- The new finite base remains the actual subfield of the fixed closure.
Source: Deligne, Weil II, p. 152
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionDatum : FiniteFieldDatum.{u} where
  p := D.p
  a := D.a * m
  q := D.q ^ m
  prime := D.prime
  exponent_pos := le_trans hm (Nat.le_mul_of_pos_left m D.exponent_pos)
  cardinality_eq := D.cardinality_eq ▸ (pow_mul D.p D.a m).symm
  k₀ := D.extensionSubfield m hm
  finite_base := (constantExtensionField_properties D m hm).1
  card_base := (constantExtensionField_properties D m hm).2.1
  k := D.k
  isAlgClosure := (constantExtensionField_properties D m hm).2.2

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]

/-- X_(0,m) as a k_m-scheme, the actual finite constant base change.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionModel : Over (Spec (.of (D.extensionSubfield m hm))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀

/-- The same scheme regarded over k_0, before finite pushforward.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionOriginalModel : Over (Spec (.of D.k₀)) :=
  Over.mk ((constantExtensionModel D m hm X₀).hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))

/-- Finite type of the base change and of its restriction to k_0.
Source: blueprint finite constant extension, parts (a)--(b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: base change preserves finite type. The finite field extension is finite,
hence finite type and quasi-compact. Composition gives the k_0 assertions. -/
theorem constantExtensionModel_properties :
    LocallyOfFiniteType (constantExtensionModel D m hm X₀).hom ∧
      QuasiCompact (constantExtensionModel D m hm X₀).hom ∧
      LocallyOfFiniteType (constantExtensionOriginalModel D m hm X₀).hom ∧
      QuasiCompact (constantExtensionOriginalModel D m hm X₀).hom := by
  sorry

/-- Finite-type structure over k_m, inherited from base change.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
instance constantExtensionModel_lft :
    LocallyOfFiniteType (constantExtensionModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).1

/-- Quasi-compact structure over k_m, inherited from base change.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
instance constantExtensionModel_qc :
    QuasiCompact (constantExtensionModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).2.1

/-- Finite type after restriction of the finite base field.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
instance constantExtensionOriginalModel_lft :
    LocallyOfFiniteType (constantExtensionOriginalModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).2.2.1

/-- Quasi-compactness after restriction of the finite base field.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
instance constantExtensionOriginalModel_qc :
    QuasiCompact (constantExtensionOriginalModel D m hm X₀).hom :=
  (constantExtensionModel_properties D m hm X₀).2.2.2

/-- The actual projection g_m, as a morphism over the original base field.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionProjection : constantExtensionOriginalModel D m hm X₀ ⟶ X₀ :=
  Over.homMk (pullback.fst X₀.hom
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))) pullback.condition

/-- Compatibility needed for the canonical sheet inclusion into the k_0-geometric fibre.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the inclusion k_m into k composed with extensionEmbedding is algebraMap.
Apply Spec and the defining pullback projection equation. -/
theorem constantExtensionSheet_compatible :
    pullback.fst (constantExtensionModel D m hm X₀).hom
        (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
        (constantExtensionOriginalModel D m hm X₀).hom =
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  sorry

/-- The distinguished sheet for the given inclusion k_m into k, constructed by a lift.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionSheet :
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).left ⟶
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left :=
  pullback.lift
    (pullback.fst (constantExtensionModel D m hm X₀).hom
      (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)))
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).hom
    (constantExtensionSheet_compatible D m hm X₀)

/-- The distinguished sheet maps isomorphically onto the original geometric fibre.
Source: blueprint parts (a)--(b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: associativity of base change identifies the composite with
(X_0 times_{k_0} k_m) times_{k_m} k to X_0 times_{k_0} k.
Its two projections are the canonical ones; the pullback universal property
constructs its inverse and proves both inverse identities. -/
theorem constantExtensionFiberMap_isIso :
    IsIso (constantExtensionSheet D m hm X₀ ≫
      zlFiberMap D (constantExtensionProjection D m hm X₀)) := by
  sorry

/-- The canonical associativity identification; no geometric scheme is replaced silently.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionFiberIso :
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).left ≅ (D.geometricFiber X₀).left :=
  letI := constantExtensionFiberMap_isIso D m hm X₀
  asIso (constantExtensionSheet D m hm X₀ ≫
    zlFiberMap D (constantExtensionProjection D m hm X₀))

/-- The q^m-Frobenius returns to the distinguished sheet.
Source: Deligne, Weil II (1.1.7)--(1.1.10), blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the geometric q^m automorphism is gamma^m on the same closure.
The latter fixes k_m. Comparing both projections of the defining fibre products
proves the sheet-return identity. -/
theorem constantExtensionSheet_return :
    ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫ constantExtensionSheet D m hm X₀ =
      constantExtensionSheet D m hm X₀ ≫
        localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m - 1) := by
  sorry

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Pullback along the distinguished sheet, with the recorded coefficient functor.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionSheetPull :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (constantExtensionSheet D m hm X₀)
    (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀))
    (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))

/-- Iterated Weil map with the prescribed integral-normalized composition comparisons.
Source: blueprint part (a), theta^[m]
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionWeilIterate
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : sfCommonStageWeilComplex D l hl Y₀ Ω) :
    (n : ℕ) →
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier ≅
      K.carrier
  | 0 => K.str
  | n + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    (zlPullComp l Ω (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (D.geometricFrobenius Y₀).hom).app K.carrier ≪≫
      (commonStageDerivedPullback l Ω
        (localPositivePower (D.geometricFrobenius Y₀).hom n)).mapIso K.str ≪≫
      constantExtensionWeilIterate Y₀ K n

/-- The return comparison is built from the specified pullback compositor and sheet equality.
Source: blueprint part (b), return around the cycle
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionReturnComparison
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left) :
    (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω).obj
        ((constantExtensionSheetPull D m hm X₀ l hl Ω).obj M) ≅
      (constantExtensionSheetPull D m hm X₀ l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower
            (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m - 1))
          (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))
          (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))).obj M) :=
  letI := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  letI := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  ((zlPullComp l Ω
    ((constantExtensionDatum D m hm).geometricFrobenius
      (constantExtensionModel D m hm X₀)).hom (constantExtensionSheet D m hm X₀)).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj M)
      (constantExtensionSheet_return D m hm X₀)) ≪≫
    (zlPullComp l Ω (constantExtensionSheet D m hm X₀)
      (localPositivePower
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m - 1))).app M

/-- Forgetting the Weil structure and heart proof, with the recorded faithful functor.
Source: blueprint parts (a)--(b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionHeartForget
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :=
  ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl Y₀ Ω)).ι ⋙ sfCommonStageWeilForget D l hl Y₀ Ω

/-- The sheet restriction is characterized on every underlying arrow and its return map.
Naturality of alpha specifies the underlying functor, and the displayed equation fixes
its Weil structure to the actual m-fold iterate, using the prescribed comparisons.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def ConstantExtensionSheetSpec
    (T : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω) : Prop :=
  ∃ α : T ⋙ constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀) ≅
      constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀) ⋙
        constantExtensionSheetPull D m hm X₀ l hl Ω,
    ∀ N,
      (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω).map (α.hom.app N) ≫
        (constantExtensionReturnComparison D m hm X₀ l hl Ω N.obj.carrier).hom ≫
        (constantExtensionSheetPull D m hm X₀ l hl Ω).map
          (constantExtensionWeilIterate D l hl Ω
            (constantExtensionOriginalModel D m hm X₀) N.obj (m - 1)).hom =
        (T.obj N).obj.str.hom ≫ α.hom.app N

/-- The residue degree uses the actual field map induced by g_m, not its total degree.
Source: blueprint part (a), f=[kappa(z):kappa(x)]
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionResidueDegree
    (z : (constantExtensionModel D m hm X₀).left) : ℕ :=
  letI : Algebra
      (X₀.left.residueField ((constantExtensionProjection D m hm X₀).left z))
      ((constantExtensionModel D m hm X₀).left.residueField z) :=
    ((constantExtensionProjection D m hm X₀).left.residueFieldMap z).hom.toAlgebra
  Module.finrank (X₀.left.residueField ((constantExtensionProjection D m hm X₀).left z))
    ((constantExtensionModel D m hm X₀).left.residueField z)

/-- A closed point has closed image under the finite projection.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: g_m is finite, hence closed. The image of the one-point closed subset is closed. -/
theorem constantExtensionClosedImage_mem
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    (constantExtensionProjection D m hm X₀).left z.val ∈ closedPoints X₀.left := by
  sorry

/-- The closed image point with its inherited closedness proof.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionClosedImage
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    {x : X₀.left // x ∈ closedPoints X₀.left} :=
  ⟨(constantExtensionProjection D m hm X₀).left z.val,
    constantExtensionClosedImage_mem D m hm X₀ z⟩

/-- Local-operator conjugacy on all finite Weil presentations after actual scalar extension.
The operators are exactly localClosedFrobeniusCohomology in degree zero. The assertion
quantifies over residue embeddings and presentations, so it makes no semisimplicity or
field-of-definition assumption. f=1 gives the two interpretations of the same point.
Source: blueprint parts (a)--(b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def ConstantExtensionLocalConjugacy
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (F : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (G : sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω)
    (x : {x : Y₀.left // x ∈ closedPoints Y₀.left})
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) (f : ℕ) : Prop :=
  ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (K' : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)),
    Nonempty (sfWeilStageObject D l hl Y₀ Ω L K ≅ F.obj) →
    Nonempty (sfWeilStageObject (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω L K' ≅ G.obj) →
    ∀ (ι : Y₀.left.residueField x.val →+* D.k)
      (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (ι' : (constantExtensionModel D m hm X₀).left.residueField z.val →+* D.k)
      (hι' : ι'.comp ((constantExtensionModel D m hm X₀).hom.residueFieldAlgebraMap z.val) =
        algebraMap (D.extensionSubfield m hm) D.k),
    ∃ e :
      (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) 0).obj
          (localPointComplex l _ D hl Y₀ K (localClosedPoint D Y₀ x ι hι))) ≅
      (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).obj
        ((DerivedCategory.coefficientFdCohomology
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) 0).obj
          (localPointComplex l _ (constantExtensionDatum D m hm) hl
            (constantExtensionModel D m hm X₀) K'
            (localClosedPoint (constantExtensionDatum D m hm)
              (constantExtensionModel D m hm X₀) z ι' hι'))),
      e.hom ≫ (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).map
          (localClosedFrobeniusCohomology l _ (constantExtensionDatum D m hm) hl
            (constantExtensionModel D m hm X₀) K' z ι' hι' 0) =
        ((End.of ((ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).map
          (localClosedFrobeniusCohomology l _ D hl Y₀ K x ι hι 0))) ^ f) ≫ e.hom

/-- The geometric sheets are the cyclic translates of the distinguished inclusion.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionCyclicSheet (i : Fin m) :
    (D.geometricFiber X₀).left ⟶
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left :=
  (constantExtensionFiberIso D m hm X₀).inv ≫ constantExtensionSheet D m hm X₀ ≫
    ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom

/-- The disjoint union of m clopen sheets, with cyclic geometric-Frobenius return.
Source: Deligne, Weil II, p. 152; blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the Galois tensor splitting k_m tensor_{k_0} k = product_sigma k gives
exactly m open-and-closed components. Geometric Frobenius permutes embeddings
cyclically. The sheet for the fixed inclusion is the pullback lift already defined;
its translates give the coproduct cocone. The mth power returns with gamma^m,
which is the geometric Frobenius for the k_m-model. Compare projections to obtain
the final equality. This includes the empty scheme and m=1. -/
theorem constantExtensionCyclicSheets :
    (∀ i : Fin m, IsOpenImmersion (constantExtensionCyclicSheet D m hm X₀ i) ∧
      IsClosedImmersion (constantExtensionCyclicSheet D m hm X₀ i)) ∧
    Nonempty (IsColimit (Cofan.mk
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left
      (constantExtensionCyclicSheet D m hm X₀))) ∧
    (constantExtensionFiberIso D m hm X₀).inv ≫ constantExtensionSheet D m hm X₀ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ m).hom =
      ((D.geometricFrobenius X₀) ^ m).hom ≫
        (constantExtensionFiberIso D m hm X₀).inv ≫ constantExtensionSheet D m hm X₀ := by
  sorry

/-- The canonical restriction followed by the inverse equivalence is the k_0-Weil pullback.
This is a functor identity by construction; its return map is specified by SheetSpec.
Source: blueprint final clause of (b), before applying g_(m,*).
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionRestriction
    (e : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ≌
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω) :=
  zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀) ⋙ e.functor

/-- The canonical fibre isomorphism intertwines the new Frobenius with the mth power.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the fibre isomorphism is the associativity map of base change, and geometric
Frobenius acts only on the closure factor. Over k_m its coefficient action is gamma^m.
Comparing the two projections gives the equality, also when the model is empty. -/
theorem constantExtensionFiber_return :
    ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫
        (constantExtensionFiberIso D m hm X₀).hom =
      (constantExtensionFiberIso D m hm X₀).hom ≫
        localPositivePower (D.geometricFrobenius X₀).hom (m - 1) := by
  sorry

/-- Canonical pullback along the actual geometric-fibre identification.
Source: blueprint part (a), unchanged underlying object
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionFiberPull :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (constantExtensionFiberIso D m hm X₀).hom
    (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀)) (sfWeilPrimeInvertible D l hl X₀)

/-- The normalized return comparison for restriction to k_m on the original geometric fibre.
Source: blueprint part (a), theta^[m]
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionRestrictionComparison
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω).obj
        ((constantExtensionFiberPull D m hm X₀ l hl Ω).obj M) ≅
      (constantExtensionFiberPull D m hm X₀ l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (D.geometricFrobenius X₀).hom (m - 1))
          (sfWeilPrimeInvertible D l hl X₀) (sfWeilPrimeInvertible D l hl X₀)).obj M) :=
  letI := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  letI := sfWeilPrimeInvertible D l hl X₀
  ((zlPullComp l Ω
    ((constantExtensionDatum D m hm).geometricFrobenius
      (constantExtensionModel D m hm X₀)).hom
      (constantExtensionFiberIso D m hm X₀).hom).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj M)
      (constantExtensionFiber_return D m hm X₀)) ≪≫
    (zlPullComp l Ω (constantExtensionFiberIso D m hm X₀).hom
      (localPositivePower (D.geometricFrobenius X₀).hom (m - 1))).app M

/-- On the canonically identified fibre the carrier is unchanged and theta becomes theta^[m].
The natural isomorphism also specifies the action on every morphism.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def ConstantExtensionRestrictionSpec
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω) : Prop :=
  ∃ α : R ⋙ constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀) ≅
      constantExtensionHeartForget D l hl Ω X₀ ⋙ constantExtensionFiberPull D m hm X₀ l hl Ω,
    ∀ F,
      (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω).map (α.hom.app F) ≫
        (constantExtensionRestrictionComparison D m hm X₀ l hl Ω F.obj.carrier).hom ≫
        (constantExtensionFiberPull D m hm X₀ l hl Ω).map
          (constantExtensionWeilIterate D l hl Ω X₀ F.obj (m - 1)).hom =
        (R.obj F).obj.str.hom ≫ α.hom.app F

/-- Pullback at a cyclic translate, in the coordinates of the k_m-geometric fibre.
In these semilinear sheet coordinates the normalized inverse has the same carrier
on each sheet; in k-linear coordinates these are the successive Frobenius translates.
Source: blueprint part (b), description of the inverse
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionSheetPullAt (i : Fin m) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _
    (constantExtensionSheet D m hm X₀ ≫
      ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom)
    (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀))
    (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))

include hsep in
/-- Constant extension on constructible Weil hearts, with its canonical return map,
residue-degree local powers, exact cyclic-sheet equivalence, and weight filtrations.
Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152; blueprint main-20261015,
thm-zl-real-mixed-by-curves, proof paragraphs 1 and 5
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).

Proof:
1. Split k_m tensor_{k_0} k as the product indexed by its m embeddings. Base change
splits the geometric k_0-scheme into the clopen sheets of constantExtensionCyclicSheets.
The mth power of geometric Frobenius returns to sheet zero as q^m-Frobenius.
2. The finite-clopen coefficient equivalence and exact inverse image under sheet
isomorphisms give componentwise equivalences on integral, rational, and common-stage
constructible categories. Scalar localization retains the normalized compositors.
3. In semilinear sheet coordinates a Weil object is a cycle of isomorphisms
A_(i+1) to A_i, with the final arrow P^m A_0 to A_(m-1). Send it to A_0 with the
composite return arrow. Conversely put A on every sheet, identities on intermediate
arrows and the given q^m-Weil map on the final arrow, then glue the clopen pieces.
4. The two composites are naturally isomorphic to the identity: normalize a cycle
by the partial products of its transition arrows. The commuting squares of a Weil
morphism make these products natural. For m=1 there are no intermediate arrows.
5. Kernels and cokernels of Weil morphisms are computed on carriers, because
Frobenius is an exact equivalence of the underlying constructible heart. Restriction
and gluing are componentwise exact. Thus the equivalence and its inverse are exact,
identify all subobjects and quotients, and carry arbitrary finite filtrations.
6. Apply this equivalence to the actual k_0-Weil pullback along g_m. Associativity of
base change gives the original carrier, and the composite return is theta^[m]. Its
canonical inverse comparison recovers precisely this pullback before pushforward.
7. At a closed point of degree d, tensoring its residue field with k_m splits into
gcd(d,m) fields of degree m/gcd(d,m) over the original residue field. Thus f has the
stated value and #kappa(z)=#kappa(x)^f, including nonsplit residue extensions.
8. Use the specified point transports and their composition laws. The return path
at z groups f consecutive return paths at x, giving conjugacy with F_x^f. In the
two interpretations of z the absolute residue return is identical, giving f=1.
Check this at finite coefficient stages and extend scalars; common-stage descent
and independence of residue embeddings give exactly LocalConjugacy below.
9. Conjugate local operators have the same eigenvalues and the same absolute
residue size. Consequently the exact equivalence preserves punctual purity of
every weight and pure quotients. Apply it and its inverse to finite filtrations
to obtain mixedness with any specified bound. Zero objects have length-zero
filtrations; Jordan blocks are allowed throughout. No lissity is used. -/
theorem constantExtensionWeilHeartEquivalence (iota : Ω ≃+* ℂ) :
    ∃ e : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ≌
        sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω,
      ConstantExtensionSheetSpec D m hm X₀ l hl Ω e.functor ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω
        (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      PreservesFiniteLimits (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      PreservesFiniteColimits (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      Nonempty (constantExtensionRestriction D m hm X₀ l hl Ω e ⋙ e.inverse ≅
        zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)) ∧
      (∀ (A : sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω) (i : Fin m),
        Nonempty ((constantExtensionSheetPullAt D m hm X₀ l hl Ω i).obj
          (e.inverse.obj A).obj.carrier ≅ A.obj.carrier)) ∧
      (∀ (z : {z : (constantExtensionModel D m hm X₀).left //
            z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
        constantExtensionResidueDegree D m hm X₀ z.val =
          m / Nat.gcd (localClosedPointDegree D X₀
            (constantExtensionClosedImage D m hm X₀ z)) m ∧
        Nat.card ((constantExtensionModel D m hm X₀).left.residueField z.val) =
          Nat.card (X₀.left.residueField
            (constantExtensionClosedImage D m hm X₀ z).val) ^
              constantExtensionResidueDegree D m hm X₀ z.val ∧
        (∀ F : sfCommonStageWeilSheaf D l hl X₀ Ω,
          ConstantExtensionLocalConjugacy D m hm X₀ l hl Ω X₀ F
            ((constantExtensionRestriction D m hm X₀ l hl Ω e).obj F)
            (constantExtensionClosedImage D m hm X₀ z) z
            (constantExtensionResidueDegree D m hm X₀ z.val))) ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω)
        (z : {z : (constantExtensionModel D m hm X₀).left //
          z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
        ConstantExtensionLocalConjugacy D m hm X₀ l hl Ω
          (constantExtensionOriginalModel D m hm X₀) N (e.functor.obj N) z z 1) ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
        (w : ℝ),
        (SfIsPunctuallyPureOfWeight D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            iota N w ↔
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (e.functor.obj N) w) ∧
        (SfIsMixedOfWeightsAtMost D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            iota N w ↔
          SfIsMixedOfWeightsAtMost (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (e.functor.obj N) w)) := by
  sorry

end WeilConjectures
