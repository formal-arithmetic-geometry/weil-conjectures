/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeSystemRestriction.FiniteFreeSystemRestrictionData
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaCoherence
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization

/-! # Scalar mates and projection maps on whole coefficient systems

Source: blueprint coefficient comparison, finite-free compact-support paragraph,
proof Steps 1--7 of the agent-formulated coherent-system obligation
(blueprint: def-coef-system-scalar-projection-data).

The projection uses the actual closed derived tensor and the pinned semilinear
Geometry.tensorPullback, followed by coefficient pullback and counit tensor identity.
The same representative-normalized U T / tensor isomorphism occurs in its equality
with the restricted scalar comparison. Finite scalar and tensor words are constructed
independently from the finite adjunctions. All equalities precede inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.leftAdjoint
  HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

attribute [local irreducible] AlgebraicGeometry.ProEtale.SemilinearProperOpen.R
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.J

universe u c v r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open WeilConjectures.SemilinearSections WeilConjectures.FiniteFreeSystemRestriction
namespace WeilConjectures.SystemScalarProjection

section TensorNormalization

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) {R S : Sheaf J CommRingCat.{max c v r}}
  (φ : R ⟶ S) (a : ScalarData.{c, v, max c v r} φ)
  (closed : WeilConjectures.SemilinearSections.Closed.{c, v, r} J R)
  (models : WeilConjectures.SemilinearSections.Models.{c, v, r} J R closed)

end TensorNormalization

variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L) {K : FiniteFieldDatum.{u}} {d : ℕ}
  {b : Fin d → Padic.coefficientExtensionIntegers l L} {ramification : ℕ}
  (s : Assertions l E L i K d b ramification)

/-- The actual scalar extension supplied by the finite-free restriction theorem.
Source: proof Step 1 (blueprint: lem-coef-system-scalar-projection-identification). -/
abbrev T (X : Spaces K) := (s.scalars X).scalar.T

/-- Tensor with B in its canonical scalar-extension presentation.
Source: proof Steps 1--2 (blueprint: lem-coef-system-scalar-projection-identification). -/
abbrev Q (X : Spaces K) := T l E L i s X ⋙ U l E L i X.val.left

/-- Pullback/scalar extension, conjugate to the section-normalized restriction square.
Source: the definition of a_p in the node
(blueprint: lem-coef-system-scalar-projection-identification). -/
def scalarPull (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left) :
    T l E L i s Y ⋙ P (B l E L i) (bTransition l E L i) f ≅
      P (A l E) (aTransition l E) f ⋙ T l E L i s X :=
  ((conjugateIsoEquiv
    ((s.scalars Y).scalar.adjunction.comp (adj (B l E L i) (bTransition l E L i) f))
    ((adj (A l E) (aTransition l E) f).comp (s.scalars X).scalar.adjunction)).symm
      (s.geometry.pushIso l E L i X Y f)).symm

/-- The proper coefficient map is the B-geometric transpose of the extended A-counit.
Source: the node's a_p formula
(blueprint: lem-coef-system-scalar-projection-identification). -/
def properScalar (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left)
    (H : Derived (A l E) (aTransition l E) X.val.left) :
    (T l E L i s Y).obj ((R (A l E) (aTransition l E) f).obj H) ⟶
      (R (B l E L i) (bTransition l E L i) f).obj ((T l E L i s X).obj H) :=
  (adj (B l E L i) (bTransition l E L i) f).homEquiv _ _
    ((scalarPull l E L i s X Y f).hom.app _ ≫
      (T l E L i s X).map ((adj (A l E) (aTransition l E) f).counit.app H))

/-- The open balancing isomorphism is conjugate to the actual restriction/pullback square.
Its ordinary normalization is x tensor b on the open and zero on the complement.
Source: proof Step 3 and lem-sf-open-tensor-normalization
(blueprint: lem-coef-system-scalar-projection-identification). -/
def openScalar (X Y : Spaces K) (j : X.val.left ⟶ Y.val.left) [IsOpenImmersion j] :
    J (A l E) (aTransition l E) j ⋙ T l E L i s Y ≅
      T l E L i s X ⋙ J (B l E L i) (bTransition l E L i) j :=
  (conjugateIsoEquiv
    ((s.scalars X).scalar.adjunction.comp (jAdj (B l E L i) (bTransition l E L i) j))
    ((jAdj (A l E) (aTransition l E) j).comp (s.scalars Y).scalar.adjunction)).symm
      ((s.geometry.ordinary X Y j).derivedPull l E L i)

/-- The ambient compactification scheme as a separated finite-type scheme over k.
Source: geometric setting (blueprint: lem-coef-system-scalar-projection-identification). -/
def ambient (Y : Spaces K) {X : Scheme.{u}} {f : X ⟶ Y.val.left}
    (c : Compactification f) : Spaces K :=
  haveI := Y.property.1
  haveI := Y.property.2.1
  haveI := Y.property.2.2
  ⟨Over.mk (c.g ≫ Y.val.hom),
    (by change IsSeparated (c.g ≫ Y.val.hom); infer_instance),
    (by change LocallyOfFiniteType (c.g ≫ Y.val.hom); infer_instance),
    (by change QuasiCompact (c.g ≫ Y.val.hom); infer_instance)⟩

/-- The specified proper-then-open scalar comparison c^c, on entire systems.
Source: the node's displayed definition of c^c
(blueprint: lem-coef-system-scalar-projection-identification). -/
def comparison (X Y : Spaces K) {f : X.val.left ⟶ Y.val.left} (c : Compactification f)
    (M : Derived (A l E) (aTransition l E) X.val.left) :
    (T l E L i s Y).obj ((compact (A l E) (aTransition l E) c.i c.g).obj M) ⟶
      (compact (B l E L i) (bTransition l E L i) c.i c.g).obj
        ((T l E L i s X).obj M) :=
  properScalar l E L i s (ambient Y c) Y c.g ((J (A l E) (aTransition l E) c.i).obj M) ≫
    (R (B l E L i) (bTransition l E L i) c.g).map
      ((openScalar l E L i s X (ambient Y c) c.i).hom.app M)

attribute [local irreducible] comparison

/-- Realization of the published semilinear geometry on the fixed constant towers.
The tensorator and its finite versions are the actual Geometry fields, with ordinary
pullback, target calculus and finite adjunctions pinned to the published operations.
Source: lem-coef-semilinear-derived-sections, proof Step 2
(blueprint: lem-coef-system-scalar-projection-identification). -/
structure PinnedGeometry (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left) where
  geometry : WeilConjectures.SemilinearSections.Geometry.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y.val.left) (coefficients (A l E) Y.val.left)
    (transition (A l E) (aTransition l E) Y.val.left) (s.scalars Y).lower
    (Scheme.ProEt.topology X.val.left)
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
    (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
    (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))
  coefficients_eq : geometry.coefficients = coefficients (A l E) X.val.left
  transitions_eq : ∀ n : ℕ,
    HEq (geometry.coefficientTransition n) (transition (A l E) (aTransition l E) X.val.left n)
  target_eq : HEq geometry.target (s.scalars X).lower
  pull_eq : HEq geometry.pull (pull (A l E) (aTransition l E) f)
  mu : (s.scalars Y).lower.closed.tensor ⋙ P (A l E) (aTransition l E) f ≅
    ((P (A l E) (aTransition l E) f).prod (P (A l E) (aTransition l E) f)) ⋙
      (s.scalars X).lower.closed.tensor
  mu_eq : HEq mu geometry.tensorPullback
  levelMu : ∀ n : ℕ,
    ((s.scalars Y).lower.levelClosed n).tensor ⋙
        (ProEtale.StrictTower.modulePullback (A l E n) f).mapDerivedCategory ≅
      ((ProEtale.StrictTower.modulePullback (A l E n) f).mapDerivedCategory.prod
        (ProEtale.StrictTower.modulePullback (A l E n) f).mapDerivedCategory) ⋙
        ((s.scalars X).lower.levelClosed n).tensor
  levelMu_eq : ∀ n : ℕ, HEq (levelMu n) (geometry.levelTensorPullback n)
  levelPull_eq : ∀ n : ℕ,
    HEq (geometry.inverseImage n).modules (ProEtale.StrictTower.modulePullback (A l E n) f)
  levelAdj_eq : ∀ n : ℕ,
    HEq (geometry.derivedLevelAdjunction n) (ProEtale.VaryingRing.levelAdj (A l E) f n)

/-- The pinned geometric calculus, for every arrow used in a compactification.
Source: proof Steps 2--3 (blueprint: lem-coef-system-scalar-projection-identification). -/
abbrev GeometryFamily := ∀ (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left),
  PinnedGeometry l E L i s X Y f

/-- Pullback of the actual restricted coefficient system, localized from its
section-normalized ordinary adjunct in the restriction lemma.
Source: lem-coef-finite-free-system-restriction, proof Step 2
(blueprint: lem-coef-system-scalar-projection-identification). -/
def coefficientPull (X Y : Spaces K) (f : X.val.left ⟶ Y.val.left) :
    (P (A l E) (aTransition l E) f).obj (coefficientObject l E L i Y.val.left) ≅
      coefficientObject l E L i X.val.left := by
  letI := s.geometry.coefficient_pull_isIso X Y f
  exact ((pull (A l E) (aTransition l E) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (asIso (((ordinaryAdj (A l E) (aTransition l E) f).homEquiv _ _).symm
        (s.geometry.coefficient_push X Y f)))

/-- The specified proper projection: pinned geometric tensorator, coefficient
pullback, counit tensor identity, then A-geometric transpose.
Source: def-exchange-projection, proof Step 2
(blueprint: lem-coef-system-scalar-projection-identification). -/
def properProjection (g : GeometryFamily l E L i s) (X Y : Spaces K)
    (f : X.val.left ⟶ Y.val.left) (H : Derived (A l E) (aTransition l E) X.val.left) :=
  (adj (A l E) (aTransition l E) f).homEquiv _ _
    ((g X Y f).mu.hom.app
        ((R (A l E) (aTransition l E) f).obj H, coefficientObject l E L i Y.val.left) ≫
      (s.scalars X).lower.closed.tensor.map
        (Prod.mkHom ((adj (A l E) (aTransition l E) f).counit.app H)
          (coefficientPull l E L i s X Y f).hom))

/-- The inverse system open tensor comparison, normalized by the open unit and the
pinned tensorator. This is gamma_inverse of lem-sf-open-tensor-normalization, with
coefficient pullback inserted; it does not use the scalar-extension comparison.
Source: Stacks 0E8I, proof Step 3
(blueprint: lem-coef-system-scalar-projection-identification). -/
def openTensorInv (g : GeometryFamily l E L i s) (X Y : Spaces K)
    (j : X.val.left ⟶ Y.val.left) [IsOpenImmersion j]
    (M : Derived (A l E) (aTransition l E) X.val.left) :=
  ((jAdj (A l E) (aTransition l E) j).homEquiv _ _).symm
    ((s.scalars X).lower.closed.tensor.map
      (Prod.mkHom ((jAdj (A l E) (aTransition l E) j).unit.app M)
        (coefficientPull l E L i s X Y j).inv) ≫
      (g X Y j).mu.inv.app
        ((J (A l E) (aTransition l E) j).obj M, coefficientObject l E L i Y.val.left))

/-- The actual strict-system PF word on the recorded derived tensors: proper counit
projection followed by the open tensor comparison. All maps precede evaluation.
Source: def-exchange-projection and lem-pur-system-level-projection-formula-coherence
(blueprint: lem-coef-system-scalar-projection-identification). -/
def projection (g : GeometryFamily l E L i s) (X Y : Spaces K)
    {f : X.val.left ⟶ Y.val.left} (c : Compactification f)
    (M : Derived (A l E) (aTransition l E) X.val.left) :=
  properProjection l E L i s g (ambient Y c) Y c.g
      ((J (A l E) (aTransition l E) c.i).obj M) ≫
    (R (A l E) (aTransition l E) c.g).map
      (SystemProjectionFormula.inverseOnDomain
        (openTensorInv l E L i s g X (ambient Y c) c.i M))

attribute [local irreducible] projection

attribute [local irreducible] commonComparison

/-- The actual positive-level evaluation, retaining the fixed coefficient action.
Source: lem-coef-semilinear-derived-sections
(blueprint: lem-coef-system-scalar-projection-identification). -/
abbrev level (C : ℕ → CommRingCat.{u + 1}) (t : ∀ n, C (n + 1) ⟶ C n)
    (X : Scheme.{u}) (n : ℕ) :=
  e.{u + 1, u, u + 1} (Scheme.ProEt.topology X) (coefficients C X) (transition C t X) n

/-- The finite-level scalar extension and the normalized adjunction evaluation diagrams.
The level geometric adjunctions are the published ordinary finite coefficient operations;
there is no arbitrary finite comparison map in this record. Each evaluation record is
pinned on its restriction/pullback side to the published comparison; unit and counit
compatibility then determine its other side, so no unit or sign twist is admitted.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
structure LevelData (X Y : Spaces K) {f : X.val.left ⟶ Y.val.left}
    (c : Compactification f) (n : ℕ) where
  scalar : ∀ W : Spaces K, ScalarData.{u + 1, u, u + 1} (sheafMap l E L i W.val.left n)
  scalarEvaluation : ∀ W : Spaces K,
    AdjunctionEvaluation
      (level (A l E) (aTransition l E) W.val.left n)
      (level (B l E L i) (bTransition l E L i) W.val.left n)
      (s.scalars W).scalar.adjunction (scalar W).adjunction
  properA : AdjunctionEvaluation
    (level (A l E) (aTransition l E) Y.val.left n)
    (level (A l E) (aTransition l E) c.Z n)
    (adj (A l E) (aTransition l E) c.g)
    (ProEtale.VaryingRing.levelAdj (A l E) c.g n)
  properB : AdjunctionEvaluation
    (level (B l E L i) (bTransition l E L i) Y.val.left n)
    (level (B l E L i) (bTransition l E L i) c.Z n)
    (adj (B l E L i) (bTransition l E L i) c.g)
    (ProEtale.VaryingRing.levelAdj (B l E L i) c.g n)
  openA : AdjunctionEvaluation
    (level (A l E) (aTransition l E) X.val.left n)
    (level (A l E) (aTransition l E) c.Z n)
    (jAdj (A l E) (aTransition l E) c.i)
    (ProEtale.VaryingRing.levelJAdj (A l E) c.i n)
  openB : AdjunctionEvaluation
    (level (B l E L i) (bTransition l E L i) X.val.left n)
    (level (B l E L i) (bTransition l E L i) c.Z n)
    (jAdj (B l E L i) (bTransition l E L i) c.i)
    (ProEtale.VaryingRing.levelJAdj (B l E L i) c.i n)
  /-- Restriction evaluation is the published identity-on-sections comparison. -/
  scalarEvaluation_right : ∀ W : Spaces K, (scalarEvaluation W).right =
    WeilConjectures.SemilinearSections.restrictionEvaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology W.val.left)
      (coefficients (A l E) W.val.left) (transition (A l E) (aTransition l E) W.val.left)
      (coefficients (B l E L i) W.val.left)
      (transition (B l E L i) (bTransition l E L i) W.val.left)
      (sheafMap l E L i W.val.left) (fun m ↦ by
        simpa only [sheafMap, AlgebraicGeometry.ProEtale.SemilinearProperOpen.transition,
          ← Functor.map_comp] using
          congrArg ((constantSheaf.{u, u + 1, u + 1, u + 2}
            (Scheme.ProEt.topology W.val.left) CommRingCat.{u + 1}).map)
            (levelMap_transition l E L i m)) n
  /-- Proper pullback evaluation is the published localized evaluation comparison. -/
  properA_left : HEq properA.left
    (ProEtale.VaryingRing.evalG (A l E) (aTransition l E) c.g n)
  properB_left : HEq properB.left
    (ProEtale.VaryingRing.evalG (B l E L i) (bTransition l E L i) c.g n)
  /-- Open restriction evaluation is the same published pullback comparison. -/
  openA_right : HEq openA.right
    (ProEtale.VaryingRing.evalG (A l E) (aTransition l E) c.i n)
  openB_right : HEq openB.right
    (ProEtale.VaryingRing.evalG (B l E L i) (bTransition l E L i) c.i n)

  tensor : ∀ W : Spaces K, TensorNormalization.{u + 1, u, u + 1}
    (Scheme.ProEt.topology W.val.left) (sheafMap l E L i W.val.left n) (scalar W)
    ((s.scalars W).lower.levelClosed n) ((s.scalars W).lower.levelTensorModels n)
  scalarSquare : ∀ (W Z : Spaces K) (f : W.val.left ⟶ Z.val.left),
    (ProEtale.StrictTower.constantRingIso (A l E n) f).hom ≫
        sheafMap l E L i W.val.left n =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (sheafMap l E L i Z.val.left n) ≫
        (ProEtale.StrictTower.constantRingIso (B l E L i n) f).hom
  coefficientPush : ∀ (W Z : Spaces K) (f : W.val.left ⟶ Z.val.left),
    restrictedUnit.{u + 1, u, u + 1} (Scheme.ProEt.topology Z.val.left)
        (sheafMap l E L i Z.val.left n) ⟶
      (ProEtale.StrictTower.moduleDirectImage (A l E n) f).obj
        (restrictedUnit.{u + 1, u, u + 1} (Scheme.ProEt.topology W.val.left)
          (sheafMap l E L i W.val.left n))
  coefficientSections : ∀ (W Z : Spaces K) (f : W.val.left ⟶ Z.val.left)
    (V : Z.val.left.ProEtᵒᵖ),
    HEq (fun x ↦ (coefficientPush W Z f).val.app V x)
      (fun x ↦ (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (B l E L i n)).hom.app V x)
  coefficientPull_isIso : ∀ (W Z : Spaces K) (f : W.val.left ⟶ Z.val.left),
    IsIso (((Scheme.proEtaleRingModuleAdjunction f
      (coefficients (A l E) Z.val.left n) (coefficients (A l E) W.val.left n)
      (ProEtale.StrictTower.constantRingIso (A l E n) f)).homEquiv _ _).symm
        (coefficientPush W Z f))

/-- Exact finite restriction at the actual A_n-to-B_n constant ring map.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
abbrev finiteU (W : Spaces K) (n : ℕ) :=
  resD.{u + 1, u, u + 1} (sheafMap l E L i W.val.left n)

/-- The actual finite coefficient system in degree zero, independently of evaluation.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
abbrev finiteCoefficient (W : Spaces K) (n : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (restrictedUnit.{u + 1, u, u + 1} (Scheme.ProEt.topology W.val.left)
      (sheafMap l E L i W.val.left n))

/-- The canonical finite restriction/pullback square, from constant coefficient maps.
Source: Stacks 0D6D, proof Step 3
(blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.restrictionPull {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (W Z : Spaces K) (h : W.val.left ⟶ Z.val.left) :=
  Scheme.proEtaleRingRestrictionDerivedPullback h
    (coefficients (A l E) Z.val.left n) (coefficients (B l E L i) Z.val.left n)
    (coefficients (A l E) W.val.left n) (coefficients (B l E L i) W.val.left n)
    (sheafMap l E L i Z.val.left n) (sheafMap l E L i W.val.left n)
    (ProEtale.StrictTower.constantRingIso (A l E n) h)
    (ProEtale.StrictTower.constantRingIso (B l E L i n) h) (z.scalarSquare W Z h)

/-- The canonical finite restriction/direct-image square; no system comparison is evaluated.
Source: Stacks 0D6E, proof Step 3
(blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.restrictionPush {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (W Z : Spaces K) (h : W.val.left ⟶ Z.val.left) :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage h
    (coefficients (A l E) Z.val.left n) (coefficients (B l E L i) Z.val.left n)
    (coefficients (A l E) W.val.left n) (coefficients (B l E L i) W.val.left n)
    (sheafMap l E L i Z.val.left n) (sheafMap l E L i W.val.left n)
    (ProEtale.StrictTower.constantRingIso (A l E n) h)
    (ProEtale.StrictTower.constantRingIso (B l E L i n) h) (z.scalarSquare W Z h)

/-- Finite scalar/pullback balancing from the canonical finite right-adjoint square.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.pull {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n) :=
  ((conjugateIsoEquiv
    ((z.scalar Y).adjunction.comp (ProEtale.VaryingRing.levelAdj (B l E L i) c.g n))
    ((ProEtale.VaryingRing.levelAdj (A l E) c.g n).comp
      (z.scalar (ambient Y c)).adjunction)).symm
        (z.restrictionPush l E L i s (ambient Y c) Y c.g)).symm

/-- The finite open coefficient balancing map is the common-right-adjoint comparison.
It uses only finite scalar/open adjunctions and the finite constant-section square.
Source: lem-sf-open-tensor-normalization, proof Step 3
(blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.openMap {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n) :=
  (conjugateIsoEquiv
    ((z.scalar X).adjunction.comp (ProEtale.VaryingRing.levelJAdj (B l E L i) c.i n))
    ((ProEtale.VaryingRing.levelJAdj (A l E) c.i n).comp
      (z.scalar (ambient Y c)).adjunction)).symm
        (z.restrictionPull l E L i s X (ambient Y c) c.i)

/-- Finite coefficient pullback is the localized ordinary constant-section adjunct.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.coefficientPull {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (W Z : Spaces K) (h : W.val.left ⟶ Z.val.left) :
    (ProEtale.StrictTower.modulePullback (A l E n) h).mapDerivedCategory.obj
        (finiteCoefficient l E L i Z n) ≅ finiteCoefficient l E L i W n := by
  letI := z.coefficientPull_isIso W Z h
  exact ((ProEtale.StrictTower.modulePullback (A l E n) h).mapDerivedCategorySingleFunctor
    0).app _ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso (asIso
      (((Scheme.proEtaleRingModuleAdjunction h
        (coefficients (A l E) Z.val.left n) (coefficients (A l E) W.val.left n)
        (ProEtale.StrictTower.constantRingIso (A l E n) h)).homEquiv _ _).symm
          (z.coefficientPush W Z h)))

/-- Finite proper PF uses the pinned finite-level tensorator and the finite counit.
Source: proof Steps 2--3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.properProjection {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (g : GeometryFamily l E L i s)
    (H : WeilConjectures.SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology c.Z) (coefficients (A l E) c.Z n)) :=
  (ProEtale.VaryingRing.levelAdj (A l E) c.g n).homEquiv _ _
    (((g (ambient Y c) Y c.g).levelMu n).hom.app
      ((ProEtale.StrictTower.moduleDirectImage (A l E n) c.g).rightDerivedFunctor.obj H,
        finiteCoefficient l E L i Y n) ≫
      ((s.scalars (ambient Y c)).lower.levelClosed n).tensor.map
        (Prod.mkHom ((ProEtale.VaryingRing.levelAdj (A l E) c.g n).counit.app H)
          (z.coefficientPull l E L i s (ambient Y c) Y c.g).hom))

/-- The independent finite open tensor inverse is the finite open-unit transpose.
This is the normalized finite balancing formula of lem-sf-open-tensor-normalization.
Source: Stacks 0E8I, proof Step 3
(blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.openTensorInv {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (g : GeometryFamily l E L i s)
    (N : WeilConjectures.SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X.val.left) (coefficients (A l E) X.val.left n)) :=
  ((ProEtale.VaryingRing.levelJAdj (A l E) c.i n).homEquiv _ _).symm
    (((s.scalars X).lower.levelClosed n).tensor.map
      (Prod.mkHom ((ProEtale.VaryingRing.levelJAdj (A l E) c.i n).unit.app N)
        (z.coefficientPull l E L i s X (ambient Y c) c.i).inv) ≫
      ((g X (ambient Y c) c.i).levelMu n).inv.app
        ((ProEtale.StrictTower.moduleJ (A l E n) c.i).mapDerivedCategory.obj N,
          finiteCoefficient l E L i (ambient Y c) n))

/-- Finite PF is the proper-counit/open-tensor word on the actual finite tensors.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.projection {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (g : GeometryFamily l E L i s)
    (N : WeilConjectures.SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X.val.left) (coefficients (A l E) X.val.left n)) :=
  z.properProjection l E L i s g
      ((ProEtale.StrictTower.moduleJ (A l E n) c.i).mapDerivedCategory.obj N) ≫
    (ProEtale.StrictTower.moduleDirectImage (A l E n) c.g).rightDerivedFunctor.map
      (SystemProjectionFormula.inverseOnDomain (z.openTensorInv l E L i s g N))

/-- The B-linear finite comparison, independently defined as proper counit transpose
and canonical finite open coefficient balancing. No system maps occur in this word.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.finiteScalarMap {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (N : WeilConjectures.SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X.val.left) (coefficients (A l E) X.val.left n)) :=
  (ProEtale.VaryingRing.levelAdj (B l E L i) c.g n).homEquiv _ _
    ((z.pull l E L i s).hom.app _ ≫
      (z.scalar (ambient Y c)).T.map
        ((ProEtale.VaryingRing.levelAdj (A l E) c.g n).counit.app
          ((ProEtale.StrictTower.moduleJ (A l E n) c.i).mapDerivedCategory.obj N))) ≫
    (ProEtale.StrictTower.moduleDirectImage (B l E L i n) c.g).rightDerivedFunctor.map
      ((z.openMap l E L i s).hom.app N)

/-- The canonical finite open restriction mate, before proving invertibility.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.restrictionOpenInv {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n) :=
  ((mateEquiv (ProEtale.VaryingRing.levelJAdj (B l E L i) c.i n)
    (ProEtale.VaryingRing.levelJAdj (A l E) c.i n)).symm
      (TwoSquare.mk _ _ _ _ (z.restrictionPull l E L i s X (ambient Y c) c.i).hom)).natTrans

/-- The specified finite compact-support restriction map, from finite proper/open mates.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.compactRestriction {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (N : WeilConjectures.SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X.val.left) (coefficients (B l E L i) X.val.left n)) :=
  (z.restrictionPush l E L i s (ambient Y c) Y c.g).hom.app
      ((ProEtale.StrictTower.moduleJ (B l E L i n) c.i).mapDerivedCategory.obj N) ≫
    (ProEtale.StrictTower.moduleDirectImage (A l E n) c.g).rightDerivedFunctor.map
      (SystemProjectionFormula.inverseOnDomain
        ((z.restrictionOpenInv l E L i s).app N))

/-- Finite tensor comparison word: the pinned finite omega, actual finite PF, and
compact support of inverse omega. Its PF is constructed from levelTensorPullback
and the independent finite open balancing, never by evaluation of a system arrow.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.finiteMap {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (g : GeometryFamily l E L i s)
    (N : WeilConjectures.SemilinearSections.D.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X.val.left) (coefficients (A l E) X.val.left n)) :=
  (z.tensor Y).derived.hom.app
      ((ProEtale.StrictTower.moduleDirectImage (A l E n) c.g).rightDerivedFunctor.obj
        ((ProEtale.StrictTower.moduleJ (A l E n) c.i).mapDerivedCategory.obj N)) ≫
    z.projection l E L i s g N ≫
    (ProEtale.StrictTower.moduleDirectImage (A l E n) c.g).rightDerivedFunctor.map
      ((ProEtale.StrictTower.moduleJ (A l E n) c.i).mapDerivedCategory.map
        ((z.tensor X).derived.inv.app N))

/-- Evaluation equals the independently constructed finite coefficient comparison;
the same comparison, after restriction and its normalized finite tensor comparison,
equals the finite PF using Geometry.levelTensorPullback and the finite open tensor map.
Source: proof Step 3 (blueprint: lem-coef-system-scalar-projection-identification). -/
def LevelData.Equation {X Y : Spaces K} {f : X.val.left ⟶ Y.val.left}
    {c : Compactification f} {n : ℕ} (z : LevelData l E L i s X Y c n)
    (g : GeometryFamily l E L i s)
    (M : Derived (A l E) (aTransition l E) X.val.left) : Prop :=
  (IsIso (z.openTensorInv l E L i s g ((level (A l E) (aTransition l E) X.val.left n).obj M)) ∧
   IsIso ((z.restrictionOpenInv l E L i s).app
     ((z.scalar X).T.obj ((level (A l E) (aTransition l E) X.val.left n).obj M))) ∧
   (finiteU l E L i Y n).map
       (z.finiteScalarMap l E L i s ((level (A l E) (aTransition l E) X.val.left n).obj M)) ≫
       z.compactRestriction l E L i s
         ((z.scalar X).T.obj ((level (A l E) (aTransition l E) X.val.left n).obj M)) =
     z.finiteMap l E L i s g ((level (A l E) (aTransition l E) X.val.left n).obj M)) ∧
  (level (B l E L i) (bTransition l E L i) Y.val.left n).map
      (comparison l E L i s X Y c M) ≫ z.properB.right.hom.app _ ≫
    (ProEtale.StrictTower.moduleDirectImage (B l E L i n) c.g).rightDerivedFunctor.map
      (z.openB.left.hom.app _ ≫
        (ProEtale.StrictTower.moduleJ (B l E L i n) c.i).mapDerivedCategory.map
          ((z.scalarEvaluation X).left.hom.app M)) =
    (z.scalarEvaluation Y).left.hom.app _ ≫
      (z.scalar Y).T.map
        (z.properA.right.hom.app ((J (A l E) (aTransition l E) c.i).obj M) ≫
          (ProEtale.StrictTower.moduleDirectImage (A l E n) c.g).rightDerivedFunctor.map
            (z.openA.left.hom.app M)) ≫
      z.finiteScalarMap l E L i s ((level (A l E) (aTransition l E) X.val.left n).obj M)

attribute [local irreducible] LevelData.Equation

/-- The fixed integral basis as constant sections of the actual upper ring system.
Source: proof Step 1 (blueprint: lem-coef-system-scalar-projection-identification). -/
def basisSection (X : Spaces K) (n : ℕ) (V : X.val.left.ProEt) (a : Fin d) :
    (ringSystem (B l E L i) (bTransition l E L i) X.val.left).obj.obj (op (n, V)) :=
  (toSheafify (Scheme.ProEt.topology X.val.left)
    ((Functor.const X.val.left.ProEtᵒᵖ).obj (B l E L i n))).app (op V)
      (Ideal.Quotient.mk ((Ideal.span {integralScalarIntegerInclusion l E L i
        (Padic.coefficientExtensionUniformizer l E)}) ^ (n + 1)) (b a))

end WeilConjectures.SystemScalarProjection
