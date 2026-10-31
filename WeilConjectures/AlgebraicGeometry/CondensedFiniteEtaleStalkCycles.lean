/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleAdaptedBaseStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.PullbackConstantModelConstructible

/-! # Condensed finite etale stalk cycles

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-finite-map,
lem-a1-finite-map-purity.proof.md, first paragraph; Stacks 03QP(1), with the
condensed and Weil refinement recorded in the DAG
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles).

The coefficient field is the standard chosen algebraic closure, with its universe lift.
All fibres are the existing point-sections functor applied to module pullback. All
restriction arrows are the existing adjunction-counit arrows. The local operators below
are the degree-zero specialization of the recorded local-return convention: the canonical
point reparametrization, pullback composition, and the iterated Weil isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures.CondensedFiniteEtale

open WeilConjectures.CondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The existing base-change functor applied to g_0.
Source: blueprint geometric base change (blueprint: lem-a1-condensed-finite-etale-stalk-cycles).
-/
def geometricMap (g₀ : X₀ ⟶ Y₀) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map g₀).left

/-- The ordinary module direct image, including its canonical coefficient action.
Source: blueprint definition G=g_*F; det-def-sfb-module-pushforward-pullback
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def directImage (g₀ : X₀ ⟶ Y₀) (M : Modules l (D.geometricFiber X₀).left) :=
  (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D g₀)).obj M

/-- The specified exchange followed by g_*theta, with no choice of a Weil structure.
Source: blueprint Weil-structure clause
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def directImageWeil (g₀ : X₀ ⟶ Y₀)
    (h : (D.geometricFrobenius X₀).hom ≫ geometricMap D g₀ =
      geometricMap D g₀ ≫ (D.geometricFrobenius Y₀).hom)
    (M : Modules l (D.geometricFiber X₀).left)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).obj M ≅ M) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom).obj (directImage D l g₀ M) ≅ directImage D l g₀ M :=
  (asIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
    (CommSq.mk h))).app M ≪≫
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D g₀)).mapIso θ

/-- The actual points of the model above y, without a closedness assumption on them.
Source: blueprint S_y (blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
abbrev ModelPoints (g₀ : X₀ ⟶ Y₀) (y : Y₀.left) := {x : X₀.left // g₀.left x = y}

/-- The residue degree for the canonical map kappa(y) to kappa(x).
Source: blueprint e_x=[kappa(x):kappa(y)]
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def residueDegree (g₀ : X₀ ⟶ Y₀) (y : Y₀.left) (x : ModelPoints D g₀ y) : ℕ :=
  letI := ((Y₀.left.residueFieldCongr x.property.symm).hom ≫
    g₀.left.residueFieldMap x.val).hom.toAlgebra
  Module.finrank (Y₀.left.residueField y) (X₀.left.residueField x.val)

/-- The geometric points over ybar whose projection to the model is x.
Source: blueprint P_x (blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
abbrev Points (g₀ : X₀ ⟶ Y₀) (y : Y₀.left)
    (ybar : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (x : ModelPoints D g₀ y) :=
  {z : CondensedRing.FibrePoints (geometricMap D g₀) ybar //
    (z.val ≫ pullback.fst X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = x.val}

/-- The restriction arrow, obtained from the actual pullback/direct-image counit.
Source: blueprint pi_z; Stacks 03QP
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def restriction (g₀ : X₀ ⟶ Y₀) (M : Modules l (D.geometricFiber X₀).left)
    (ybar : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (z : CondensedRing.FibrePoints (geometricMap D g₀) ybar) :
    fibre l D (directImage D l g₀ M) ybar ⟶ fibre l D M z.val :=
  (CondensedRing.pointSections l D.k).map
    (CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) z.property M)

/-- The complete fibre comparison, with its prescribed restriction components and local returns.
The cycle is transitive on every P_x, including a singleton; its linear transports are
canonical, so zero summands do not hide the geometric permutation.
Source: blueprint first paragraph, all fibre and cycle clauses
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
structure FibreComparison (g₀ : X₀ ⟶ Y₀)
    (h : (D.geometricFrobenius X₀).hom ≫ geometricMap D g₀ =
      geometricMap D g₀ ≫ (D.geometricFrobenius Y₀).hom)
    (M : Modules l (D.geometricFiber X₀).left)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).obj M ≅ M)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) where
  finite_model : Finite (ModelPoints D g₀ y.val)
  closed_model : ∀ x : ModelPoints D g₀ y.val, x.val ∈ closedPoints X₀.left
  finite_points : ∀ x : ModelPoints D g₀ y.val,
    Finite (Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x)
  card_points : ∀ x : ModelPoints D g₀ y.val,
    Nat.card (Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x) =
      residueDegree D g₀ y.val x
  degree_pos : ∀ x : ModelPoints D g₀ y.val, 1 ≤ residueDegree D g₀ y.val x
  card_residue : ∀ x : ModelPoints D g₀ y.val,
    Nat.card (X₀.left.residueField x.val) =
      Nat.card (Y₀.left.residueField y.val) ^ residueDegree D g₀ y.val x
  finite_stalk : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
    (fibre l D (directImage D l g₀ M) (localClosedPoint D Y₀ y ι hι))
  finite_summands : ∀ (x : ModelPoints D g₀ y.val)
    (z : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x),
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M z.val.val)
  comparison :
    fibre l D (directImage D l g₀ M) (localClosedPoint D Y₀ y ι hι) ≃ₗ[
      ULift.{u + 1} (PadicAlgCl l)]
      ⨁ x : ModelPoints D g₀ y.val,
        ⨁ z : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x, fibre l D M z.val.val
  comparison_components : ∀ v (x : ModelPoints D g₀ y.val)
    (z : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x),
    comparison v x z = restriction D l g₀ M (localClosedPoint D Y₀ y ι hι) z.val v
  cycle : ∀ x : ModelPoints D g₀ y.val,
    Equiv.Perm (Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x)
  transitive_cycle : ∀ (x : ModelPoints D g₀ y.val) (z z'), ∃ n : ℕ, (cycle x ^ n) z = z'
  cycle_return : ∀ (x : ModelPoints D g₀ y.val)
    (z : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x),
    z.val.val ≫ localPositivePower (D.geometricFrobenius X₀).hom
        (localClosedPointDegree D Y₀ y - 1) =
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D Y₀ y - 1) ≫
        (cycle x z).val.val
  cycle_action : ∀ (x : ModelPoints D g₀ y.val)
    (z : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x),
    CommSq
      (operator l D (D.geometricFrobenius Y₀).hom (directImage D l g₀ M)
        (directImageWeil D l g₀ h M θ) (localClosedPoint D Y₀ y ι hι)
        (localClosedPointDegree D Y₀ y - 1) (localClosedPoint_return D Y₀ y ι hι))
      (restriction D l g₀ M (localClosedPoint D Y₀ y ι hι) (cycle x z).val)
      (restriction D l g₀ M (localClosedPoint D Y₀ y ι hι) z.val)
      (transport l D (D.geometricFrobenius X₀).hom M θ z.val.val (cycle x z).val.val
        (localClosedPointDegree D Y₀ y - 1) (cycle_return x z)).hom
  local_return : ∀ (x : ModelPoints D g₀ y.val)
    (z : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x),
    z.val.val ≫ localPositivePower (D.geometricFrobenius X₀).hom
        (localClosedPointDegree D X₀ ⟨x.val, closed_model x⟩ - 1) =
      localPositivePower (frobeniusPointIso D).hom
        (localClosedPointDegree D X₀ ⟨x.val, closed_model x⟩ - 1) ≫ z.val.val
  power_return : ∀ (x : ModelPoints D g₀ y.val)
    (z : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x),
    CommSq
      (operator l D (D.geometricFrobenius Y₀).hom (directImage D l g₀ M)
        (directImageWeil D l g₀ h M θ) (localClosedPoint D Y₀ y ι hι)
        (localClosedPointDegree D Y₀ y - 1) (localClosedPoint_return D Y₀ y ι hι) ^
          residueDegree D g₀ y.val x)
      (restriction D l g₀ M (localClosedPoint D Y₀ y ι hι) z.val)
      (restriction D l g₀ M (localClosedPoint D Y₀ y ι hι) z.val)
      (operator l D (D.geometricFrobenius X₀).hom M θ z.val.val
        (localClosedPointDegree D X₀ ⟨x.val, closed_model x⟩ - 1) (local_return x z))

/-- A constructible condensed Weil module has the asserted finite etale stalk cycles.
Source: latest blueprint lem-a1-finite-map-purity.proof.md, first paragraph; Stacks 03QP(1)
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles).

Proof plan:
1. The geometric fibres are Noetherian. Apply
   lem-a1-finite-etale-adapted-base-stratification to a finite lisse stratification of M.
   Pullback preserves the lisse models on each clopen part.
2. Use lem-a1-finite-etale-condensed-base-change and the etale-local splitting of the
   finite etale map. Direct image is a finite product of lisse modules; simultaneous
   refinement makes it finite free, also for an empty product. The Frobenius square is
   Cartesian since both Frobenius maps are automorphisms, giving the displayed exchange.
3. For a closed y base change to kappa(y) and use lem-zl-condensed-finite-fibre-evaluation
   in degree zero. Its evaluation is the counit restriction. The closed fibre points are
   exactly the model points above y; each block has residue degree many geometric lifts.
   A field basis gives the asserted residue-field cardinality.
4. Exchange naturality identifies the local direct-image operator with the finite-fibre
   operator. Its transitive cycles preserve each closed-point block. Concatenating the
   degree(y) iterates residueDegree(x) times gives degree(x) iterates, with the identical
   geometric-point reparametrization and pullback compositors. This gives power_return
   as an equality of the specified operators, using lem-weil-pbc-profinite-point-pullback.
-/
theorem stalkCycles (hl : l ≠ D.p) (g₀ : X₀ ⟶ Y₀) [IsFinite g₀.left] [Etale g₀.left]
    (M : Modules l (D.geometricFiber X₀).left)
    (hM : ∃ S : (D.geometricFiber X₀).left.FiniteLocallyClosedStratification,
      ∀ a : Fin S.n, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (S.immersion a)).obj M))
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).obj M ≅ M) :
    ∃ h : (D.geometricFrobenius X₀).hom ≫ geometricMap D g₀ =
        geometricMap D g₀ ≫ (D.geometricFrobenius Y₀).hom,
      (∃ S : (D.geometricFiber Y₀).left.FiniteLocallyClosedStratification,
        ∀ a : Fin S.n, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (S.immersion a)).obj
            (directImage D l g₀ M))) ∧
      ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
        (ι : Y₀.left.residueField y.val →+* D.k)
        (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
        Nonempty (FibreComparison D l g₀ h M θ y ι hι) := by
  sorry

end WeilConjectures.CondensedFiniteEtale
