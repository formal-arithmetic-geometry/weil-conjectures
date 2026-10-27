/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.PointCount
import Sheaf.Paper.IsomorphismFieldTransport
import Sheaf.Paper.AutomorphismConstructibleStageEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Residue-compatible pullback and three-factor local Frobenius

Source: current Weil blueprint, lem-zl-morphism-open-closed-reduction.proof.md,
Restriction; the explicit eleven-step auxiliary argument in the DAG
(blueprint: lem-zl-residue-compatible-pullback-frobenius).

Positive power index n means exponent n+1, as in LocalFrobeniusTrace.
The comparison records specify actual pullbacks and actual compositor components.

## Main statements

- `frobenius_exact`: semilinear exact autoequivalences and standard classes.
- `residueCompatiblePullbackFrobenius`: normalized Weil pullback and local comparisons.
- `immersion_residue`: closed images, actual residue maps and residue cardinalities.
- `finite_diagram_descent`: simultaneous descent of objects, inverse maps and relations.
- `composition_scalar`, `transport_scalar`: the generating coefficient-extension squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures
namespace ResidueCompatible

attribute [local irreducible] Scheme.residueField

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable {W₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

private theorem rational_composition_eq {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Z) :
    localPullbackComposition l E h k K = (fieldRationalPullComp l E h k).app K := by
  apply Iso.ext
  apply eq_of_heq
  have hc := (fieldRationalPullComp_existsUnique l E h k).exists.choose_spec K.obj
  apply HEq.trans _ hc.symm
  simp only [localPullbackComposition, localPullbackObjectIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_map, ← Category.assoc, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

private theorem qbar_composition_eq {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    localQbarPullbackComposition l Ω h k K = (zlPullComp l Ω h k).app K := by
  have hc := (zlPullComp_existsUnique l Ω h k).exists.choose_spec K.stage K.obj.obj
  apply Iso.ext
  apply (cancel_mono
    ((commonStageDerivedPullback l Ω h).map (zlStagePullIso l Ω k K.stage K.obj.obj).hom ≫
      (zlStagePullIso l Ω h K.stage
        ((constructibleIntegralPullback l _ k).obj K.obj.obj)).hom)).1
  erw [hc]
  simp only [localQbarPullbackComposition, localQbarPullbackStageIso,
    localPullbackComposition, localPullbackObjectIso, zlStagePullIso, zlIntegralPullComp,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    eqToIso.hom, eqToIso.inv, Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]
  apply eq_of_heq
  simpa only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff] using
    (HEq.rfl : HEq
      ((GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).map
        ((sfRationalConstructibleLocalization l _ X).map
          (((integralPullbackComposition l _).choose h k).hom.app K.obj.obj)))
      ((GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).map
        ((sfRationalConstructibleLocalization l _ X).map
          (((integralPullbackComposition l _).choose h k).hom.app K.obj.obj))))

attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback

namespace Rational

/-- Actual pullback on the geometric fibres. Source: Restriction
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
abbrev pull (f₀ : W₀ ⟶ X₀) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (zlFiberMap D f₀)
    (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)

/-- Pullback along the positive power of geometric Frobenius. Source: Restriction
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
abbrev power (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] (n : ℕ) :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (localPositivePower (D.geometricFrobenius T₀).hom n)
    (sfWeilPrimeInvertible D l hl T₀) (sfWeilPrimeInvertible D l hl T₀)

/-- The actual point pullback with its inherited residue units. Source: Restriction
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
abbrev point (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (t : Spec (.of D.k) ⟶ (D.geometricFiber T₀).left) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ t
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl T₀)

/-- Collapse across the Frobenius square, then expand in the other order.
Source: Restriction, proof Steps 2--3
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
def alphaComponent (f₀ : W₀ ⟶ X₀) (n : ℕ)
    (w : localPositivePower (D.geometricFrobenius W₀).hom n ≫ zlFiberMap D f₀ =
      zlFiberMap D f₀ ≫ localPositivePower (D.geometricFrobenius X₀).hom n)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    (power D l hl E W₀ n).obj ((pull D l hl E f₀).obj K) ≅
      (pull D l hl E f₀).obj ((power D l hl E X₀ n).obj K) :=
  letI := sfWeilPrimeInvertible D l hl W₀
  letI := sfWeilPrimeInvertible D l hl X₀
  (localPullbackComposition l E (localPositivePower (D.geometricFrobenius W₀).hom n)
    (zlFiberMap D f₀) K).symm ≪≫
    eqToIso (congrArg (fun f : (D.geometricFiber W₀).left ⟶
      (D.geometricFiber X₀).left ↦ (@rationalDerivedPullback l _ E _ _ _ _ _ f
        (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)).obj K) w) ≪≫
    localPullbackComposition l E (zlFiberMap D f₀)
      (localPositivePower (D.geometricFrobenius X₀).hom n) K

/-- The inverse compositor is the canonical comparison before taking the fibre.
Source: Restriction, proof Step 4
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
def pointComponent (f₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (w : z ≫ zlFiberMap D f₀ = x)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    (point D l hl E W₀ z).obj ((pull D l hl E f₀).obj K) ≅
      (point D l hl E X₀ x).obj K :=
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    fun x ↦ frobeniusPointPrimeInvertible D l hl x
  letI : ∀ x : (D.geometricFiber W₀).left,
      Invertible (l : (D.geometricFiber W₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl W₀ x
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  (@localPullbackComposition l _ E _ _ _ _ _ _ z (zlFiberMap D f₀)
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl W₀)
    (sfWeilPrimeInvertible D l hl X₀) K).symm ≪≫
    eqToIso (congrArg (fun f : Spec (.of D.k) ⟶
      (D.geometricFiber X₀).left ↦ (@rationalDerivedPullback l _ E _ _ _ _ _ f
        (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj K) w)

/-- The specified comparison c is the point fibre of the inverse compositor.
Source: Restriction, proof Step 4
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
def fibreComponent (f₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (w : z ≫ zlFiberMap D f₀ = x)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (pointRationalFibre D l hl E).mapIso (pointComponent D l hl E f₀ z x w K)

/-- All powers of the normalized Frobenius square. The induced functor on fixed pairs
is IsoAlgebra.mapOfNatIso (alpha 0), with structure alpha followed by pullback(theta).
The iterate equation uses the recorded compositor-normalized iterates.
Source: Restriction, proof Steps 2--3
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
structure Pullback (f₀ : W₀ ⟶ X₀) where
  commutes : ∀ n : ℕ,
    localPositivePower (D.geometricFrobenius W₀).hom n ≫ zlFiberMap D f₀ =
      zlFiberMap D f₀ ≫ localPositivePower (D.geometricFrobenius X₀).hom n
  alpha : ∀ n : ℕ,
    pull D l hl E f₀ ⋙ power D l hl E W₀ n ≅
      power D l hl E X₀ n ⋙ pull D l hl E f₀
  normalization : ∀ (n : ℕ) (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left),
    (alpha n).app K = alphaComponent D l hl E f₀ n (commutes n) K
  iterate : ∀ (K : sfWeilComplex D l hl X₀ E) (n : ℕ),
    (localWeilIterate l E D hl W₀ ((IsoAlgebra.mapOfNatIso (alpha 0)).obj K) n).hom =
      (alpha n).hom.app K.carrier ≫
        (pull D l hl E f₀).map (localWeilIterate l E D hl X₀ K n).hom

end Rational

attribute [local irreducible] Rational.alphaComponent
  Rational.fibreComponent

namespace Common

/-- Actual pullback on the geometric fibres. Source: Restriction
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
abbrev pull (f₀ : W₀ ⟶ X₀) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (zlFiberMap D f₀)
    (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)

/-- Pullback along the positive power of geometric Frobenius. Source: Restriction
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
abbrev power (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] (n : ℕ) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _
    (localPositivePower (D.geometricFrobenius T₀).hom n)
    (sfWeilPrimeInvertible D l hl T₀) (sfWeilPrimeInvertible D l hl T₀)

/-- The actual point pullback with its inherited residue units. Source: Restriction
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
abbrev point (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (t : Spec (.of D.k) ⟶ (D.geometricFiber T₀).left) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ t
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl T₀)

/-- Collapse across the Frobenius square, then expand in the other order.
Source: Restriction, proof Steps 2--3
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
def alphaComponent (f₀ : W₀ ⟶ X₀) (n : ℕ)
    (w : localPositivePower (D.geometricFrobenius W₀).hom n ≫ zlFiberMap D f₀ =
      zlFiberMap D f₀ ≫ localPositivePower (D.geometricFrobenius X₀).hom n)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (power D l hl Ω W₀ n).obj ((pull D l hl Ω f₀).obj K) ≅
      (pull D l hl Ω f₀).obj ((power D l hl Ω X₀ n).obj K) :=
  letI := sfWeilPrimeInvertible D l hl W₀
  letI := sfWeilPrimeInvertible D l hl X₀
  (localQbarPullbackComposition l Ω (localPositivePower (D.geometricFrobenius W₀).hom n)
    (zlFiberMap D f₀) K).symm ≪≫
    eqToIso (congrArg (fun f : (D.geometricFiber W₀).left ⟶
      (D.geometricFiber X₀).left ↦ (@commonStageDerivedPullback l _ Ω _ _ _ _ _ f
        (sfWeilPrimeInvertible D l hl W₀) (sfWeilPrimeInvertible D l hl X₀)).obj K) w) ≪≫
    localQbarPullbackComposition l Ω (zlFiberMap D f₀)
      (localPositivePower (D.geometricFrobenius X₀).hom n) K

/-- The inverse compositor is the canonical comparison before taking the fibre.
Source: Restriction, proof Step 4
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
def pointComponent (f₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (w : z ≫ zlFiberMap D f₀ = x)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    (point D l hl Ω W₀ z).obj ((pull D l hl Ω f₀).obj K) ≅
      (point D l hl Ω X₀ x).obj K :=
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    fun x ↦ frobeniusPointPrimeInvertible D l hl x
  letI : ∀ x : (D.geometricFiber W₀).left,
      Invertible (l : (D.geometricFiber W₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl W₀ x
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  (@localQbarPullbackComposition l _ Ω _ _ _ _ _ _ z (zlFiberMap D f₀)
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl W₀)
    (sfWeilPrimeInvertible D l hl X₀) K).symm ≪≫
    eqToIso (congrArg (fun f : Spec (.of D.k) ⟶
      (D.geometricFiber X₀).left ↦ (@commonStageDerivedPullback l _ Ω _ _ _ _ _ f
        (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl X₀)).obj K) w)

/-- The specified comparison c is the point fibre of the inverse compositor.
Source: Restriction, proof Step 4
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
def fibreComponent (f₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (w : z ≫ zlFiberMap D f₀ = x)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :=
  (pointQbarFibre D l hl Ω).mapIso (pointComponent D l hl Ω f₀ z x w K)

/-- All powers of the normalized Frobenius square. The induced functor on fixed pairs
is IsoAlgebra.mapOfNatIso (alpha 0), with structure alpha followed by pullback(theta).
The iterate equation uses the recorded compositor-normalized iterates.
Source: Restriction, proof Steps 2--3
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
structure Pullback (f₀ : W₀ ⟶ X₀) where
  commutes : ∀ n : ℕ,
    localPositivePower (D.geometricFrobenius W₀).hom n ≫ zlFiberMap D f₀ =
      zlFiberMap D f₀ ≫ localPositivePower (D.geometricFrobenius X₀).hom n
  alpha : ∀ n : ℕ,
    pull D l hl Ω f₀ ⋙ power D l hl Ω W₀ n ≅
      power D l hl Ω X₀ n ⋙ pull D l hl Ω f₀
  normalization : ∀ (n : ℕ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω
      (D.geometricFiber X₀).left),
    (alpha n).app K = alphaComponent D l hl Ω f₀ n (commutes n) K
  iterate : ∀ (K : sfCommonStageWeilComplex D l hl X₀ Ω) (n : ℕ),
    (localQbarWeilIterate l Ω D hl W₀ ((IsoAlgebra.mapOfNatIso (alpha 0)).obj K) n).hom =
      (alpha n).hom.app K.carrier ≫
        (pull D l hl Ω f₀).map (localQbarWeilIterate l Ω D hl X₀ K n).hom

end Common

attribute [local irreducible] Common.alphaComponent
  Common.fibreComponent

namespace Rational

variable (f₀ : W₀ ⟶ X₀) (P : Pullback D l hl E f₀)
  (z : {z : W₀.left // z ∈ closedPoints W₀.left})
  (hx : f₀.left z.val ∈ closedPoints X₀.left)
  (ιz : W₀.left.residueField z.val →+* D.k)
  (hz : ιz.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
  (ιx : X₀.left.residueField (f₀.left z.val) →+* D.k)
  (hιx : ιx.comp (X₀.hom.residueFieldAlgebraMap (f₀.left z.val)) = algebraMap D.k₀ D.k)

/-- Separate comparison of the three defining factors, followed by the equality
of derived local operators and its image on every cohomology group. The residue
condition is imposed by the theorem that supplies these data; no arbitrary stalk
isomorphism occurs here. Source: Restriction, proof Steps 4--8
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
structure Local where
  degree_eq : localClosedPointDegree D W₀ z =
    localClosedPointDegree D X₀ ⟨f₀.left z.val, hx⟩
  point_eq : localClosedPoint D W₀ z ιz hz ≫ zlFiberMap D f₀ =
    localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx
  return_x : localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx ≫
      localPositivePower (D.geometricFrobenius X₀).hom (localClosedPointDegree D W₀ z - 1) =
    localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1) ≫
      localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx
  transport : ∀ K : sfWeilComplex D l hl X₀ E,
    localPointTransportIterate l E D hl
        ((point D l hl E W₀ (localClosedPoint D W₀ z ιz hz)).obj
          ((pull D l hl E f₀).obj K.carrier)) (localClosedPointDegree D W₀ z - 1) ≫
      (pointRationalFibre D l hl E).map
        ((@rationalDerivedPullback l _ E _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1))
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).map
            (pointComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
              (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom) =
    (fibreComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
      (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      localPointTransportIterate l E D hl
        ((point D l hl E X₀
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx)).obj K.carrier)
        (localClosedPointDegree D W₀ z - 1)
  return_compositor : ∀ K : sfWeilComplex D l hl X₀ E,
    (localReturnComparison l E D hl W₀ ((IsoAlgebra.mapOfNatIso (P.alpha 0)).obj K)
        (localClosedPoint D W₀ z ιz hz) (localClosedPointDegree D W₀ z - 1)
        (localClosedPoint_return D W₀ z ιz hz)).hom ≫
      (point D l hl E W₀ (localClosedPoint D W₀ z ιz hz)).map
        ((P.alpha (localClosedPointDegree D W₀ z - 1)).hom.app K.carrier) ≫
      (pointComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
        (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq
        ((power D l hl E X₀ (localClosedPointDegree D W₀ z - 1)).obj K.carrier)).hom =
    (@rationalDerivedPullback l _ E _ _ _ _ _
      (localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1))
      (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)).map
        (pointComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      (localReturnComparison l E D hl X₀ K (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx)
        (localClosedPointDegree D W₀ z - 1) return_x).hom
  weil_map : ∀ K : sfWeilComplex D l hl X₀ E,
    (point D l hl E W₀ (localClosedPoint D W₀ z ιz hz)).map
        ((pull D l hl E f₀).map
          (localWeilIterate l E D hl X₀ K (localClosedPointDegree D W₀ z - 1)).hom) ≫
      (pointComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
        (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom =
    (pointComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
      (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq
      ((power D l hl E X₀ (localClosedPointDegree D W₀ z - 1)).obj K.carrier)).hom ≫
      (point D l hl E X₀ (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx)).map
        (localWeilIterate l E D hl X₀ K (localClosedPointDegree D W₀ z - 1)).hom
  derived : ∀ K : sfWeilComplex D l hl X₀ E,
    localClosedFrobenius l E D hl W₀ ((IsoAlgebra.mapOfNatIso (P.alpha 0)).obj K) z ιz hz ≫
      (fibreComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
        (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom =
    (fibreComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
      (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      localClosedFrobenius l E D hl X₀ K ⟨f₀.left z.val, hx⟩ ιx hιx
  cohomology : ∀ (K : sfWeilComplex D l hl X₀ E) (j : ℤ),
    (DerivedCategory.coefficientFdCohomology E j).map
        (localClosedFrobenius l E D hl W₀ ((IsoAlgebra.mapOfNatIso (P.alpha 0)).obj K) z ιz hz) ≫
      (DerivedCategory.coefficientFdCohomology E j).map
        (fibreComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom =
    (DerivedCategory.coefficientFdCohomology E j).map
        (fibreComponent D l hl E f₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      (DerivedCategory.coefficientFdCohomology E j).map (localClosedFrobenius l E D hl X₀ K
        ⟨f₀.left z.val, hx⟩ ιx hιx)

end Rational

namespace Common

variable (f₀ : W₀ ⟶ X₀) (P : Pullback D l hl Ω f₀)
  (z : {z : W₀.left // z ∈ closedPoints W₀.left})
  (hx : f₀.left z.val ∈ closedPoints X₀.left)
  (ιz : W₀.left.residueField z.val →+* D.k)
  (hz : ιz.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
  (ιx : X₀.left.residueField (f₀.left z.val) →+* D.k)
  (hιx : ιx.comp (X₀.hom.residueFieldAlgebraMap (f₀.left z.val)) = algebraMap D.k₀ D.k)

/-- Separate comparison of the three defining factors, followed by the equality
of derived local operators and its image on every cohomology group. The residue
condition is imposed by the theorem that supplies these data; no arbitrary stalk
isomorphism occurs here. Source: Restriction, proof Steps 4--8
(blueprint: lem-zl-residue-compatible-pullback-frobenius). -/
structure Local where
  degree_eq : localClosedPointDegree D W₀ z =
    localClosedPointDegree D X₀ ⟨f₀.left z.val, hx⟩
  point_eq : localClosedPoint D W₀ z ιz hz ≫ zlFiberMap D f₀ =
    localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx
  return_x : localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx ≫
      localPositivePower (D.geometricFrobenius X₀).hom (localClosedPointDegree D W₀ z - 1) =
    localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1) ≫
      localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx
  transport : ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
    localQbarPointTransportIterate l Ω D hl
        ((point D l hl Ω W₀ (localClosedPoint D W₀ z ιz hz)).obj
          ((pull D l hl Ω f₀).obj K.carrier)) (localClosedPointDegree D W₀ z - 1) ≫
      (pointQbarFibre D l hl Ω).map
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1))
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).map
            (pointComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
              (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom) =
    (fibreComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
      (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      localQbarPointTransportIterate l Ω D hl
        ((point D l hl Ω X₀
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx)).obj K.carrier)
        (localClosedPointDegree D W₀ z - 1)
  return_compositor : ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
    (localQbarReturnComparison l Ω D hl W₀ ((IsoAlgebra.mapOfNatIso (P.alpha 0)).obj K)
        (localClosedPoint D W₀ z ιz hz) (localClosedPointDegree D W₀ z - 1)
        (localClosedPoint_return D W₀ z ιz hz)).hom ≫
      (point D l hl Ω W₀ (localClosedPoint D W₀ z ιz hz)).map
        ((P.alpha (localClosedPointDegree D W₀ z - 1)).hom.app K.carrier) ≫
      (pointComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
        (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq
        ((power D l hl Ω X₀ (localClosedPointDegree D W₀ z - 1)).obj K.carrier)).hom =
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _
      (localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D W₀ z - 1))
      (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)).map
        (pointComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      (localQbarReturnComparison l Ω D hl X₀ K (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx)
        (localClosedPointDegree D W₀ z - 1) return_x).hom
  weil_map : ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
    (point D l hl Ω W₀ (localClosedPoint D W₀ z ιz hz)).map
        ((pull D l hl Ω f₀).map
          (localQbarWeilIterate l Ω D hl X₀ K (localClosedPointDegree D W₀ z - 1)).hom) ≫
      (pointComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
        (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom =
    (pointComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
      (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq
      ((power D l hl Ω X₀ (localClosedPointDegree D W₀ z - 1)).obj K.carrier)).hom ≫
      (point D l hl Ω X₀ (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx)).map
        (localQbarWeilIterate l Ω D hl X₀ K (localClosedPointDegree D W₀ z - 1)).hom
  derived : ∀ K : sfCommonStageWeilComplex D l hl X₀ Ω,
    localQbarClosedFrobenius l Ω D hl W₀ ((IsoAlgebra.mapOfNatIso (P.alpha 0)).obj K) z ιz hz ≫
      (fibreComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
        (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom =
    (fibreComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
      (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      localQbarClosedFrobenius l Ω D hl X₀ K ⟨f₀.left z.val, hx⟩ ιx hιx
  cohomology : ∀ (K : sfCommonStageWeilComplex D l hl X₀ Ω) (j : ℤ),
    (DerivedCategory.coefficientQbarCohomology l Ω j).map
        (localQbarClosedFrobenius l Ω D hl W₀ ((IsoAlgebra.mapOfNatIso (P.alpha 0)).obj K) z ιz
          hz) ≫
      (DerivedCategory.coefficientQbarCohomology l Ω j).map
        (fibreComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom =
    (DerivedCategory.coefficientQbarCohomology l Ω j).map
        (fibreComponent D l hl Ω f₀ (localClosedPoint D W₀ z ιz hz)
          (localClosedPoint D X₀ ⟨f₀.left z.val, hx⟩ ιx hιx) point_eq K.carrier).hom ≫
      (DerivedCategory.coefficientQbarCohomology l Ω j).map (localQbarClosedFrobenius l Ω D hl X₀
        K ⟨f₀.left z.val, hx⟩ ιx hιx)

end Common

section CanonicalExactness
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

private theorem fieldShift_ext
    {C B : Type*} [Category C] [Category B] [HasShift C ℤ] [HasShift B ℤ]
    {F : C ⥤ B} (s t : F.CommShift ℤ)
    (h : ∀ r, s.commShiftIso r = t.commShiftIso r) : s = t := by
  cases s
  cases t
  congr
  funext r
  exact h r

attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι in
private theorem fieldConstructibleShift_normalization
    (c : (constructibleIntegralPullback l E f).CommShift ℤ)
    (h : automorphismStageIntegralShiftNormalization l E f c) :
    c = fieldConstructiblePullShift l E f := by
  obtain ⟨a, d, ha, hd, hc⟩ := h
  have he : d = fieldIntegralPullShift l E f :=
    (fieldIntegralPullShift_existsUnique l E f).unique ⟨a, ha, hd⟩
      (fieldIntegralPullShift_existsUnique l E f).exists.choose_spec
  subst d
  apply fieldShift_ext
  intro r
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (sfIntegralConstructible l E X).ι.map_injective
  have hK := hc K r
  apply eq_of_heq
  exact hK.trans (by
    dsimp only [fieldConstructiblePullShift, Functor.CommShift.ofComp,
      Functor.commShiftIso]
    erw [Functor.CommShift.OfComp.map_iso_hom_app]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Functor.commShiftIso_comp_hom_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id]
    erw [Category.id_comp]
    rfl)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem fieldRationalShift_normalization
    (c : (rationalDerivedPullback l E f).CommShift ℤ)
    (h : automorphismStageRationalShiftNormalization l E f c) :
    c = fieldRationalPullShift l E f := by
  obtain ⟨s, hs, hn⟩ := h
  have he := fieldConstructibleShift_normalization l E f s hs
  subst s
  apply (fieldRationalPullShift_existsUnique l E f).unique
  · intro K
    exact hn ⟨K⟩ 1
  · exact (fieldRationalPullShift_existsUnique l E f).exists.choose_spec

private theorem canonical_rational_exact :
    (rationalDerivedPullback l E f).IsTriangulated := by
  obtain ⟨C, _⟩ := automorphismConstructibleStage_comparison_system.{u} l
  obtain ⟨c, _, _, hc, _, _, he⟩ :=
    (automorphismConstructibleStage_descended_shifts l (AlgebraicClosure ℚ_[l]) C f
      (Iso.refl _) (Iso.refl _) (by simp)).1 E
  have h := fieldRationalShift_normalization l E f c hc
  subst c
  exact he.1

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

private theorem canonical_common_exact :
    (commonStageDerivedPullback l Ω f).IsTriangulated := by
  obtain ⟨C, _⟩ := automorphismConstructibleStage_comparison_system.{u} l
  obtain ⟨c, _, _, hc, _, _, he⟩ :=
    (automorphismConstructibleStage_descended_shifts l Ω C f
      (Iso.refl _) (Iso.refl _) (by simp)).2
  have h : c = fieldCommonPullShift l Ω f := by
    apply (fieldCommonPullShift_existsUnique l Ω f).unique
    · intro L K
      obtain ⟨s, hs, hn⟩ := hc L
      have h := fieldRationalShift_normalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f s hs
      subst s
      exact hn K 1
    · exact (fieldCommonPullShift_existsUnique l Ω f).exists.choose_spec
  subst c
  exact he.1
end CanonicalExactness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rational_class_pullback
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : IsomorphismFieldTransportStage l E g hX hY)
    (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y)
    (hK : sfRationalStandardClass l E Y b n K) :
    sfRationalStandardClass l E X b n ((rationalDerivedPullback l E g).obj K) := by
  have := S.moduleAdditive
  have := S.moduleLimits
  have := S.moduleColimits
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  refine ⟨(constructibleIntegralPullback l E g).obj M, ?_,
    ⟨(rationalDerivedPullback l E g).mapIso e ≪≫ eqToIso (S.rational_object _)⟩⟩
  intro i hi
  let G := AlgebraicGeometry.ProEtale.inverseImageIntegralModules l E g
  have hz := G.isZero_homologyFunctor_mapDerivedCategory_obj (hM i hi)
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (S.lambda.app M))

private theorem common_class_pullback
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      IsomorphismFieldTransportStage l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g hX hY)
    (C : IsomorphismFieldTransportCommon l Ω g hX hY S)
    (b : Bool) (n : ℤ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (hK : sfCommonStageStandardClass l Y Ω b n K) :
    sfCommonStageStandardClass l X Ω b n ((commonStageDerivedPullback l Ω g).obj K) := by
  obtain ⟨L, M, hM, ⟨e⟩⟩ := hK
  refine ⟨L, (rationalDerivedPullback l _ g).obj M,
    rational_class_pullback l _ g hX hY (S L) b n M hM, ?_⟩
  exact ⟨(commonStageDerivedPullback l Ω g).mapIso e ≪≫ (C.stageComparison L).app M⟩

/-- Semilinear Frobenius preserves the triangulated structure and both standard
half-categories, in both directions. Source: Restriction, proof Step 1
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: the scheme isomorphism and its inverse induce exact inverse-image equivalences
on the pro-etale site (lem-weil-proetale-isomorphism-inverse-image). Identify derived
pullback with these by lem-weil-isomorphism-derived-pullback. They preserve
constructibility and cohomology. Localize integral triangles and standard classes;
then use finite-stage representatives for the common-stage assertion. No k-linearity
is used for either scheme automorphism. -/
theorem frobenius_exact (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    (sfWeilFrobeniusPullback D l hl T₀ E).IsEquivalence ∧
    (sfWeilFrobeniusPullback D l hl T₀ E).IsTriangulated ∧
    (∀ (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E
        (D.geometricFiber T₀).left),
      sfRationalStandardClass l E (D.geometricFiber T₀).left b n
          ((sfWeilFrobeniusPullback D l hl T₀ E).obj K) ↔
        sfRationalStandardClass l E (D.geometricFiber T₀).left b n K) ∧
    (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsEquivalence ∧
    (sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).IsTriangulated ∧
    (∀ (b : Bool) (n : ℤ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω
        (D.geometricFiber T₀).left),
      sfCommonStageStandardClass l (D.geometricFiber T₀).left Ω b n
          ((sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω).obj K) ↔
        sfCommonStageStandardClass l (D.geometricFiber T₀).left Ω b n K) := by
  let : (D.geometricFiber T₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber T₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber T₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  obtain ⟨iX, iY, h⟩ := isomorphismFieldTransport D l hl Ω
    (D.geometricFrobenius T₀).hom
  have hx : iX = (fun x ↦ sfWeilPrimeInvertible D l hl T₀ x) := Subsingleton.elim _ _
  have hy : iY = (fun x ↦ sfWeilPrimeInvertible D l hl T₀ x) := Subsingleton.elim _ _
  subst iX
  subst iY
  let := sfWeilPrimeInvertible D l hl T₀
  obtain ⟨hX, hY, hs, _, S, R, _, ⟨C⟩, ⟨B⟩⟩ := h
  obtain ⟨SE⟩ := (hs E).1
  obtain ⟨RE⟩ := (hs E).2
  refine ⟨SE.rationalEquivalence,
    canonical_rational_exact l E (D.geometricFrobenius T₀).hom, ?_,
    C.equivalence, canonical_common_exact l (D.geometricFrobenius T₀).hom Ω, ?_⟩
  · intro b n K
    constructor
    · intro hK
      obtain ⟨M, hM, ⟨e⟩⟩ := rational_class_pullback l E
        (inv (D.geometricFrobenius T₀).hom) hY hX RE b n _ hK
      exact ⟨M, hM, ⟨(SE.rationalEpsilon.app K).symm ≪≫ e⟩⟩
    · exact rational_class_pullback l E (D.geometricFrobenius T₀).hom hX hY SE b n K
  · intro b n K
    constructor
    · intro hK
      obtain ⟨L, M, hM, ⟨e⟩⟩ := common_class_pullback l Ω
        (inv (D.geometricFrobenius T₀).hom) hY hX R B b n _ hK
      exact ⟨L, M, hM, ⟨(C.epsilon.app K).symm ≪≫ e⟩⟩
    · exact common_class_pullback l Ω (D.geometricFrobenius T₀).hom hX hY S C b n K

/-- The residue hypothesis supplies the common return and all three-factor equations.
The positive-power index r-1 denotes exponent r, including r=1. The structure map
of the induced fixed pair is alpha_1 followed by pullback(theta), by
IsoAlgebra.mapOfNatIso. Source: Restriction, proof Steps 2--9
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: base-change Frobenius commutes with f. Collapse and expand by the associative
integral compositor (lem-pod-integral-pullback-composition), then rationalize and
pass to common stages. Naturality gives the fixed-pair functor. Associativity and
induction give its iterate identity. The actual residue isomorphism gives equal
finite degrees by lem-kun-closed-point-field; compatible embeddings give the point
square and common return. The inverse compositor defines e, and Fib(e) defines c.
Naturality of iterated point transport (lem-weil-frobenius-point-transport-natural)
gives the first factor. Expand alpha and return compositors, apply associativity
three times and cancel inverse compositors for the middle factor. Naturality at
theta^[r] gives the third factor. Composing the three equalities gives the derived
intertwining equation. Apply coefficient cohomology to get every degree. The heart
and stalk identifications follow from lem-a1-constructible-pullback-t-exact. -/
theorem residueCompatiblePullbackFrobenius (f₀ : W₀ ⟶ X₀)
    [IsSeparated W₀.hom] [IsSeparated X₀.hom] :
    ∃ (P : Rational.Pullback D l hl E f₀) (Q : Common.Pullback D l hl Ω f₀),
      ∀ (z : {z : W₀.left // z ∈ closedPoints W₀.left})
        (hx : f₀.left z.val ∈ closedPoints X₀.left),
        IsIso (f₀.left.residueFieldMap z.val) →
        ∀ (ιz : W₀.left.residueField z.val →+* D.k)
          (hz : ιz.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
          (ιx : X₀.left.residueField (f₀.left z.val) →+* D.k)
          (hιx : ιx.comp (X₀.hom.residueFieldAlgebraMap (f₀.left z.val)) =
            algebraMap D.k₀ D.k),
          ιz.comp (f₀.left.residueFieldMap z.val).hom = ιx →
          Nonempty (Rational.Local D l hl E f₀ P z hx ιz hz ιx hιx) ∧
            Nonempty (Common.Local D l hl Ω f₀ Q z hx ιz hz ιx hιx) := by
  sorry

set_option linter.unusedSectionVars false in
/-- A locally closed immersion preserves closed points and their actual residue fields.
Source: Restriction, proof Step 9
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: an immersion is surjective on stalks, so its actual residue map is an
isomorphism by Scheme.Hom.isIso_residueFieldMap. The finite-point criterion
identifies closed points with points having finite residue fields. Transporting
finiteness across the residue isomorphism therefore proves closedness of the
image. The vector-space cardinality formula gives q^r at the source, and the
residue-field isomorphism transports this cardinality to the image. -/
theorem immersion_residue (f₀ : W₀ ⟶ X₀) [IsImmersion f₀.left]
    [IsSeparated W₀.hom] [IsSeparated X₀.hom]
    (z : {z : W₀.left // z ∈ closedPoints W₀.left}) :
    f₀.left z.val ∈ closedPoints X₀.left ∧
      IsIso (f₀.left.residueFieldMap z.val) ∧
      Nat.card (W₀.left.residueField z.val) = D.q ^ localClosedPointDegree D W₀ z ∧
      Nat.card (X₀.left.residueField (f₀.left z.val)) =
        D.q ^ localClosedPointDegree D W₀ z := by
  have hi : IsIso (f₀.left.residueFieldMap z.val) :=
    Scheme.Hom.isIso_residueFieldMap f₀.left z.val
  have hz : z.val ∈ W₀.left.finitePoints := by
    rw [W₀.hom.finitePoints_eq_closedPoints]
    exact z.prop
  have hx : f₀.left z.val ∈ closedPoints X₀.left := by
    rw [← X₀.hom.finitePoints_eq_closedPoints]
    exact (f₀.left.mem_finitePoints_iff_of_isIso z.val).mpr hz
  have hc : Nat.card (W₀.left.residueField z.val) =
      D.q ^ localClosedPointDegree D W₀ z := by
    let := (W₀.hom.residueFieldAlgebraMap z.val).toAlgebra
    have : Finite (W₀.left.residueField z.val) := W₀.left.mem_finitePoints.mp hz
    simpa only [localClosedPointDegree, D.card_base] using
      (Module.natCard_eq_pow_finrank (K := D.k₀)
        (V := W₀.left.residueField z.val))
  refine ⟨hx, hi, hc, ?_⟩
  exact (f₀.left.pointNorm_of_isIso z.val).trans hc

/-- Naturality of the specified inverse-compositor point comparison.
Source: Restriction, proof Steps 4 and 7
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: naturality of the integral pullback compositor passes through rationalization
and common-stage representatives; the equality identifying the composite point is
natural. Invert the compositor and compose these natural squares. -/
theorem rational_point_naturality (f₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : z ≫ zlFiberMap D f₀ = x)
    (K M : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) (a : K ⟶ M) :
    (Rational.point D l hl E W₀ z).map ((Rational.pull D l hl E f₀).map a) ≫
        (Rational.pointComponent D l hl E f₀ z x w M).hom =
      (Rational.pointComponent D l hl E f₀ z x w K).hom ≫
        (Rational.point D l hl E X₀ x).map a := by
  let := frobeniusPointPrimeInvertible D l hl
  let := sfWeilPrimeInvertible D l hl W₀
  let := sfWeilPrimeInvertible D l hl X₀
  subst x
  dsimp only [Rational.pointComponent]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rw [rational_composition_eq, rational_composition_eq]
  exact (fieldRationalPullComp l E z (zlFiberMap D f₀)).inv.naturality a

/-- Pullback restricts to constructible sheaves; degree-zero fibre comparison is
therefore the canonical stalk comparison, with equivariance given by Local.cohomology.
Source: Restriction, proof Step 8
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: f is a k-morphism, so lem-a1-constructible-pullback-t-exact preserves both
standard degree-zero classes. Their intersection is the recorded heart. Apply the
same theorem to the geometric points to identify degree-zero derived fibres with
stalks; the compositor normalization identifies the induced maps. -/
theorem rational_heart (f₀ : W₀ ⟶ X₀)
    (K : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) :
    sfRationalHeartProperty l E (D.geometricFiber X₀).left K →
      sfRationalHeartProperty l E (D.geometricFiber W₀).left ((Rational.pull D l hl E f₀).obj K)
        := by
  sorry

/-- Naturality of the specified inverse-compositor point comparison.
Source: Restriction, proof Steps 4 and 7
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: naturality of the integral pullback compositor passes through rationalization
and common-stage representatives; the equality identifying the composite point is
natural. Invert the compositor and compose these natural squares. -/
theorem common_point_naturality (f₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (w : z ≫ zlFiberMap D f₀ = x)
    (K M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) (a : K
      ⟶ M) :
    (Common.point D l hl Ω W₀ z).map ((Common.pull D l hl Ω f₀).map a) ≫
        (Common.pointComponent D l hl Ω f₀ z x w M).hom =
      (Common.pointComponent D l hl Ω f₀ z x w K).hom ≫
        (Common.point D l hl Ω X₀ x).map a := by
  let := frobeniusPointPrimeInvertible D l hl
  let := sfWeilPrimeInvertible D l hl W₀
  let := sfWeilPrimeInvertible D l hl X₀
  subst x
  dsimp only [Common.pointComponent]
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rw [qbar_composition_eq, qbar_composition_eq]
  exact (zlPullComp l Ω z (zlFiberMap D f₀)).inv.naturality a

/-- Pullback restricts to constructible sheaves; degree-zero fibre comparison is
therefore the canonical stalk comparison, with equivariance given by Local.cohomology.
Source: Restriction, proof Step 8
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: f is a k-morphism, so lem-a1-constructible-pullback-t-exact preserves both
standard degree-zero classes. Their intersection is the recorded heart. Apply the
same theorem to the geometric points to identify degree-zero derived fibres with
stalks; the compositor normalization identifies the induced maps. -/
theorem common_heart (f₀ : W₀ ⟶ X₀)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left) :
    sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω K →
      sfCommonStageHeartProperty l (D.geometricFiber W₀).left Ω ((Common.pull D l hl Ω f₀).obj K)
        := by
  intro hK
  exact zlPull_mem D l hl Ω f₀ ⟨K, hK⟩

/-- Every finite graph of Weil pairs and any finite list of path equations descend
together. Each object of A is already an IsoAlgebra, so both inverse Weil equations
hold over L. The conjugacy equation uses the literal existing stage object and
inclusion on arrows, without choosing another fixed-pair inclusion functor.
Source: Restriction, proof Step 11
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: choose stages for the finitely many carriers, Weil maps and inverse maps,
and graph arrows. Choose one finite upper coefficient field. Every relation,
including equivariance and the two inverse equations, is an equality in the
common-stage Hom quotient, so holds after a finite further enlargement. Take a
common upper field for these finitely many witnesses. The resulting rational
objects and arrows form A; the quotient identifications give e. The empty graph
uses the base coefficient field. Integral lattices enter only as representatives
of carriers; no lattice is required to be stable under the Weil map. -/
theorem finite_diagram_descent (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (I : Type u) [Finite I] [Quiver.{u} I] [∀ i j : I, Finite (i ⟶ j)]
    (F : Paths I ⥤ sfCommonStageWeilComplex D l hl T₀ Ω)
    (n : ℕ) (a b : Fin n → Paths I)
    (p q : ∀ t : Fin n, a t ⟶ b t)
    (relations : ∀ t : Fin n, F.map (p t) = F.map (q t)) :
    ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (A : Paths I ⥤ sfWeilComplex D l hl T₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
      (e : ∀ i : Paths I, sfWeilStageObject D l hl T₀ Ω L (A.obj i) ≅ F.obj i),
      (∀ (i j : Paths I) (v : i ⟶ j),
        (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          ((IsoAlgebra.forget _).map (A.map v)) =
          (IsoAlgebra.forget _).map ((e i).hom ≫ F.map v ≫ (e j).inv)) ∧
      ∀ t : Fin n, A.map (p t) = A.map (q t) := by
  sorry

section Scalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Scalar compatibility of the specified rationalized compositor, for arbitrary
scheme maps including semilinear ones. It also specifies its inverse, all alpha_m,
point e and return R comparisons by composition and cancellation. Naturality of
these same scalar comparisons identifies the maps induced by theta^[r].
Source: Restriction, proof Step 10
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: rationalize the composition/scalar square of
lem-pod-pullback-identities-scalar-extension, with its canonical comparison
families, not arbitrary systems. The scalar and pullback comparisons are the
normalized integral ones. Cancel invertible comparison factors for inverses;
compose the squares for alpha_m, e and R. Naturality gives the theta-map square.
Identity and tower laws pass these maps to the recorded common-stage quotient. -/
theorem composition_scalar {S T U : Scheme.{u}} (h : S ⟶ T) (k : T ⟶ U)
    [∀ s : S, Invertible (l : S.residueField s)]
    [∀ t : T, Invertible (l : T.residueField t)]
    [∀ t : U, Invertible (l : U.residueField t)]
    (K : sfRationalConstructibleCategory l E U) :
    (sfRationalScalarExtension l E S 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        (localPullbackComposition l E h k K).hom ≫
      (rationalPullbackScalarComparison l E L ι h).hom.app
        ((rationalDerivedPullback l E k).obj K) ≫
      (rationalDerivedPullback l L h).map
        ((rationalPullbackScalarComparison l E L ι k).hom.app K) =
    (rationalPullbackScalarComparison l E L ι (h ≫ k)).hom.app K ≫
      (localPullbackComposition l L h k
        ((sfRationalScalarExtension l E U 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K)).hom := by
  sorry

/-- Scalar compatibility of every iterated point transport, completing the first
of the three-factor scalar squares; the other two are composition_scalar and
naturality. Source: Restriction, proof Step 10
(blueprint: lem-zl-residue-compatible-pullback-frobenius).
Proof: apply lem-weil-frobenius-point-transport-natural's scalar equation r times.
The middle fibre comparisons cancel. Use the scalar compositor equation to replace
the iterated pullback by pullback along the positive power. Point sections commute
with finite scalar extension by lem-weil-point-sections-scalar-extension. Hence
the complete local operator and all its cohomology maps commute with extension. -/
theorem transport_scalar (N : sfRationalConstructibleCategory l E (Spec (.of D.k)))
    (n : ℕ) :
    letI := frobeniusPointPrimeInvertible D l hl
    (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (localPointTransportIterate l E D hl N n) ≫
      (pointRationalFibreScalarIso D l hl E L ι).inv.app
        ((rationalDerivedPullback l E (localPositivePower (frobeniusPointIso D).hom n)).obj
          N) ≫
      (pointRationalFibre D l hl L).map
        ((rationalPullbackScalarComparison l E L ι
          (localPositivePower (frobeniusPointIso D).hom n)).hom.app N) =
    (pointRationalFibreScalarIso D l hl E L ι).inv.app N ≫
      localPointTransportIterate l L D hl
        ((sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N) n := by
  sorry
end Scalar

end ResidueCompatible
end WeilConjectures
