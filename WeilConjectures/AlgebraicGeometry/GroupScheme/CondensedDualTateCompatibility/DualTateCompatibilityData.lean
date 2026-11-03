/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar
public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing

/-! # Comparison maps for dual and Tate compatibility

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius/
prop-pod-dual-tate-data-compatibility.md and proof Steps 1--5
(blueprint: prop-pod-dual-tate-data-compatibility).
(blueprint: def-pod-dual-tate-comparison-data).

The equations use the actual evaluation, root-normalized Tate data, normalized
smooth exceptional inverse image, and evaluation-transpose scalar comparisons.

## Main declarations

* `omegaDatum` and `verdierDatum` give the specified exceptional and closed data.
* `scalarTate` and `scalarOmega` give canonical coefficient-comparison arrows.
The proposition is stated and assembled in `Sheaf.Paper.DualTateCompatibility`.

The target of the orientation comparison is written K-dual tensor Lambda(d)[2d];
the native tensor/shift comparison identifies it with K-dual(d)[2d].
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.CondensedDualTateCompatibility

variable (P : CondensedPoincareDualityConventions.{u})

/-- The existing geometric Frobenius, with its scheme carrier exposed.
Source: Step 1 (blueprint: prop-pod-dual-tate-data-compatibility). -/
abbrev geometric : P.X ≅ P.X :=
  ⟨(P.datum.geometricFrobenius P.X₀).hom, (P.datum.geometricFrobenius P.X₀).inv,
    (P.datum.geometricFrobenius P.X₀).hom_inv_id,
    (P.datum.geometricFrobenius P.X₀).inv_hom_id⟩

variable (c : Coefficient P.ell)

local notation "Fr" => StrictWeilCondensed.action (c.obj P.ell) (geometric P)
local notation "L" => c.derivedLine P.ell P.X P.dimension
local notation "Smooth" => c.smoothSource P.ell P.structureMap P.dimension

/-- The existing normalized smooth right adjoint evaluated at the coefficient unit.
Source: Step 4, omega = Ra^! Lambda (blueprint: prop-pod-dual-tate-data-compatibility). -/
abbrev omega : c.derived P.ell P.X := (Smooth).obj (𝟙_ _)

/-- The canonical orientation, with no extra orientation supplied by the caller.
Source: Step 4, eta = gamma^-1 at the unit
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def orientation : omega P c ≅ L :=
  smoothTraceUnitSource P.ell c P.datum P.smoothIndex

/-- Positive root coordinates identify the native Tate line with the purity line.
Source: Step 4, the shift of the twisted datum
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def lineCoordinates :
    L ≅ (StrictWeilCondensed.derivedTateLine P.ell c P.X (P.dimension : ℤ)) ⟦
      2 * (P.dimension : ℤ)⟧ :=
  (shiftFunctor _ (2 * (P.dimension : ℤ))).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      (StrictWeilCondensed.tateLine_identification P.ell c P.X (P.dimension : ℤ))).symm

/-- The residue-field unit condition follows from ell different from p.
Source: Tate-line hypothesis in Step 3
(blueprint: prop-pod-dual-tate-data-compatibility). -/
instance primeInvertible (x : P.X) : Invertible (P.ell : P.X.residueField x) :=
  IsUnit.invertible (by
    simpa using (primeUnit P.datum P.ell P.different).map
      (P.structureMap.residueFieldAlgebraMap x))

/-- The shift of the existing root-normalized tau_d, in purity-line coordinates.
Source: Step 4 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def lineDatum : (Fr).obj L ≅ L :=
  (Fr).mapIso (lineCoordinates P c) ≪≫
    ((Fr).commShiftIso (2 * (P.dimension : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (P.dimension : ℤ))).mapIso
      (StrictWeilCondensed.tateDatum P.ell c (geometric P) (P.dimension : ℤ)) ≪≫
    (lineCoordinates P c).symm

/-- Shift a specified datum using the canonical exact-pullback/shift comparison.
Source: Step 4 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def shiftDatum (K : c.derived P.ell P.X) (phi : (Fr).obj K ≅ K) (n : ℤ) :
    (Fr).obj (K⟦n⟧) ≅ K⟦n⟧ :=
  ((Fr).commShiftIso n).app K ≪≫ (shiftFunctor _ n).mapIso phi

/-- Pullback of the point-unit datum, using the canonical pullback-square comparison.
Source: Step 4, exceptional datum of the point unit
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def pulledUnitDatum : (Fr).obj
    ((upperStar (c.obj P.ell) P.structureMap).leftDerivedFunctor.obj (𝟙_ _)) ≅
      (upperStar (c.obj P.ell) P.structureMap).leftDerivedFunctor.obj (𝟙_ _) := by
  let := Fintype.ofFinite P.datum.k₀
  exact (leftDerivedUpperStarIsoMapDerivedCategory (c.obj P.ell) (geometric P).hom).symm.app _ ≪≫
    (pullbackSquareComparison (c.obj P.ell)
      (show CommSq (geometric P).hom P.structureMap P.structureMap
          (StrictWeilCondensed.pointFrobenius P.datum).hom from
        ⟨(P.datum.galoisMap_projections P.X₀.hom
          (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.datum.k₀ P.datum.k)).2⟩)
      ).symm.app (𝟙_ _) ≪≫
    (upperStar (c.obj P.ell) P.structureMap).leftDerivedFunctor.mapIso
      (leftDerivedUpperStarUnitIso (c.obj P.ell)
        (StrictWeilCondensed.pointFrobenius P.datum).hom)

/-- Exceptional datum in the normalized explicit smooth right-adjoint presentation.
Here gamma is the counit-preserving identification with this right adjoint, so the
three-factor smooth exchange is the independent pullback/tensor/shift comparison.
It is formed before applying the orientation at the coefficient unit.
Source: Step 4 and def-pur-tate-datum
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def omegaDatum : (Fr).obj (omega P c) ≅ omega P c :=
  StrictWeilCondensed.tensorDatum (c.obj P.ell) (geometric P)
    (pulledUnitDatum P c) (lineDatum P c)

/-- Evaluation-transpose datum on RHom(K,omega), with phi_K inverse in the first slot.
Source: Step 4, the displayed RHom(phi_K^-1,phi^!) c composite
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def verdierDatum (K : c.derived P.ell P.X) (phi : (Fr).obj K ≅ K) :
    (Fr).obj ((ihom K).obj (omega P c)) ≅ (ihom K).obj (omega P c) :=
  Functor.Monoidal.ihomObjIso Fr K (omega P c) ≪≫
    (ihom ((Fr).obj K)).mapIso (omegaDatum P c) ≪≫
    (MonoidalClosed.internalHom.mapIso phi.symm.op).app (omega P c)

/-- The exact canonical identification of thm-sf-dual-perfect, using the recorded
orientation and inverse twist interchange, without a freely chosen duality isomorphism.
Source: Step 4 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def dualityIso (hL : IsInvertible L) (K : c.derived P.ell P.X) :
    (ihom K).obj (omega P c) ≅ (ihom K).obj (𝟙_ _) ⊗ L :=
  ihomIsoIhomUnitTensor (orientation P c).symm hL K

/-- The canonical comparison from this tensor coordinate to K-dual(d)[2d].
Source: Step 4, final shift sentence
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def shiftedTwistCoordinates (K : c.derived P.ell P.X) :
    (ihom K).obj (𝟙_ _) ⊗ L ≅
      ((ihom K).obj (𝟙_ _) ⊗
        StrictWeilCondensed.derivedTateLine P.ell c P.X (P.dimension : ℤ)) ⟦
          2 * (P.dimension : ℤ)⟧ :=
  tensorIso (Iso.refl _) (lineCoordinates P c) ≪≫
    ((tensorLeft ((ihom K).obj (𝟙_ _))).commShiftIso (2 * (P.dimension : ℤ))).app _

section Scalar

variable {c} (c' : Coefficient P.ell)
  (a : c.bundled.{u} P.ell ⟶ c'.bundled P.ell)
  (ha : c.integralMap P.ell ≫ a.hom.hom = c'.integralMap P.ell)

local notation "Sc" => scalarSixChange a P.X
local notation "FrTarget" => StrictWeilCondensed.action (c'.obj P.ell) (geometric P)

/-- Pullback comparison pi = TP to PT, including semilinear geometric Frobenius.
Source: Step 5 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarFrobenius : Fr ⋙ Sc ≅ Sc ⋙ FrTarget :=
  scalarPullbackIso a (geometric P).hom

/-- The specified transported datum, pi inverse followed by Sc(phi).
Source: Step 5 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarDatum (K : c.derived P.ell P.X) (phi : (Fr).obj K ≅ K) :
    (FrTarget).obj ((Sc).obj K) ≅ (Sc).obj K :=
  ((scalarFrobenius P c' a).app K).symm ≪≫ (Sc).mapIso phi

/-- The ordinary positive-power scalar comparison, fixed by scalar association on
roots and the unit/tensor recursion; includes degree zero.
Source: Step 5 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarPositiveLine (d : ℕ) :
    (Mod.extendScalars
      (coefficientMap (Λ := c.obj P.ell) (Λ' := c'.obj P.ell) a.hom.hom P.X)).obj
        (c.line P.ell P.X d) ≅ c'.line P.ell P.X d := by
  letI := Mod.extendScalarsMonoidal
    (coefficientMap (Λ := c.obj P.ell) (Λ' := c'.obj P.ell) a.hom.hom P.X)
  induction d with
  | zero => exact (Functor.Monoidal.εIso _).symm
  | succ d ih =>
    exact (Functor.Monoidal.μIso _ _ _).symm ≪≫
      tensorIso ih (scalarFirst P.ell a ha P.X)

set_option maxHeartbeats 1200000 in
-- The signed branch elaborates the closed structure on the internal-module categories.
/-- Signed scalar line map on the existing presentation. Negative powers use the
closed evaluation transpose followed by the inverse positive-power comparison.
Source: Step 5, coefficient-independent roots and their duals
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarPresentationLine (r : ℤ) :
    (Mod.extendScalars (coefficientMap (Λ := c.obj P.ell) (Λ' := c'.obj P.ell) a.hom.hom P.X)).obj
        (StrictWeilCondensed.presentationLine P.ell c P.X r) ⟶
      StrictWeilCondensed.presentationLine P.ell c' P.X r := by
  letI := Mod.extendScalarsMonoidal
    (coefficientMap (Λ := c.obj P.ell) (Λ' := c'.obj P.ell) a.hom.hom P.X)
  cases r with
  | ofNat n => exact (scalarPositiveLine P c' a ha n).hom
  | negSucc n =>
    exact ihomUnitComparison (Mod.extendScalars
        (coefficientMap (Λ := c.obj P.ell) (Λ' := c'.obj P.ell) a.hom.hom P.X))
        (c.line P.ell P.X (n + 1)) ≫
      (pre (scalarPositiveLine P c' a ha (n + 1)).inv).app (𝟙_ _)

/-- Ordinary signed scalar map on the actual Tate sheaf, retaining its canonical
identification with the root-power presentation.
Source: Step 5 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarOrdinaryTate (r : ℤ) :=
  (Mod.extendScalars (coefficientMap (Λ := c.obj P.ell) (Λ' := c'.obj P.ell) a.hom.hom P.X)).map
      (StrictWeilCondensed.tateLine_identification P.ell c P.X r).hom ≫
    scalarPresentationLine P c' a ha r ≫
    (StrictWeilCondensed.tateLine_identification P.ell c' P.X r).inv

set_option maxHeartbeats 1200000 in
-- The two derived adjunctions and their single-functor comparisons need extra elaboration.
/-- The specified derived signed Tate comparison, adjunct to its ordinary scalar map.
This construction allows nonflat finite reduction.
Source: Step 5 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarTate (r : ℤ) :
    (Sc).obj (StrictWeilCondensed.derivedTateLine P.ell c P.X r) ⟶
      StrictWeilCondensed.derivedTateLine P.ell c' P.X r :=
  let alpha : condensedRingObj (c.obj P.ell) P.X ⟶
      condensedRingObj (c'.obj P.ell) P.X :=
    coefficientMap (Λ := c.obj P.ell) (Λ' := c'.obj P.ell) a.hom.hom P.X
  let M := StrictWeilCondensed.tateLine P.ell c P.X r
  let M' := StrictWeilCondensed.tateLine P.ell c' P.X r
  ((Mod.derivedExtendMapDerivedCategoryAdjunction alpha).homEquiv
    ((DerivedCategory.singleFunctor _ 0).obj M)
    ((DerivedCategory.singleFunctor _ 0).obj M')).symm
      ((DerivedCategory.singleFunctor _ 0).map
        (((Mod.extendRestrictAdjunction alpha).homEquiv M M')
          (scalarOrdinaryTate P c' a ha r)) ≫
        ((Mod.comap (C := Sheaf (Scheme.ProEt.topology P.X) Ab.{u + 1})
          alpha).mapDerivedCategorySingleFunctor 0).inv.app M')

/-- The shifted scalar comparison of the positive purity line.
Source: Step 5 (blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarShiftedLine : (Sc).obj L ⟶ c'.derivedLine P.ell P.X P.dimension :=
  scalarLineMap P.ell a P.X P.dimension (scalarPositiveLine P c' a ha P.dimension)

set_option maxHeartbeats 1200000 in
-- The scalar pullback and derived tensor comparisons elaborate large coefficient types.
/-- The exceptional coefficient map in the normalized explicit smooth presentation.
The scalar pullback, tensor and shifted root-line maps are the specified ones;
this is the scalar exceptional mate under the normalized smooth adjunctions.
Source: Step 5 and det-prop-scalar-six-exceptional
(blueprint: prop-pod-dual-tate-data-compatibility). -/
def scalarOmega : (Sc).obj (omega P c) ⟶ omega P c' := by
  letI := scalarSixChangeMonoidal a P.s
  exact (scalarSixTensorIso a P.X _ _).hom ≫
    ((((Sc).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory (c.obj P.ell) P.structureMap).app _)
      ≪≫ (scalarPullbackIso a P.structureMap).app _ ≪≫
        ((leftDerivedUpperStarIsoMapDerivedCategory (c'.obj P.ell) P.structureMap).app
          _).symm).hom ≫
        (upperStar (c'.obj P.ell) P.structureMap).leftDerivedFunctor.map
          (Functor.Monoidal.εIso (scalarSixChange a P.s)).inv) ⊗ₘ
      scalarShiftedLine P c' a ha)

end Scalar

end WeilConjectures.CondensedDualTateCompatibility
