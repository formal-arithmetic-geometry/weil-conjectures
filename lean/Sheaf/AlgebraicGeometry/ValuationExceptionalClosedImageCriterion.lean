/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.SixFunctors.TraceFormula.NodalGeometricFibresReduced
import Sheaf.AlgebraicGeometry.SepClosedValuationGeometricComponents
import Sheaf.TraceFormula.ExceptionalComponentSpecialization
import Sheaf.TraceFormula.SemistableNormalTargetFactorization

/-! # Closed-image exceptional components detect stability

Source: Temkin, Stable modification of relative curves, Lemmas 4.2.2 and 4.4.4,
printed pp. 26--27 and 31--32
(blueprint: lem-trf-valuation-exceptional-closed-image-criterion).

The auxiliary definitions spell out the set and exceptional components introduced in this
statement. Reduced component structures are represented by reduced closed immersions with
the prescribed image, and the geometric inclusion is the canonical pullback map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical inclusion into the geometric fibre of a scheme in an ordinary fibre.
Source: Temkin §1.2, geometric base change of components
(blueprint: lem-trf-valuation-exceptional-closed-image-criterion). -/
def MultipointedCurve.geometricComponentInclusion {T : Scheme.{u}} (P : MultipointedCurve T)
    (t : T) {C : Scheme.{u}} (i : C ⟶ P.x.fiber t) :
    pullback (i ≫ P.x.fiberToSpecResidueField t)
        (Spec.map (CommRingCat.ofHom
          (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t))))) ⟶
      pullback P.x (Orgogozo.geometricPoint T t) :=
  pullback.lift
    (pullback.fst _ _ ≫ i ≫ P.x.fiberι t)
    (pullback.snd _ _)
    (by
      simp only [Category.assoc, P.x.fiber_fac, Orgogozo.geometricPoint]
      simpa only [Category.assoc] using
        (pullback.condition_assoc
          (f := i ≫ P.x.fiberToSpecResidueField t)
          (g := Spec.map (CommRingCat.ofHom
            (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t)))))
          (T.fromSpecResidueField t)))

/-- The set `B_f`: ordinary fibre-component generic points with image closed in the entire
original target. Source: Temkin §4.2 and Lemma 4.2.2
(blueprint: lem-trf-valuation-exceptional-closed-image-criterion). -/
def MultipointedCurve.Hom.closedImageFiberGenericPoints {T : Scheme.{u}}
    {P Q : MultipointedCurve T} (f : P.Hom Q) : Set P.X :=
  {z | IsClosed ({f.curve z} : Set Q.X) ∧
    ∃ (t : T) (c : P.x.fiber t),
      c ∈ genericPoints (P.x.fiber t) ∧ P.x.fiberι t c = z}

/-- Exceptionality of an ordinary fibre-component generic point: its reduced component is
contracted, its algebraic-closure base change is a projective line over that field, and its
geometric image has at most two marking or singular points. The reduced closed immersion
`i` has exactly the closure of the generic point as its image, so it represents the reduced
induced component, not an arbitrary parametrization or a normalization.
Source: Temkin §1.2 and Lemma 4.4.4
(blueprint: lem-trf-valuation-exceptional-closed-image-criterion). -/
def MultipointedCurve.Hom.IsExceptionalFiberGenericPoint {T : Scheme.{u}}
    {P Q : MultipointedCurve T} (f : P.Hom Q) (z : P.X) : Prop :=
  ∃ (t : T) (c : P.x.fiber t) (C : Scheme.{u}) (i : C ⟶ P.x.fiber t),
    c ∈ genericPoints (P.x.fiber t) ∧ P.x.fiberι t c = z ∧
    IsReduced C ∧ IsClosedImmersion i ∧ Set.range i = closure ({c} : Set (P.x.fiber t)) ∧
    (Set.range (i ≫ P.x.fiberι t ≫ f.curve)).Subsingleton ∧
    ∃ e : ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t)))) ≅
        pullback (i ≫ P.x.fiberToSpecResidueField t)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t))))),
      e.hom ≫ pullback.snd _ _ =
        ProjectiveLine (Spec (.of (AlgebraicClosure (T.residueField t)))) ↘
          Spec (.of (AlgebraicClosure (T.residueField t))) ∧
      (Set.range (P.geometricComponentInclusion t i) ∩ P.specialPoints t).encard ≤ 2

namespace Temkin

/-- Closed-image exceptional components detect stability, including finiteness of the
closed-image generic-point set and an explicit exceptional witness when stability fails.
Source: Temkin, Lemmas 4.2.2 and 4.4.4, printed pp. 26--27 and 31--32
(blueprint: lem-trf-valuation-exceptional-closed-image-criterion).

Proof plan:
1. The finite prime chain makes the base finite. Each fibre is finite type over a field
   by lem-sfb-finite-type-composition-base-change, hence Noetherian by
   lem-weil-pbc-finite-type-over-noetherian, and has finitely many components by
   lem-weil-pbc-noetherian-finitely-many-components. Generic points are unique in a scheme.
   Thus the union of their finite sets over the finite base, and its subset B_f, are finite.
2. Apply lem-trf-semistable-normal-target-factorization. It gives a normal target and a
   factor g of f with unchanged marked source and the same contracted ordinary and geometric
   components. Thus f and g have exactly the same exceptional components and stability.
3. If f is unstable, choose a geometric exceptional component for g. Its nodal fibre is
   geometrically reduced by lem-trf-nodal-geometric-fibres-reduced. The component descends
   to an ordinary component C by lem-trf-sepclosed-valuation-geometric-components. Its
   contraction, projective-line base change and special-point bound descend as stated.
4. Let W be the closure of its generic point in Y. Choose the most special point t in the
   nonempty finite-chain image of W. It specializes the original base point, and W_t is
   nonempty and closed in W, hence in Y; t need not be closed in the whole base.
5. Apply lem-trf-exceptional-component-specialization to the normal-target factor g, C and
   W_t. The exceptional component supplied in W_t is closed in Y. Transfer its contraction
   back to f by the factorization input. Properness of the original f makes its one-point
   image closed in the entire original X. Its generic point is an exceptional element of B_f.
6. Stable f has no geometric exceptional component, hence no exceptional element of B_f,
   using the component correspondence and geometric reducedness from step 3. Conversely
   step 5 contradicts absence of such points if f is unstable. This proves the equivalence
   and the particular consequence, together with finiteness from step 1. -/
theorem valuation_exceptional_closed_image_criterion
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)]
    (X Y : MultipointedCurve (Spec (.of V)))
    (hX : Smooth (pullback.snd X.x (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hD : Etale (pullback.snd X.d
      (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (f : Y.Hom X)
    (hf : f.IsEtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)))
    (hY : Y.IsSemistable) :
    f.closedImageFiberGenericPoints.Finite ∧
    (f.IsStable (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) ↔
      ∀ z ∈ f.closedImageFiberGenericPoints, ¬ f.IsExceptionalFiberGenericPoint z) ∧
    (¬ f.IsStable (Spec.map (CommRingCat.ofHom V.toSubring.subtype)) →
      ∃ z ∈ f.closedImageFiberGenericPoints, f.IsExceptionalFiberGenericPoint z) := by
  sorry

end Temkin

end AlgebraicGeometry
