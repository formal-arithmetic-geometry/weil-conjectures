/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import Sheaf.TraceFormula.FlatFibreComponentClosureDimension
import Sheaf.TraceFormula.GenusZeroSmoothProperLine
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler
import Sheaf.SixFunctors.TraceFormula.NodalGeometricFibresReduced
import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction
import Sheaf.RingTheory.ProjectiveOverLocalFree
import Sheaf.AlgebraicGeometry.ProperNormalGeometricConnectedness
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.SepClosedValuationGeometricComponents
import Sheaf.TraceFormula.ValuationCurveProjectivePreparation
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Specialization of an exceptional component

Source: Temkin, Stable modification of relative curves, Lemma 4.4.4, proof after
normalizing the target, and Lemma 4.4.2, printed pp. 30--32
(blueprint: lem-trf-exceptional-component-specialization).

Reduced closed immersions with the prescribed image represent the reduced induced
structures, by `Scheme.IdealSheafData.reduced_induced_closed_subscheme`. The inverse image
of a component's image under the geometric-fibre projection is precisely its geometric
support. This expresses its intersection with the marking and singular locus using the
shared `MultipointedCurve.specialPoints`, without choosing a component parametrization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Temkin

/-- An exceptional component has an exceptional component in each nonempty specialized
fibre of its reduced closure. Source: Temkin, Lemma 4.4.4, after normalizing the target,
and Lemma 4.4.2, printed pp. 30--32
(blueprint: lem-trf-exceptional-component-specialization).

Proof plan, following the node:
1. For `t = s`, use the given component. Otherwise nodal geometric fibres are reduced
   (lem-trf-nodal-geometric-fibres-reduced). The finite normalization furnished by
   lem-trf-valuation-curve-projective-preparation is an eta-modification, hence an
   isomorphism by lem-trf-geometrically-reduced-eta-normal. The valuation base is normal:
   an integral element outside a valuation ring has its inverse inside, and its monic
   equation then expresses the element inside. Thus Y is normal. Its component closure
   lies above the finite quasi-finite modification locus M in the target X.
2. A component B of the prescribed nonempty closure fibre has dimension one by
   lem-trf-flat-fibre-component-closure-dimension, hence is a whole component of Y_t.
   Its image in M_t is a point x. Localize the valuation ring at t and use
   lem-trf-valuation-curve-projective-preparation to shrink about x, compactify the normal
   target and extend the modification by the identity. No point at infinity enters the
   component closure, since the modification locus stays closed. Pass to the valuation
   quotient with generic point s and closed point t. Its fraction field is separably
   closed by lem-trf-sepclosed-valuation-geometric-components.
3. Semistability and the marking pull back by lem-trf-semistable-marked-base-change.
   Apply lem-trf-nodal-generic-component-closure to the proper closure H of C and its
   preserved semistable neighbourhood. H is integral, proper, flat and finitely presented,
   with nodal geometrically reduced fibres and entire ambient fibre components. Its
   boundary and marking are finite etale, with constant total geometric count d. Since
   the generic component is a projective line without self-nodes, its special-point bound
   gives d at most two.
4. By lem-pc-rf-perfect-base-change the structure-sheaf direct image is perfect and
   computes fibre cohomology. By def-pc-perfect-complex and lem-trf-projective-over-local-free
   it has a bounded finite-free representative over the local base. The alternating sum
   of ranks is constant. The generic projective line has h0 = 1, h1 = 0 by
   lem-sc-p1-monomial; higher cohomology vanishes by
   lem-sc-noetherian-cohomology-above-dimension and lem-weil-pbc-finite-type-over-noetherian.
   Thus the geometric special fibre F of H has Euler characteristic one.
5. The valuation quotient and its localizations are integrally closed by the argument
   in step 1. H dominates this normal integral base, and its proper geometrically integral
   generic fibre has only scalar global functions by lem-pc-h0-proper-variety. Apply
   lem-trf-proper-normal-geometric-connectedness: F is nonempty and connected.
6. Apply lem-trf-nodal-normalization-adjunction and
   lem-trf-nodal-curve-normalization-euler. Euler characteristic one gives zero as the
   sum of the dual graph's first Betti number and the normalization genera. A spanning
   tree shows each term is nonnegative; thus the graph is a tree and all genera vanish.
   By lem-trf-genus-zero-smooth-proper-line all normalized components are projective lines.
   There are no self-nodes, so the components themselves are projective lines.
7. If there is only one component it has at most two special points. Otherwise choose
   a leaf carrying at most one of the at most two external marking and boundary points:
   two leaves exist, so one works. Its one internal node gives at most two special points
   in the original geometric fibre, by the boundary identification in step 3.
8. Descend this component by lem-trf-sepclosed-valuation-geometric-components, using
   geometric reducedness from lem-trf-nodal-geometric-fibres-reduced. It lies in W_t and
   is contracted, since an irreducible subset of the finite zero-dimensional M_t is a
   singleton. Its projective-line and special-point properties are those of step 7.
   Closedness of the image point in the whole target is never needed. -/
theorem exceptional_component_specialization
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)]
    (X Y : MultipointedCurve (Spec (.of V)))
    (hX : Smooth (pullback.snd X.x (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hD : Etale (pullback.snd X.d (Spec.map (CommRingCat.ofHom V.toSubring.subtype))))
    (hnormal : ∀ x : X.X,
      IsDomain (X.X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.X.presheaf.stalk x))
    (f : Y.Hom X)
    (hf : f.IsEtaModification (Spec.map (CommRingCat.ofHom V.toSubring.subtype)))
    (hY : Y.IsSemistable)
    (s : Spec (.of V)) (C : Scheme.{u}) (i : C ⟶ Y.x.fiber s)
    [IsReduced C] [IsClosedImmersion i]
    (hC : Set.range i ∈ irreducibleComponents (Y.x.fiber s))
    (z : Y.x.fiber s) (hz : IsGenericPoint z (Set.range i))
    (W : Scheme.{u}) (w : W ⟶ Y.X) [IsReduced W] [IsClosedImmersion w]
    (hW : Set.range w = closure ({Y.x.fiberι s z} : Set Y.X))
    (hcontract : (Set.range (i ≫ Y.x.fiberι s ≫ f.curve)).Subsingleton)
    (hline : ∃ e :
      ProjectiveLine (Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField s)))) ≅
        pullback (i ≫ Y.x.fiberToSpecResidueField s)
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((Spec (.of V)).residueField s)
              (AlgebraicClosure ((Spec (.of V)).residueField s))))),
      e.hom ≫ pullback.snd _ _ =
        ProjectiveLine (Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField s)))) ↘
          Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField s))))
    (hpoints :
      ((pullback.fst Y.x (Orgogozo.geometricPoint (Spec (.of V)) s)) ⁻¹'
        Set.range (i ≫ Y.x.fiberι s) ∩ Y.specialPoints s).encard ≤ 2)
    (t : Spec (.of V)) (ht : t ∈ closure ({s} : Set (Spec (.of V))))
    (hne : Nonempty ((w ≫ Y.x).fiber t)) :
    ∃ (Cₜ : Scheme.{u}) (iₜ : Cₜ ⟶ Y.x.fiber t),
      IsReduced Cₜ ∧ IsClosedImmersion iₜ ∧
      Set.range iₜ ∈ irreducibleComponents (Y.x.fiber t) ∧
      Set.range iₜ ⊆ (Y.x.fiberι t) ⁻¹' Set.range w ∧
      (Set.range (iₜ ≫ Y.x.fiberι t ≫ f.curve)).Subsingleton ∧
      (∃ e :
        ProjectiveLine (Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField t)))) ≅
          pullback (iₜ ≫ Y.x.fiberToSpecResidueField t)
            (Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec (.of V)).residueField t)
                (AlgebraicClosure ((Spec (.of V)).residueField t))))),
        e.hom ≫ pullback.snd _ _ =
          ProjectiveLine (Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField t)))) ↘
            Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField t)))) ∧
      ((pullback.fst Y.x (Orgogozo.geometricPoint (Spec (.of V)) t)) ⁻¹'
        Set.range (iₜ ≫ Y.x.fiberι t) ∩ Y.specialPoints t).encard ≤ 2 := by
  sorry

end AlgebraicGeometry.Temkin
