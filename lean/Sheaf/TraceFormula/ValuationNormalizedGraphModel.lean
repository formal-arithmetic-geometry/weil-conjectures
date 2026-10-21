/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.TraceFormula.ValuationHorizontalCurveModels
public import Sheaf.TraceFormula.Modification
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.TraceFormula.FlatFiniteTypeDensePresentation
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.ProperNormalGeometricConnectedness
import Sheaf.TraceFormula.ValuationCurveProjectivePreparation
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Jacobson.Ring

/-!+# The normalized graph model of a valuation curve

Source: Temkin, *Stable modification of relative curves*, Lemma 4.4.1(i), p. 30,
and the last paragraph of the proof of Proposition 4.4.6, p. 33
(blueprint: lem-trf-valuation-normalized-graph-model).

The projective line has two homogeneous coordinates. The graph and its image use the
specified morphisms. The normalization is the integral closure in the normal generic
fibre; this agrees with integral closure in the product of component function fields.
In particular no integralness, connectedness, or nonemptiness of a curve is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Projection of the actual schematic graph image to `X`.
Source: Temkin, Proposition 4.4.6, p. 33
(blueprint: lem-trf-valuation-normalized-graph-model). -/
def relativeGraphImageProjection {T X Y : Scheme.{u}} (p : X ⟶ T) (f : Y ⟶ X)
    (u : Y ⟶ ℙ(ULift.{u} (Fin 2); T))
    (hu : u ≫ (ℙ(ULift.{u} (Fin 2); T) ↘ T) = f ≫ p) :
    (ProjectiveSpace.liftBaseChange f u hu.symm).image ⟶ X :=
  (ProjectiveSpace.liftBaseChange f u hu.symm).imageι ≫ (ℙ(ULift.{u} (Fin 2); X) ↘ X)

/-- The canonical inclusion of the specified generic fibre of the graph image.
Its relative normalization is the normalization in the component function fields
when this generic fibre is smooth and schematically dense.
Source: Temkin, Lemma 4.4.1(i), p. 30, and Proposition 4.4.6, p. 33
(blueprint: lem-trf-valuation-normalized-graph-model). -/
def relativeGraphImageGenericInclusion {T E X Y : Scheme.{u}} (p : X ⟶ T)
    (η : E ⟶ T) (f : Y ⟶ X) (u : Y ⟶ ℙ(ULift.{u} (Fin 2); T))
    (hu : u ≫ (ℙ(ULift.{u} (Fin 2); T) ↘ T) = f ≫ p) :
    pullback (relativeGraphImageProjection p f u hu ≫ p) η ⟶
      (ProjectiveSpace.liftBaseChange f u hu.symm).image :=
  pullback.fst _ _

/-- The normalized schematic graph image is an intermediate normal relative curve.
The two existential proof binders supply only the qcqs conditions needed to form
the actual integral-closure normalization. The morphism `q` is uniquely determined
by its factorization of the canonical map to the schematic image.

Source: Temkin, Lemma 4.4.1(i), p. 30; last paragraph of Proposition 4.4.6, p. 33;
Stacks, Tags 0AY8, 02UP, and 0AB1
(blueprint: lem-trf-valuation-normalized-graph-model).

Proof plan, following the node:
1. The finite chain of primes makes the generic point a principal quasi-compact
   open. Flatness makes it schematically dense, by
   lem-sc-flat-invertible-sections-torsion-free, also for the empty curve.
2. The graph is proper by lemma-nagata-projective-space-base-change-proper and
   lem-weil-pbc-proper-to-separated. The proper schematic-image theorem gives its
   image and proper projection to X (lem-weil-pbc-scheme-theoretic-image-proper).
3. Its affine rings inject into sections on the normal source, so are reduced and
   torsion-free over V. Use lem-trf-valuation-torsionfree-flat and
   lem-weil-pbc-flat-morphism-affine-criterion for flatness of the image.
4. By lemma-nagata-scheme-image-restrict-open the generic image is the closed
   graph of the smooth generic curve, and hence is that curve.
5. On standard projective charts the quotient module is finite type and V-flat;
   its generic restriction is finitely presented by Noetherianity. Apply
   lem-trf-flat-finite-type-dense-presentation and the standard-chart and qcqs
   permanence nodes to get finite presentation of the image.
6. Use lem-trf-flat-dense-generic-fibre-pure-dimension for pure relative dimension
   one. Thus the image is a reduced relative curve and h is an eta-modification.
7. Apply lem-trf-valuation-curve-projective-preparation to obtain its finite
   normalization, normal relative curve structure, and unique factorization q.
8. Set g = nu followed by p. Finiteness gives properness of g; proper-to-separated
   gives properness of q. Generic isomorphisms and flatness give both modifications
   and the equality q followed by g = f.
9. By lem-trf-valuation-horizontal-curve-models the curves have finitely many
   components, all meeting the generic fibre. The reduced-normal total-fractions
   criterion and finite affine coproduct-spectrum give normal integral affine covers.
10. Above each such target open the source is integral and its generic fibre has
   function algebra the target function field. All hypotheses of
   lem-trf-proper-normal-geometric-connectedness hold, giving connected geometric fibres.
11. The finite normalization preserves dimensions of reduced component images,
   by lem-sc-finite-surjective-dimension, so q contracts exactly what the graph does.
12. A constant graph has constant projections. Conversely, two zero-dimensional
   projection images are residue-field points; properness and the Zariski lemma
   make their residue fields finite over the base residue field. Their fibre
   product is zero-dimensional. This proves the contraction equivalence.
13. A zero-dimensional fibre is finite by the zero-dimensional closed-subscheme
   theorem. Use lem-trf-proper-finite-fibre-finite-near and then
   lem-trf-finite-birational-normal-iso on normal integral opens to get an
   isomorphism neighbourhood. The converse is immediate for an isomorphism.
14. Over an open where f is invertible, its graph is the normal open itself.
   Scheme-image restriction and finite-birational normal invertibility make both
   the normalization and q isomorphisms there. -/
theorem valuation_normalized_graph_model
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of V))
    (f : Y ⟶ X) (hX : RelativeCurve p) (hY : RelativeCurve (f ≫ p))
    (hnX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hsX : Smooth (pullback.snd p (Spec.map (CommRingCat.ofHom V.subtype))))
    (hsY : Smooth (pullback.snd (f ≫ p) (Spec.map (CommRingCat.ofHom V.subtype))))
    (hf : EtaModification (Spec.map (CommRingCat.ofHom V.subtype)) f p)
    (u : Y ⟶ ℙ(ULift.{u} (Fin 2); Spec (.of V)))
    (hu : u ≫ (ℙ(ULift.{u} (Fin 2); Spec (.of V)) ↘ Spec (.of V)) = f ≫ p) :
    IsReduced (ProjectiveSpace.liftBaseChange f u hu.symm).image ∧
    RelativeCurve (relativeGraphImageProjection p f u hu ≫ p) ∧
    ∃ (_ : QuasiCompact (relativeGraphImageGenericInclusion p
        (Spec.map (CommRingCat.ofHom V.subtype)) f u hu))
      (_ : QuasiSeparated (relativeGraphImageGenericInclusion p
        (Spec.map (CommRingCat.ofHom V.subtype)) f u hu)),
      IsFinite (relativeGraphImageGenericInclusion p
        (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization ∧
      (∀ z : (relativeGraphImageGenericInclusion p
          (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).normalization,
        IsDomain ((relativeGraphImageGenericInclusion p
          (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).normalization.presheaf.stalk z) ∧
        IsIntegrallyClosed ((relativeGraphImageGenericInclusion p
          (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).normalization.presheaf.stalk z)) ∧
      RelativeCurve ((relativeGraphImageGenericInclusion p
        (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization ≫
        relativeGraphImageProjection p f u hu ≫ p) ∧
      ∃ q : Y ⟶ (relativeGraphImageGenericInclusion p
          (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).normalization,
        q ≫ (relativeGraphImageGenericInclusion p
          (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization =
          (ProjectiveSpace.liftBaseChange f u hu.symm).toImage ∧
        (∀ q' : Y ⟶ (relativeGraphImageGenericInclusion p
            (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).normalization,
          q' ≫ (relativeGraphImageGenericInclusion p
            (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization =
            (ProjectiveSpace.liftBaseChange f u hu.symm).toImage → q' = q) ∧
        EtaModification (Spec.map (CommRingCat.ofHom V.subtype)) q
          ((relativeGraphImageGenericInclusion p
            (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization ≫
            relativeGraphImageProjection p f u hu ≫ p) ∧
        EtaModification (Spec.map (CommRingCat.ofHom V.subtype))
          ((relativeGraphImageGenericInclusion p
            (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization ≫
            relativeGraphImageProjection p f u hu) p ∧
        q ≫ (relativeGraphImageGenericInclusion p
          (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization ≫
          relativeGraphImageProjection p f u hu = f ∧
        (∀ z, GeometricallyConnected (q.fiberToSpecResidueField z)) ∧
        (∀ (s : Spec (.of V)) (A : Set ((f ≫ p).fiber s)),
          A ∈ irreducibleComponents ((f ≫ p).fiber s) →
          (topologicalKrullDim (q '' ((f ≫ p).fiberι s '' A)) = 0 ↔
            topologicalKrullDim (f '' ((f ≫ p).fiberι s '' A)) = 0 ∧
            topologicalKrullDim (u '' ((f ≫ p).fiberι s '' A)) = 0)) ∧
        (∀ z, (∀ W : ((relativeGraphImageGenericInclusion p
              (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).normalization).Opens,
            z ∈ W → ¬ IsIso (q ∣_ W)) ↔ 0 < topologicalKrullDim (q.fiber z)) ∧
        (∀ U : X.Opens, IsIso (f ∣_ U) →
          IsIso (q ∣_ (((relativeGraphImageGenericInclusion p
            (Spec.map (CommRingCat.ofHom V.subtype)) f u hu).fromNormalization ≫
            relativeGraphImageProjection p f u hu) ⁻¹ᵁ U))) := by
  sorry

end AlgebraicGeometry
