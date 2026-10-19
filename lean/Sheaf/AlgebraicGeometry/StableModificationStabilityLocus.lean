/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement
public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.SemistableMultipointedPair
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Constructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
import Sheaf.TraceFormula.RiemannZariskiLocalColimit
import Sheaf.TraceFormula.StableModificationConstructibility
import Sheaf.TraceFormula.StableModificationStabilityFieldDescent

/-! # Constructible stable locus and dense isomorphism open for a spread modification

Source: Temkin, *Stable modification of relative curves*, Lemma 5.1(ii), Remark 3.1.1(ii),
and the second paragraph of the proof of Theorem 1.5, pp. 34--36
(blueprint: lem-trf-stable-modification-stability-locus).

The auxiliary base-change records below retain the canonical fibre-product pair and map while
allowing the existing `MultipointedCurve.Hom` and its stability predicate to be used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A multipointed-curve presentation of the canonical base change of a pair.
Source: Temkin §1.2 and the base-change construction in the proof of Theorem 1.5
(blueprint: lem-trf-stable-modification-stability-locus). -/
structure MultipointedCurve.BaseChange {T S : Scheme.{u}} (P : MultipointedCurve T)
    (s : S ⟶ T) where
  curve : MultipointedCurve S
  asPair : MultipointedPair.ofCurve curve = (MultipointedPair.ofCurve P).baseChange s

/-- A morphism between chosen presentations of canonical base changes, retaining the canonical
pullback maps on the curve and marking. Source: Temkin §1.2
(blueprint: lem-trf-stable-modification-stability-locus). -/
structure MultipointedCurve.BaseChangeHom {T S : Scheme.{u}}
    {P Q : MultipointedCurve T} (f : P.Hom Q) (s : S ⟶ T)
    (P' : P.BaseChange s) (Q' : Q.BaseChange s) where
  hom : P'.curve.Hom Q'.curve
  curve_eq : HEq hom.curve
    ((Over.pullback s).map
      (Over.homMk (U := Over.mk P.x) (V := Over.mk Q.x) f.curve f.curve_over)).left
  marking_eq : HEq hom.marking
    ((Over.pullback s).map
      (Over.homMk (U := Over.mk P.d) (V := Over.mk Q.d) f.marking f.marking_over)).left

/-- Constructibility of the stable fibre locus and existence of a quasi-model on which a given
valuation-centred stable modification spreads, with a dense open isomorphism locus.
Source: Temkin, *Stable modification of relative curves*, Lemma 5.1(ii), Remark 3.1.1(ii),
and the second paragraph of the proof of Theorem 1.5, pp. 34--36
(blueprint: lem-trf-stable-modification-stability-locus).

Proof (deferred), following the seven DAG steps:
1. On a nonempty affine open of U₀, the principal opens of nonzero functions have limit
   Spec k(U₀). Apply `thm-pd-spreading-out` (2) to both generic inverse maps and (3) to
   their inverse identities. Obtain one generic-containing base open W₀ on whose full
   preimages both maps are isomorphisms. Use `lem-weil-pbc-finite-type-over-noetherian`
   for Noetherianity of U₀ and its finite-type quasi-models. The hypotheses over Spec L
   express the same generic conditions: smoothness, etaleness and isomorphisms descend
   along the faithfully flat field extension k(U₀) → L.
2. Integrality makes W₀ schematically dense; Noetherianity makes its immersion qcqs.
   Apply `lemma-nagata-dense-flat-pullback` to the flat curve and marking structure maps.
   Their preimages of W₀ are schematically dense. The same argument applies to the
   source pair, so both source and target opens are schematically dense as required by
   `IsEtaModification`. Properness and the generic isomorphisms give an eta-modification.
3. Apply `lem-trf-stable-modification-constructibility` to obtain a constructible set C
   of semistable fibres with no exceptional component. For every point of Spec V, its
   fibre is a field extension of the fibre at its image in U₀. The hypothesis over V
   and `lem-trf-stable-modification-stability-field-descent` put every such image in C.
4. Choose an affine open A₀ containing the valuation centre; Spec V factors through it.
   Restrict C using `lem-weil-pbc-constructible-open-restriction`. On the Noetherian
   affine A₀, `def-weil-constructible-subset` gives a finite Boolean expression in
   principal opens. Pull it back to centre local rings of affine centred quasi-models.
   By `lem-trf-riemann-zariski-local-colimit` their affine limit is Spec V. Apply
   `lem-weil-pbc-limit-contained-in-constructible` (05F4) to get a centre local spectrum
   whose entire image lies in C. Its stages are qcqs and all transitions are affine.
5. Write the chosen quasi-model as Spec B with centre p. The inverse image of C is
   constructible by the same finite Boolean expression. The principal neighbourhoods
   D(f), f ∉ p, have limit Spec B_p. Apply 05F4 a second time to obtain D(f) mapping
   entirely into C. The local map B_p → V sends f to a unit, so the lift factors through
   U = D(f). This is an integral separated finite-type L-quasi-model through the centre,
   with its specified map from Spec L.
6. Use `lem-trf-semistable-marked-base-change` for multipointedness and the generic
   smooth/etale conditions, and `lem-weil-pbc-proper-base-change` for properness.
   `lem-trf-stable-modification-stability-field-descent` gives nodality and geometric
   stability at every point of U. Flatness, finite presentation and
   `lem-sbc-flat-fibre-etale-neighbourhoods` give an etale structural marking.
   `lem-trf-smooth-at-point-fibre-criterion` puts it in the relative smooth locus.
7. Pull W₀ back to U. This open contains the generic point and is dense. Integrality
   makes it schematically dense and Noetherianity makes its immersion qcqs. Apply
   `lemma-nagata-dense-flat-pullback` to both flat target maps, and also to both flat
   source maps, to obtain the dense opens in `IsEtaModification`, even for an empty
   marking. The two maps are isomorphisms there by Step 1 and fibre-product associativity.
   Steps 6 and 7 give `IsStable`; the base open is the final requested open.
   The factorization respects Spec L, so `lem-trf-riemann-zariski-finite-refinement`
   identifies its valuation point with the original x under the open injection.

The two presentation records fix the underlying pairs and induced maps, rather than
choosing arbitrary morphisms. The constructibility, centre-colimit and field-descent
DAG inputs remain deferred until their own stage-2 declarations are available.
-/
theorem stable_modification_stability_locus
    (U₀ : Scheme.{u}) [IsIntegral U₀]
    (t₀ : U₀ ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType t₀]
    [QuasiCompact t₀]
    (L : Type u) [Field L] [Algebra U₀.functionField L] [IsSepClosure U₀.functionField L]
    (x : RiemannZariski.ValuationPoint U₀ L
      (Spec.map (CommRingCat.ofHom (algebraMap U₀.functionField L)) ≫
        U₀.fromSpecStalk (genericPoint U₀)))
    (X Y₀ : MultipointedCurve U₀)
    (g : Y₀.Hom X)
    [IsProper g.curve] [IsProper g.marking]
    (hX : Smooth (pullback.snd X.x (Spec.map
      (CommRingCat.ofHom (algebraMap U₀.functionField L)) ≫
        U₀.fromSpecStalk (genericPoint U₀))))
    (hD : Etale (pullback.snd X.d (Spec.map
      (CommRingCat.ofHom (algebraMap U₀.functionField L)) ≫
        U₀.fromSpecStalk (genericPoint U₀))))
    (hηcurve : IsIso (g.curveBaseChange
      (Spec.map (CommRingCat.ofHom (algebraMap U₀.functionField L)) ≫
        U₀.fromSpecStalk (genericPoint U₀))))
    (hηmark : IsIso (g.markingBaseChange
      (Spec.map (CommRingCat.ofHom (algebraMap U₀.functionField L)) ≫
        U₀.fromSpecStalk (genericPoint U₀))))
    (hV : ∃ (P' : Y₀.BaseChange x.centre) (Q' : X.BaseChange x.centre)
      (f' : MultipointedCurve.BaseChangeHom g x.centre P' Q'),
      f'.hom.IsStable (Spec.map (CommRingCat.ofHom x.V.subtype)) ∧
        IsProper f'.hom.curve ∧ IsProper f'.hom.marking) :
    ∃ (U : RiemannZariski.QuasiModel U₀ L
        (Spec.map (CommRingCat.ofHom (algebraMap U₀.functionField L)) ≫
          U₀.fromSpecStalk (genericPoint U₀)))
      (l : Spec (.of x.V) ⟶ U.X),
      l ≫ U.map = x.centre ∧
        Spec.map (CommRingCat.ofHom x.V.subtype) ≫ l = U.generic ∧
      ∃ (P' : Y₀.BaseChange U.map) (Q' : X.BaseChange U.map)
        (f' : MultipointedCurve.BaseChangeHom g U.map P' Q'),
        f'.hom.IsStable U.generic ∧
          ∃ V : U.X.Opens, genericPoint U.X ∈ V ∧
            IsIso (f'.hom.curveBaseChange V.ι) ∧
            IsIso (f'.hom.markingBaseChange V.ι) := by
  sorry

end AlgebraicGeometry
