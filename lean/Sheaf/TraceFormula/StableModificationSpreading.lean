/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.TraceFormula.MultipointedCurve
public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement
import Sheaf.AlgebraicGeometry.StableModificationFinitePresentationSpread
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.StableModificationStabilityLocus

/-!
# Spreading a prescribed stable valuation model

Source: Temkin, *Stable modification*, Lemma 3.2.2, §3.1 and Remark 3.1.1(ii),
Lemma 5.1(ii), and the second paragraph of the proof of Theorem 1.5, pp. 34--36
(blueprint: lem-trf-stable-modification-spreading).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A multipointed pair over `S` together with the canonical comparison maps to the
base change of a pair over `T`.  The comparison maps are isomorphisms and commute
with both structure maps and the marking inclusion.  Source: Temkin §3.1
(blueprint: lem-trf-stable-modification-spreading). -/
structure BaseChangePair {T S : Scheme.{u}} (P : MultipointedCurve T)
    (s : S ⟶ T) where
  pair : MultipointedCurve S
  curveMap : pair.X ⟶ pullback P.x s
  markingMap : pair.D ⟶ pullback P.d s
  curveIso : IsIso curveMap
  markingIso : IsIso markingMap
  curveOver : curveMap ≫ pullback.snd P.x s = pair.x
  markingOver : markingMap ≫ pullback.snd P.d s = pair.d
  inclusionOver : pair.i ≫ curveMap =
    markingMap ≫ pullback.map P.d s P.x s P.i (𝟙 S) (𝟙 T)
      ((Category.comp_id _).trans P.comm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)

attribute [instance] BaseChangePair.curveIso BaseChangePair.markingIso

/--
Source: Temkin, *Stable modification*, Lemma 3.2.2, §3.1 and Remark 3.1.1(ii),
Lemma 5.1(ii), and the second paragraph of the proof of Theorem 1.5, pp. 34--36
(blueprint: lem-trf-stable-modification-spreading).

Proof, following the four steps of the node:
1. Unpack the prescribed stable modification into the multipointed source, two proper
   maps, their marking compatibility and their isomorphisms over `Spec L`. Apply
   `lem-trf-stable-modification-finite-presentation-spread` to descend these data to
   an integral separated finite-type quasi-model `U₀`, retaining the valuation lift
   and the two isomorphisms identifying its pullback with the prescribed model.
2. The quasi-model `U₀` is finite type over the integers, and its function field is
   a finite separable subextension of `L/k(T)`, so `L` remains a separable closure
   of that field. Its generic map sends the generic point to that of `T`.
   Apply the generic clause of `lem-trf-semistable-marked-base-change` to obtain
   the multipointed target over `U₀` with smooth generic curve and etale marking.
   The identification in Step 1 makes the valuation pullback stable. Apply
   `lem-trf-stable-modification-stability-locus` to obtain a further quasi-model
   `U → U₀`, still admitting the valuation lift, on which the descended map is
   stable and both maps are isomorphisms over one dense base open containing the
   generic point. Compose with `U₀ → T`: integrality, separatedness, finite type
   and the generic factorization make `U` an `L`-quasi-model of `T`.
3. Associativity of fibre products identifies the pullback along `Spec V → U`
   with the pullback along the original lift to `U₀`. The isomorphisms from
   `lem-trf-stable-modification-finite-presentation-spread` preserve the structure
   maps and marking and recover both prescribed maps. The displayed equations
   after projection to `P.X` and `P.D`, together with the structure-map equations,
   express equality under the canonical iterated-pullback comparisons: the two
   projections jointly determine a morphism to each fibre product.
4. By `lem-trf-riemann-zariski-finite-refinement`, the compatible valuation lift
   says that the open `RZ_L(U)` contains `x`. The common base open contains the
   generic point, hence its inverse images in both source and target contain
   their entire generic fibres. These are all the claimed clauses; no global
   existence theorem for stable modifications is used.
-/
theorem stable_modification_spreading
    (T : Scheme.{u}) [IsIntegral T]
    (t : T ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType t] [QuasiCompact t]
    (L : Type u) [Field L] [Algebra T.functionField L] [IsSepClosure T.functionField L]
    (η : Spec (.of L) ⟶ T)
    (hη : η = Spec.map (CommRingCat.ofHom (algebraMap T.functionField L)) ≫
      T.fromSpecStalk (genericPoint T))
    (x : RiemannZariski.Point T L η)
    (v : RiemannZariski.ValuationPoint T L η)
    (hx : RiemannZariski.Corresponds x v)
    (P : MultipointedCurve T)
    (hgenX : Smooth (P.x.fiberToSpecResidueField (genericPoint T)))
    (hgenD : Etale (P.d.fiberToSpecResidueField (genericPoint T)))
    (PV : MultipointedCurve (Spec (.of v.V)))
    (QV : BaseChangePair P v.centre)
    (f : MultipointedCurve.Hom PV QV.pair)
    (hf : f.IsStable (Spec.map (CommRingCat.ofHom v.V.subtype))) :
    ∃ (U : RiemannZariski.QuasiModel T L η)
      (lift : Spec (.of v.V) ⟶ U.X),
      lift ≫ U.map = v.centre ∧
      Spec.map (CommRingCat.ofHom v.V.subtype) ≫ lift = U.generic ∧
      ∃ (Y : MultipointedCurve U.X) (QU : BaseChangePair P U.map)
        (g : MultipointedCurve.Hom Y QU.pair),
        g.IsStable U.generic ∧
        (∃ (eX : pullback Y.x lift ≅ PV.X) (eD : pullback Y.d lift ≅ PV.D),
          eX.hom ≫ PV.x = pullback.snd Y.x lift ∧
          eD.hom ≫ PV.d = pullback.snd Y.d lift ∧
          eD.hom ≫ PV.i = Y.markingBaseChange lift ≫ eX.hom ∧
          eX.hom ≫ f.curve ≫ QV.curveMap ≫ pullback.fst P.x v.centre =
            pullback.fst Y.x lift ≫ g.curve ≫ QU.curveMap ≫ pullback.fst P.x U.map ∧
          eD.hom ≫ f.marking ≫ QV.markingMap ≫ pullback.fst P.d v.centre =
            pullback.fst Y.d lift ≫ g.marking ≫ QU.markingMap ≫
              pullback.fst P.d U.map) ∧
        (∃ Uo : U.X.Opens,
          Dense (Uo : Set U.X) ∧ genericPoint U.X ∈ Uo ∧
          IsIso (g.curveBaseChange Uo.ι) ∧ IsIso (g.markingBaseChange Uo.ι)) ∧
        RiemannZariski.ValuationPoint.LiftsTo v U := by
  sorry

end AlgebraicGeometry
