/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure
public import Sheaf.AlgebraicGeometry.FunctorialFanDesingularization
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalizedBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Compactification.StrictTransform

import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation
import Sheaf.AlgebraicGeometry.ProjectiveBundleComposition
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent
import Sheaf.AlgebraicGeometry.LogBlowupNormalization
import Sheaf.AlgebraicGeometry.LogFanChartBlowup
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.TraceFormula.LogRegularToricRefinement
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # Fan-induced saturated log blowup regularization

Source: ILO, Travaux de Gabber, VIII Theorems 3.3.15 and 3.4.9, sections 3.4.5--3.4.8,
pp.107--112, and 5.3.11, p.126 (blueprint: lem-per-gabber-log-blowup-regularization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The fixed saturated smooth-functorial fan rule induces one strict-functorial regularization
rule on all Noetherian separated fs log regular schemes. Its chart condition retains the
actual lifted fan centers and contracts exactly whole-monoid centers. Ring centers are
characterized by their strict-local germs, rather than chosen unrelated ideals. All scheme
steps are componentwise normalized blowups, their normalization maps are finite without
excellence, and their maps and the composite are projective in the projective-bundle sense.
The entire tower is unchanged over the regular locus. Its strict comparisons are ordinary
scheme pullbacks and strict transforms, with the pulled ring centers in their original order.
Empty, disconnected, length-zero and integral inputs are all included.

Source: ILO VIII 3.3.15, 3.4.5--3.4.9, pp.107--112; 5.3.11, p.126
(blueprint: lem-per-gabber-log-blowup-regularization).

Proof plan:
1. Log regularity gives sharp fs characteristic charts by
   `lem-trf-log-regular-sharp-chart`; saturation and sharpness imply torsion-free completion.
   Fix R from `lem-trf-functorial-fan-desingularization`. Quasi-compactness replaces any
   chart fan by a finite union of affine localization neighborhoods. Face sharpening
   (`lem-trf-fs-face-sharpening`) gives the torsion-free stalks there. Lift R's ordered
   tower using `lem-trf-log-fan-chart-blowup`, and contract whole-monoid centers.
2. Compare charts by `lem-trf-strict-fan-chart-local-comparison`. Fan smooth functoriality
   identifies their localized ordered centers, and universal log blowups identify their
   lifts. The composition laws and finite-disjoint-union comparisons synchronize the
   finite tower. Apply `lem-trf-functorial-log-blowup-etale-descent` to descend it.
3. Inductively use `lem-trf-coherent-log-ideal-chart-construction` for the ring center,
   fine blowup and finite saturation map. The saturated fraction monoids retain the
   chart group completion, so `lem-trf-log-regular-toric-refinement` gives log regularity.
   The ring images of log sections are non-zero-divisors by
   `lem-trf-log-regular-divisorial-structure`. Thus `lem-trf-monomial-rees-chart-comparison`
   and `lem-trf-etale-blowup-chart-descent` identify the fine blowup with the ordinary one.
4. `lem-sfb-blowup-rees-symmetric-presentation` and
   `prop-nagata-relative-proj-functoriality` embed that blowup into the projective bundle
   of its finite-type ideal. Use `lem-trf-finite-projective-bundle` for saturation and
   `lem-sfb-projective-bundle-composition` for the stage and total maps. Projectivity
   implies properness by `lem-trf-projective-bundle-proper`, hence finite type; use
   `lem-weil-pbc-finite-type-over-noetherian` inductively for Noetherianity.
5. Normality and the dense triviality locus follow from the divisorial-structure lemma.
   `lem-trf-normal-topologically-noetherian-components` splits each stage into its finite
   disjoint normal integral components. `lem-trf-log-blowup-normalization` and
   `lem-trf-finite-normal-blowup-recognition` identify the finite saturation map with
   their function-field normalizations. Integral inputs retain integral stages and
   their inverse-image dense triviality opens, proving the stated birationality.
6. The terminal fan is smooth. Its stalks identify the terminal characteristics as free
   monoids. Apply `lem-trf-free-characteristic-regular-boundary` for terminal regularity.
7. At an originally regular point the same lemma gives a free characteristic chart.
   `lem-trf-monoid-chart-characteristic-fan` gives its free fan chart. Its smooth map to
   the point and fan functoriality make its contracted tower empty. Strict etale chart
   images are open by `lem-weil-pbc-etale-morphism-open-map`; these cover the regular
   locus, so all the stage composites are isomorphisms there.
8. For an arbitrary strict map, local chart comparison applies without etaleness.
   The same pulled centers and uniqueness of saturated blowups glue the ordered
   contraction comparison, including identities and composition and hence automorphisms.
9. On a strict affine chart the saturated chart rings on both sides are
   A tensor Z[Q_sat] over Z[P] and A' tensor Z[Q_sat] over Z[P]. The canonical
   coefficient tensor isomorphism identifies the second with base change of the first.
   It agrees on monomial-localization overlaps. Use `lem-weil-pbc-fpqc-descend-isomorphism`
   on a finite strict etale cover to obtain the ordinary scheme pullback at every step.
   The same formula pulls back each generator of the ring ideal. By the normalized
   blowup identification in Step 5 this is also the canonical strict transform.
-/
theorem exists_gabber_log_blowup_regularization
    (R : FineFan.SmoothFunctorialDesingularization.{u}) :
    ∃ (P : StrictLogBlowupProcedure IsLogRegularResolutionInput.{u})
      (J : ∀ (X : FineSaturatedLogScheme.{u}) (hX : IsLogRegularResolutionInput X)
        (i : Fin (P.tower X hX).tower.length),
        ((P.tower X hX).tower.level i.castSucc).scheme.IdealSheafData),
      (∀ (X : FineSaturatedLogScheme.{u}) (hX : IsLogRegularResolutionInput X)
        (F : FineFan.ResolutionInput.{u})
        (c : LogFanChart X ((R.resolution F).tower.level 0)),
        ∃ (L : LogFanTower (R.resolution F).tower) (h : L.level 0 = X),
          HEq (L.chart 0) c ∧ Nonempty (LogBlowupComparison (EtaleLogHom.id X)
            { tower :=
                { length := (R.resolution F).length
                  level := L.level
                  arrow := L.arrow
                  center := fun i ↦ (L.chart i.castSucc).pullbackIdeal
                    ((R.resolution F).tower.center i)
                  isBlowup := L.blowup }
              initial := h }
            (P.tower X hX))) ∧
      (∀ (X : FineSaturatedLogScheme.{u}) (hX : IsLogRegularResolutionInput X),
        IsRegularScheme ((P.tower X hX).tower.level
          (Fin.last (P.tower X hX).tower.length)).scheme ∧
        ((P.tower X hX).tower.level (Fin.last (P.tower X hX).tower.length)).IsLogRegular ∧
        (∀ i, IsNoetherian ((P.tower X hX).tower.level i).scheme ∧
          ∀ x : ((P.tower X hX).tower.level i).scheme,
            IsDomain (((P.tower X hX).tower.level i).scheme.presheaf.stalk x) ∧
            IsIntegrallyClosed (((P.tower X hX).tower.level i).scheme.presheaf.stalk x)) ∧
        (∀ i : Fin (P.tower X hX).tower.length,
          (∀ V : ((P.tower X hX).tower.level i.castSucc).scheme.affineOpens,
            ((J X hX i).ideal V).FG) ∧
          (∃ e : ((P.tower X hX).tower.level i.succ).scheme ≅ (J X hX i).normalizedBlowup,
            e.hom ≫ (J X hX i).normalizedBlowupMap = ((P.tower X hX).tower.arrow i).base) ∧
          IsFinite (J X hX i).blowup.fromReducedNormalization ∧
          IsProjectiveBundle ((P.tower X hX).tower.arrow i).base ∧
          ∀ (V : ((P.tower X hX).tower.level i.castSucc).scheme.affineOpens)
            (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (t : Spec (.of Ω) ⟶ ((P.tower X hX).tower.level i.castSucc).scheme)
            (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.1.ι)),
            ((J X hX i).ideal V).map
                ((strictLocalGerm _ t (Scheme.Etale.mk V.1.ι) w).hom.comp V.1.topIso.inv.hom) =
              Ideal.span
                (((P.tower X hX).tower.level
                  i.castSucc).logStructure.toEtalePrelogStructure.stalkAlpha t ''
                    ((P.tower X hX).tower.level i.castSucc).logStructure.idealStalk
                    ((P.tower X hX).tower.center i) t)) ∧
        IsProjectiveBundle ((P.tower X hX).toBase
          (Fin.last (P.tower X hX).tower.length)).base ∧
        (∀ x : X.scheme, IsRegularLocalRing (X.scheme.presheaf.stalk x) →
          ∃ U : X.scheme.Opens, x ∈ U ∧
            ∀ i, IsIso (((P.tower X hX).toBase i).base ∣_ U)) ∧
        (IsIntegral X.scheme →
          (∀ i, IsIntegral ((P.tower X hX).tower.level i).scheme) ∧
          ∃ U : X.scheme.Opens, Dense (U : Set X.scheme) ∧
            Dense ((((P.tower X hX).toBase
              (Fin.last (P.tower X hX).tower.length)).base ⁻¹ᵁ U :
                ((P.tower X hX).tower.level (Fin.last (P.tower X hX).tower.length)).scheme.Opens) :
                  Set ((P.tower X hX).tower.level
                    (Fin.last (P.tower X hX).tower.length)).scheme) ∧
            IsIso (((P.tower X hX).toBase
              (Fin.last (P.tower X hX).tower.length)).base ∣_ U))) ∧
      ∀ (X Y : FineSaturatedLogScheme.{u})
        (hX : IsLogRegularResolutionInput X) (hY : IsLogRegularResolutionInput Y)
        (f : EtaleLogHom Y X) (hf : f.IsStrict),
        (∀ i, IsPullback ((P.comparison hX hY f hf).step i).base
          ((P.comparison hX hY f hf).map i.succ).base
          ((P.comparison hX hY f hf).map i.castSucc).base
          ((P.tower X hX).tower.arrow i).base) ∧
        (∀ k, HEq ((J X hX ((P.comparison hX hY f hf).retained k)).comap
          ((P.comparison hX hY f hf).map
            ((P.comparison hX hY f hf).retained k).castSucc).base) (J Y hY k)) ∧
        (∀ i, i ∉ Set.range (P.comparison hX hY f hf).retained ↔
          (J X hX i).comap ((P.comparison hX hY f hf).map i.castSucc).base = ⊤) ∧
        ∀ i, IsIso (strictTransformι ((P.comparison hX hY f hf).map i.castSucc).base
          ((P.tower X hX).tower.arrow i).base (J X hX i).support.compl) := by
  sorry

end AlgebraicGeometry
