/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Sheaf.AlgebraicGeometry.LogCharacteristicIdeal
import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
import Sheaf.AlgebraicGeometry.FSStrictLogMorphism
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction

/-!
# Strict base change of saturated logarithmic blowups

Source: ILO VIII 3.3.8--3.3.11, printed pp. 107--108
(blueprint: lem-trf-strict-log-blowup-cartesian).

Characteristic comparisons are normalized on actual Zariski log-section germs.
The saturated universal properties and Cartesian squares allow every fs test scheme.
Identity and composition equations retain the log-section maps as well as scheme maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- A Cartesian square for arbitrary fs log test schemes. Commutativity is witnessed
by a common composite (the condition of `EtaleLogMap.CompEq`), including all log-section
maps. Unique factorizations are unique as complete log morphisms, without a Noetherian
condition on the tests.
This generalizes `EtaleLogHom.IsFSPullback` from `LogFanChartBlowup`: its bundled
`FineSaturatedLogScheme` tests are locally Noetherian, whereas this item requires all
fs log test schemes. The original locally Noetherian interface is retained.
Source: ILO VIII 3.3.9--3.3.11 (blueprint: lem-trf-strict-log-blowup-cartesian). -/
def EtaleLogMap.IsFSPullback {A B C D : Scheme.{u}}
    {LA : EtaleLogStructure A} {LB : EtaleLogStructure B}
    {LC : EtaleLogStructure C} {LD : EtaleLogStructure D}
    (a : EtaleLogMap LA LB) (b : EtaleLogMap LB LD)
    (c : EtaleLogMap LA LC) (d : EtaleLogMap LC LD) : Prop :=
  (∃ f : EtaleLogMap LA LD, a.CompEq b f ∧ c.CompEq d f) ∧
    ∀ (T : Scheme.{u}) (L : EtaleLogStructure T), L.IsFineSaturated →
    ∀ (p : EtaleLogMap L LB) (q : EtaleLogMap L LC),
      (∃ f : EtaleLogMap L LD, p.CompEq b f ∧ q.CompEq d f) →
      ∃! r : EtaleLogMap L LA, r.CompEq a p ∧ r.CompEq c q


/-- The characteristic map induced by the specified log morphism: its base is the given
scheme map, and it acts on every Zariski log-section germ by the given section map.
These equations determine the map on the sheafified unit quotient, because its sections
are locally represented by sharp log sections.
Source: ILO VIII 3.3.8, 3.3.12 (blueprint: lem-trf-strict-log-blowup-cartesian). -/
def EtaleLogHom.IsSharpMap {W V : FineSaturatedLogScheme.{u}} (g : EtaleLogHom W V)
    (c : W.logStructure.sharpSpace ⟶ V.logStructure.sharpSpace) : Prop :=
  c.hom.base = g.base.base ∧
    ∀ (U : V.scheme.Opens) (B : W.scheme.Opens)
      (k : B.toScheme ⟶ U.toScheme)
      (hk : k ≫ U.ι = B.ι ≫ g.base)
      (s : V.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale V.scheme).obj U)))
      (y : W.scheme) (hy : y ∈ B) (hx : c.hom.base y ∈ U),
      FineFan.stalkMap c y
        (FineFan.germ V.logStructure.sharpSpace.presheaf U (c.hom.base y) hx
          (V.logStructure.sharpSection U s)) =
        FineFan.germ W.logStructure.sharpSpace.presheaf B y hy
          (W.logStructure.sharpSection B
            (g.sectionMap ((logOpenEtale V.scheme).obj U)
              ((logOpenEtale W.scheme).obj B) k hk s))

/-- Strict logarithmic base change, coherent characteristic centers, saturated Cartesian
squares, and their identity/composition coherence.

Source: ILO VIII 3.3.8--3.3.11, 3.3.12--3.3.13
(blueprint: lem-trf-strict-log-blowup-cartesian).

Proof plan (the seven DAG steps):
1. Choose Zariski fs monoid charts by `lem-trf-zariski-fs-monoid-chart`. Pull them back
using the actual section maps of g. The mapping bijection of
`lem-sfb-fine-chart-logification-thickening` and strictness identify their logifications
with L; `lem-trf-monoid-chart-characteristic-fan` gives Zariski origin. Uniqueness fixing
prelog sections and units glues these identifications.
2. At w over v, the local ring map preserves and reflects units of chart elements.
Thus the same face E is inverted at both points. The characteristic formula of
`lem-trf-monoid-chart-characteristic-fan` identifies both stalks with P_E/E^gp and the
map with the identity on representatives. Local inverse germs glue to a sheaf isomorphism.
3. Lift a nonempty finite list of generators of K locally to log sections n_i. Its
inverse image is exactly the ideal (n_i): characteristic equality differs by a unit.
The chart pushout formula of `def-trf-fs-log-blowup` proves nonempty coherence, and the
same calculation with g(n_i) gives the asserted equality after pullback.
4. Strict pullback preserves the finite chart generators of any coherent H. Apply
`lem-trf-coherent-log-ideal-chart-construction` to both bases. The saturated universal
property gives the unique arrow g' over the original composite. The arbitrary-test
scope is that of `lem-trf-log-ideal-chart-lifting-criterion`.
5. For arbitrary fs T, pull back the principal center on V' to T. It equals the pullback
of H_W. The universal property of W' gives the unique lift over W. Applying uniqueness
for V' makes its other projection the prescribed map T to V'.
6. Use the common saturated fraction monoids R_e on both bases. The base-change clause
of `lem-trf-log-ideal-affine-atlas-gluing` identifies charts and overlaps with their
scheme pullbacks. The chart logification mapping bijection makes the local maps strict;
they glue and equal g' by uniqueness.
7. Identity and composite comparisons are lifts of the same log morphism. Uniqueness
in the saturated universal property gives the full identity/composition equations.
Pullback centers compose because their generators are the images of the same sections.
-/
theorem strictLogBlowupCartesian :
    (∀ (W V : FineSaturatedLogScheme.{u}) (g : EtaleLogHom W V),
      g.IsStrict → V.logStructure.IsZariski →
      W.logStructure.IsZariski ∧
        ∃ c : W.logStructure.sharpSpace ⟶ V.logStructure.sharpSpace,
          g.IsSharpMap c ∧ (∀ w : W.scheme, Function.Bijective (FineFan.stalkMap c w)) ∧
          (∀ K : V.logStructure.SharpIdealFamily,
            V.logStructure.IsNonemptyCoherentSharpIdeal K →
            V.logStructure.IsNonemptyCoherentIdeal (V.logStructure.inverseSharpIdeal K) ∧
              W.logStructure.inverseSharpIdeal
                (EtaleLogStructure.pullbackSharpIdeal c K) =
                  g.pullbackIdeal (V.logStructure.inverseSharpIdeal K)) ∧
          (∀ H : V.logStructure.IdealFamily,
            V.logStructure.IsNonemptyCoherentIdeal H →
            ∃ (V' W' : FineSaturatedLogScheme.{u})
              (bV : EtaleLogHom V' V) (bW : EtaleLogHom W' W),
              IsSaturatedLogBlowup bV H ∧
              bV.toLogMap.IsFSPrincipalization H ∧
              IsSaturatedLogBlowup bW (g.pullbackIdeal H) ∧
              bW.toLogMap.IsFSPrincipalization (g.pullbackIdeal H) ∧
              ∃ g' : EtaleLogHom W' V',
                (∃ f : EtaleLogMap W'.logStructure V.logStructure,
                    bW.toLogMap.CompEq g.toLogMap f ∧ g'.toLogMap.CompEq bV.toLogMap f) ∧
                (∀ h : EtaleLogHom W' V',
                  (∃ f : EtaleLogMap W'.logStructure V.logStructure,
                      bW.toLogMap.CompEq g.toLogMap f ∧ h.toLogMap.CompEq bV.toLogMap f) → h = g') ∧
                g'.IsStrict ∧
                bW.toLogMap.IsFSPullback g.toLogMap g'.toLogMap bV.toLogMap)) ∧
    (∀ (V V' : FineSaturatedLogScheme.{u}) (H : V.logStructure.IdealFamily)
      (b : EtaleLogHom V' V), V.logStructure.IsZariski →
      IsSaturatedLogBlowup b H →
      ∀ (i : EtaleLogHom V V) (i' : EtaleLogHom V' V'), i.IsIdentity →
        (∃ f : EtaleLogMap V'.logStructure V.logStructure,
            b.toLogMap.CompEq i.toLogMap f ∧ i'.toLogMap.CompEq b.toLogMap f) → i'.IsIdentity) ∧
    (∀ (U W V U' W' V' : FineSaturatedLogScheme.{u})
      (h : EtaleLogHom U W) (g : EtaleLogHom W V) (k : EtaleLogHom U V)
      (H : V.logStructure.IdealFamily)
      (bU : EtaleLogHom U' U) (bW : EtaleLogHom W' W) (bV : EtaleLogHom V' V),
      V.logStructure.IsZariski → h.IsStrict → g.IsStrict → h.CompEq g k →
      IsSaturatedLogBlowup bV H → IsSaturatedLogBlowup bW (g.pullbackIdeal H) →
      IsSaturatedLogBlowup bU (h.pullbackIdeal (g.pullbackIdeal H)) →
      ∀ (h' : EtaleLogHom U' W') (g' : EtaleLogHom W' V') (k' : EtaleLogHom U' V'),
        (∃ f : EtaleLogMap U'.logStructure W.logStructure,
            bU.toLogMap.CompEq h.toLogMap f ∧ h'.toLogMap.CompEq bW.toLogMap f) →
        (∃ f : EtaleLogMap W'.logStructure V.logStructure,
            bW.toLogMap.CompEq g.toLogMap f ∧ g'.toLogMap.CompEq bV.toLogMap f) →
        (∃ f : EtaleLogMap U'.logStructure V.logStructure,
            bU.toLogMap.CompEq k.toLogMap f ∧ k'.toLogMap.CompEq bV.toLogMap f) →
        h.pullbackIdeal (g.pullbackIdeal H) = k.pullbackIdeal H ∧
          h'.CompEq g' k') := by
  sorry

end AlgebraicGeometry
