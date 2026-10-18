/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/

import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction
import Sheaf.GroupTheory.FineMonoidFiniteSaturation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Fan charts and pullback of saturated fan blowup towers

Source: ILO, Exposé VIII 3.3.2--3.3.13, printed pp. 106--109, and the finite-cover
argument of 3.3.15 (blueprint: lem-trf-log-fan-chart-blowup).

The characteristic sheaf is the sheafified unit quotient of the Zariski restriction.
No global lift of a fan chart to a monoid chart is assumed. Cartesian squares below
are universal squares of fs log schemes, rather than ordinary scheme pullbacks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The canonical inclusion of opens into the small étale site. Source: ILO VIII 3.3.2
(blueprint: lem-trf-log-fan-chart-blowup). -/
noncomputable def logOpenEtale (X : Scheme.{u}) : X.Opens ⥤ X.Etale :=
  MorphismProperty.Comma.lift X.restrictFunctor
    (fun U ↦ (inferInstance : Etale U.ι)) (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- Zariski restriction of the actual log sheaf. Source: ILO VIII 3.3.2
(blueprint: lem-trf-log-fan-chart-blowup). -/
noncomputable def EtaleLogStructure.zariskiPresheaf {X : Scheme.{u}}
    (M : EtaleLogStructure X) : TopCat.Presheaf CommMonCat.{u} X.carrier :=
  (logOpenEtale X).op ⋙ M.monoidSheaf.obj

/-- The sharp monoidal space of a log scheme, using actual sheafification of the unit
quotient. Source: ILO VIII 3.3.12 (blueprint: lem-trf-log-fan-chart-blowup). -/
noncomputable def EtaleLogStructure.sharpSpace {X : Scheme.{u}}
    (M : EtaleLogStructure X) : SheafedSpace CommMonCat.{u} where
  carrier := X.carrier
  presheaf := (FineFan.sharpSheaf M.zariskiPresheaf).obj
  IsSheaf := (FineFan.sharpSheaf M.zariskiPresheaf).property

/-- The canonical sharpening of a log section. Source: ILO VIII 3.3.12
(blueprint: lem-trf-log-fan-chart-blowup). -/
noncomputable def EtaleLogStructure.sharpSection {X : Scheme.{u}}
    (M : EtaleLogStructure X) (U : X.Opens) :
    M.monoidSheaf.obj.obj (op ((logOpenEtale X).obj U)) →*
      M.sharpSpace.presheaf.obj (op U) :=
  (((toSheafify (Opens.grothendieckTopology X.carrier)
    (FineFan.sharpPresheaf M.zariskiPresheaf)).app (op U)).hom).comp
      Associates.mkMonoidHom

/-- A Zariski log structure: every geometric characteristic germ comes from a Zariski neighbourhood
of its image. This is the stalkwise counit criterion for association from the Zariski
site, followed by adjoining the étale units. Source: ILO VIII 3.3.2, 3.3.12
(blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogStructure.IsZariski {X : Scheme.{u}} (M : EtaleLogStructure X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (m : M.toEtalePrelogStructure.stalk t),
    ∃ (U : X.Opens) (w : (Scheme.pointSmallEtale t).fiber.obj ((logOpenEtale X).obj U))
      (s : M.monoidSheaf.obj.obj (op ((logOpenEtale X).obj U))),
      ∃ a : (strictLocalRing X t)ˣ,
        M.toEtalePrelogStructure.germ t ((logOpenEtale X).obj U) w s * M.unitsIn t a = m

/-- The relation induced on characteristic stalks by a log morphism. Representatives
are compared on a pointed relative étale diagram, so this is the graph of the canonical
map, without choosing presentations of stalk elements. Source: ILO VI 1.1, VIII 3.3.8
(blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.CharacteristicRelation {Y X : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom Y X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Y.scheme)
    (a : X.logStructure.characteristic (t ≫ f.base))
    (b : Y.logStructure.characteristic t) : Prop :=
  ∃ (W : X.scheme.Etale) (V : Y.scheme.Etale)
    (w : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj W)
    (v : (Scheme.pointSmallEtale t).fiber.obj V)
    (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f.base)
    (s : X.logStructure.monoidSheaf.obj.obj (op W)),
    v.left ≫ k = w.left ∧
      Associates.mk (X.logStructure.toEtalePrelogStructure.germ (t ≫ f.base) W w s) = a ∧
      Associates.mk (Y.logStructure.toEtalePrelogStructure.germ t V v
        (f.sectionMap W V k hk s)) = b

/-- Strictness is the canonical characteristic-stalk isomorphism criterion for pullback
log structures. Normalization by the graph excludes an arbitrary isomorphism.
Source: ILO VI 1.1, VIII 3.3.8 (blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.IsStrict {Y X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y.scheme),
    ∃ e : X.logStructure.characteristic (t ≫ f.base) ≃* Y.logStructure.characteristic t,
      ∀ a b, f.CharacteristicRelation t a b ↔ e a = b

/-- A fan chart is a local morphism of sharp monoidal spaces whose inverse-image
characteristic-sheaf map is an isomorphism, tested on all stalks. Source: ILO VIII
3.3.12 (blueprint: lem-trf-log-fan-chart-blowup). -/
structure LogFanChart (X : FineSaturatedLogScheme.{u}) (F : FineFan.Fan.{u}) where
  zariski : X.logStructure.IsZariski
  map : X.logStructure.sharpSpace ⟶ F.space
  stalkBijective : ∀ x : X.scheme, Function.Bijective (FineFan.stalkMap map x)

/-- The induced ideal is the inverse image in the log sheaf of the ideal generated
in characteristics. The displayed germ condition performs both sheaf-local generation
and the inverse image, including unit multiples. Source: ILO VIII 3.3.13(i)
(blueprint: lem-trf-log-fan-chart-blowup). -/
def LogFanChart.pullbackIdeal {X : FineSaturatedLogScheme.{u}} {F : FineFan.Fan.{u}}
    (c : LogFanChart X F) (J : FineFan.IdealFamily F) : X.logStructure.IdealFamily :=
  fun W ↦ {s | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme) (w : (Scheme.pointSmallEtale t).fiber.obj W),
    ∃ (U : X.scheme.Opens)
      (v : (Scheme.pointSmallEtale t).fiber.obj ((logOpenEtale X.scheme).obj U))
      (hx : t default ∈ U)
      (m : X.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale X.scheme).obj U)))
      (a : FineFan.stalk F.space.presheaf (c.map.hom.base (t default)))
      (q : FineFan.stalk X.logStructure.sharpSpace.presheaf (t default)),
      Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W w s) =
        Associates.mk (X.logStructure.toEtalePrelogStructure.germ t
          ((logOpenEtale X.scheme).obj U) v m) ∧
      a ∈ FineFan.idealStalk J (c.map.hom.base (t default)) ∧
      FineFan.germ X.logStructure.sharpSpace.presheaf U (t default) hx
        (X.logStructure.sharpSection U m) = FineFan.stalkMap c.map (t default) a * q}

/-- The normalized geometric-stalk comparison of a fan chart. This is a property of
an isomorphism, fixed on all Zariski log-section germs. Source: ILO VIII 3.3.12--3.3.13
(blueprint: lem-trf-log-fan-chart-blowup). -/
def LogFanChart.IsGeometricComparison {X : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart X F)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (e : FineFan.stalk F.space.presheaf (c.map.hom.base (t default)) ≃*
      X.logStructure.characteristic t) : Prop :=
  ∀ (U : X.scheme.Opens)
    (w : (Scheme.pointSmallEtale t).fiber.obj ((logOpenEtale X.scheme).obj U))
    (hx : t default ∈ U)
    (s : X.logStructure.monoidSheaf.obj.obj (op ((logOpenEtale X.scheme).obj U)))
    (a : FineFan.stalk F.space.presheaf (c.map.hom.base (t default))),
    FineFan.stalkMap c.map (t default) a =
      FineFan.germ X.logStructure.sharpSpace.presheaf U (t default) hx
        (X.logStructure.sharpSection U s) →
      e a = Associates.mk
        (X.logStructure.toEtalePrelogStructure.germ t ((logOpenEtale X.scheme).obj U) w s)

/-- Commutativity of a log/fan square, checked on actual section germs. The two
fan stalk elements correspond under the fan arrow exactly when their characteristic
images correspond under the log arrow. Source: ILO VIII 3.3.13(i),(iii)
(blueprint: lem-trf-log-fan-chart-blowup). -/
def LogFanChart.Compatible {Y X : FineSaturatedLogScheme.{u}} {G F : FineFan.Fan.{u}}
    (d : LogFanChart Y G) (c : LogFanChart X F) (f : EtaleLogHom Y X)
    (g : G.space ⟶ F.space) : Prop :=
  (∀ y : Y.scheme, g.hom.base (d.map.hom.base y) = c.map.hom.base (f.base y)) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y.scheme)
      (e : FineFan.stalk F.space.presheaf (c.map.hom.base ((t ≫ f.base) default)) ≃*
        X.logStructure.characteristic (t ≫ f.base))
      (e' : FineFan.stalk G.space.presheaf (d.map.hom.base (t default)) ≃*
        Y.logStructure.characteristic t),
      c.IsGeometricComparison (t ≫ f.base) e → d.IsGeometricComparison t e' →
      ∀ (h : c.map.hom.base ((t ≫ f.base) default) =
          g.hom.base (d.map.hom.base (t default)))
        (a : FineFan.stalk F.space.presheaf (c.map.hom.base ((t ≫ f.base) default))),
        f.CharacteristicRelation t (e a)
          (e' (FineFan.stalkMap g (d.map.hom.base (t default))
            (eqToHom (congrArg (FineFan.stalk F.space.presheaf) h) a)))

/-- A lift retains every level, ordered center, log blowup, and fan chart, with the
commuting log/fan squares. Source: ILO VIII 3.3.13(i),(iii)
(blueprint: lem-trf-log-fan-chart-blowup). -/
structure LogFanTower {n : ℕ} (T : FineFan.Tower.{u} n) where
  level : Fin (n + 1) → FineSaturatedLogScheme.{u}
  chart : ∀ i, LogFanChart (level i) (T.level i)
  arrow : ∀ i : Fin n, EtaleLogHom (level i.succ) (level i.castSucc)
  blowup : ∀ i : Fin n,
    IsSaturatedLogBlowup (arrow i) ((chart i.castSucc).pullbackIdeal (T.center i))
  compatible : ∀ i : Fin n,
    (chart i.succ).Compatible (chart i.castSucc) (arrow i) (T.arrow i).map

/-- Equality of two log composites, using a common composite as witness and testing
all relative sections. Source: ILO VIII 3.3.8--3.3.13
(blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.Square {A B C D : FineSaturatedLogScheme.{u}}
    (a : EtaleLogHom A B) (b : EtaleLogHom B D)
    (c : EtaleLogHom A C) (d : EtaleLogHom C D) : Prop :=
  ∃ f : EtaleLogHom A D, a.CompEq b f ∧ c.CompEq d f

/-- A Cartesian square in the fs category, expressed by unique log factorizations.
No assertion about the ordinary scheme fibre product is included. Source: ILO VIII
3.3.9--3.3.11 (blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.IsFSPullback {A B C D : FineSaturatedLogScheme.{u}}
    (a : EtaleLogHom A B) (b : EtaleLogHom B D)
    (c : EtaleLogHom A C) (d : EtaleLogHom C D) : Prop :=
  a.Square b c d ∧ ∀ (Z : FineSaturatedLogScheme.{u})
    (p : EtaleLogHom Z B) (q : EtaleLogHom Z C), p.Square b q d →
      ∃! r : EtaleLogHom Z A, r.CompEq a p ∧ r.CompEq c q

/-- A strict base-change comparison of lifted towers: every stage is Cartesian in
fs log schemes, and the centers and charts are preserved. Source: ILO VIII 3.3.8--3.3.13
(blueprint: lem-trf-log-fan-chart-blowup). -/
structure LogFanTower.StrictComparison {n : ℕ} {T : FineFan.Tower.{u} n}
    (L K : LogFanTower T) where
  map : ∀ i, EtaleLogHom (K.level i) (L.level i)
  strict : ∀ i, (map i).IsStrict
  charts : ∀ i, (K.chart i).Compatible (L.chart i) (map i)
    (𝟙 (T.level i).space)
  centers : ∀ i : Fin n,
    (K.chart i.castSucc).pullbackIdeal (T.center i) =
      (map i.castSucc).pullbackIdeal ((L.chart i.castSucc).pullbackIdeal (T.center i))
  cartesian : ∀ i : Fin n,
    (K.arrow i).IsFSPullback (map i.castSucc) (map i.succ) (L.arrow i)

/-- Inclusion of a consecutive segment of an ordered fan tower, retaining the centers
and arrows under the specified level identifications. This includes the two segments
of a concatenation and the empty segment. Source: ILO VIII 3.3.9--3.3.13
(blueprint: lem-trf-log-fan-chart-blowup). -/
structure LogFanSegment {m n : ℕ} (S : FineFan.Tower.{u} m) (T : FineFan.Tower.{u} n) where
  index : Fin (m + 1) → Fin (n + 1)
  step : Fin m → Fin n
  source : ∀ i, index i.castSucc = (step i).castSucc
  target : ∀ i, index i.succ = (step i).succ
  level : ∀ i, T.level (index i) = S.level i
  arrow : ∀ i, HEq (T.arrow (step i)) (S.arrow i)
  center : ∀ i, HEq (T.center (step i)) (S.center i)

/-- The identity log morphism, specified on all relative test sections. Source: ILO
VI 1.1 and VIII 3.3.9 (blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.IsIdentity {X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X X) : Prop :=
  f.base = 𝟙 X.scheme ∧
    ∀ (W V : X.scheme.Etale) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ f.base) (h : k ≫ W.hom = V.hom),
      f.sectionMap W V k hk =
        (X.logStructure.monoidSheaf.obj.map
          (MorphismProperty.Over.homMk k h : V ⟶ W).op).hom

/-- Inverse log morphisms, with both composites equal to the actual identity including
all log-section maps. Source: ILO VI 1.1 and VIII 3.3.9
(blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.AreInverses {Y X : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom Y X) (g : EtaleLogHom X Y) : Prop :=
  (∃ h : EtaleLogHom Y Y, f.CompEq g h ∧ h.IsIdentity) ∧
    (∃ h : EtaleLogHom X X, g.CompEq f h ∧ h.IsIdentity)

/-- Identification of a lifted consecutive segment with any other lift from its
specified initial log scheme. It is an isomorphism of log towers, not just of schemes.
The inverse identities are expressed by unique factorizations, since log blowups
have at most one map over a fixed base making their center invertible.
Source: ILO VIII 3.3.9--3.3.13 (blueprint: lem-trf-log-fan-chart-blowup). -/
structure LogFanSegment.Comparison {m n : ℕ} {S : FineFan.Tower.{u} m}
    {T : FineFan.Tower.{u} n} (a : LogFanSegment S T)
    (L : LogFanTower T) (K : LogFanTower S) where
  forward : ∀ i, EtaleLogHom (K.level i) (L.level (a.index i))
  backward : ∀ i, EtaleLogHom (L.level (a.index i)) (K.level i)
  inverse : ∀ i, (forward i).AreInverses (backward i)
  strict : ∀ i, (forward i).IsStrict ∧ (backward i).IsStrict
  charts : ∀ i, (K.chart i).Compatible (L.chart (a.index i)) (forward i)
    (eqToHom (congrArg FineFan.Fan.space (a.level i).symm))
  arrows : ∀ i : Fin m,
    ∃ (f : EtaleLogHom (K.level i.succ) (L.level (a.index i.castSucc))),
        (K.arrow i).CompEq (forward i.castSucc) f ∧
          ∃ (g : EtaleLogHom (K.level i.succ) (L.level (a.step i).succ)),
            HEq g (forward i.succ) ∧
            ∃ (h : EtaleLogHom (K.level i.succ) (L.level (a.step i).castSucc)),
              g.CompEq (L.arrow (a.step i)) h ∧ HEq h f

/-- Local fan charts, a finite quasi-compact strict étale cover when required, and
pullback of every ordered saturated fan blowup tower, with geometric characteristic
stalks, coherent centers and strict fs base change.

Source: ILO VIII 3.3.2--3.3.13 and the finite-cover argument of 3.3.15
(blueprint: lem-trf-log-fan-chart-blowup).

Proof:
1. Choose fs charts on strict étale neighbourhoods. Send a point to the prime
complementary to the elements mapping to units. Associated-log stalks and
`lem-trf-fs-face-sharpening` identify its sharpened stalks with the characteristic.
The associated log structure of a constant chart is Zariski.
2. Refine to affine open neighbourhoods. Étale maps are open and affine schemes
are quasi-compact, so quasi-compactness selects finitely many of their images.
The empty scheme permits the empty family.
3. Near a fan point use its affine generalization neighbourhood. Its monoid is
sharp fs with free finite-rank completion by face sharpening.
4. Lift a finite basis of that group to the Zariski log stalk; differences from
monoid representatives are units. Spread these finitely many lifts and equations
on a Zariski neighbourhood to obtain a lift of the given characteristic chart.
5. The associated-log universal property and its stalk formula show this lift is
a log chart: identity on units and an isomorphism on characteristics give bijectivity.
6. A finite nonempty generating set of a fan ideal gives precisely the prescribed
inverse-image log ideal. Apply `lem-trf-coherent-log-ideal-chart-construction`.
7. Both saturated blowups have charts from the same saturated fraction monoids;
the unit-face calculation identifies all their characteristic stalks.
8. The local fan maps glue: a generator of the principal ideal determines the
fractions uniquely, saturation determines their roots, and common localizations
identify overlaps. Thus no global monoid lift is used.
9. Iterate in the given order, starting with the supplied chart. The universal
properties identify repeated constructions and concatenated towers uniquely.
10. Strict pullback preserves characteristic sheaves and the prescribed centers.
The same universal property is the fs Cartesian property at each level. Unique
factorizations give compatibility with identities and composition; the comparison of
a consecutive segment starts with the identity log morphism, sections included.
-/
theorem log_fan_chart_blowup :
    (∀ (X : FineSaturatedLogScheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X.scheme),
      ∃ (V : FineSaturatedLogScheme.{u}) (f : EtaleLogHom V X)
        (F : FineFan.Fan.{u}), f.IsStrict ∧ Etale f.base ∧
        (∃ v : Spec (.of Ω) ⟶ V.scheme, v ≫ f.base = t) ∧ Nonempty (LogFanChart V F)) ∧
    (∀ X : FineSaturatedLogScheme.{u}, CompactSpace X.scheme →
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
        (g : Algebra.GrothendieckGroup (X.logStructure.characteristic t)) (k : ℕ),
        0 < k → g ^ k = 1 → g = 1) →
      ∃ (r : ℕ) (V : Fin r → FineSaturatedLogScheme.{u})
        (f : ∀ i, EtaleLogHom (V i) X) (F : Fin r → FineFan.Fan.{u}),
        (∀ i, (f i).IsStrict ∧ Etale (f i).base ∧ CompactSpace (V i).scheme ∧
          (F i).IsSaturated ∧ (F i).IsTorsionFree ∧
          (∃ P : CommMonCat.{u}, FineFan.IsFine P ∧ Nonempty ((F i).space ≅ FineFan.affine P)) ∧
          Nonempty (LogFanChart (V i) (F i))) ∧
        ∀ x : X.scheme, ∃ (i : Fin r) (v : (V i).scheme), (f i).base v = x) ∧
    (∀ (n : ℕ) (T : FineFan.Tower.{u} n) (X : FineSaturatedLogScheme.{u})
      (c : LogFanChart X (T.level 0)),
      ∃ L : LogFanTower T, L.level 0 = X ∧ HEq (L.chart 0) c ∧
        (∀ (i : Fin (n + 1)) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (t : Spec (.of Ω) ⟶ (L.level i).scheme),
          ∃ e : FineFan.stalk (T.level i).space.presheaf
            ((L.chart i).map.hom.base (t default)) ≃* (L.level i).logStructure.characteristic t,
            (L.chart i).IsGeometricComparison t e) ∧
        (∀ (Y : FineSaturatedLogScheme.{u}) (F : FineFan.Fan.{u})
          (d : LogFanChart Y F) (J : FineFan.IdealFamily F),
          FineFan.IsNonemptyCoherentIdeal J →
            Y.logStructure.IsNonemptyCoherentIdeal (d.pullbackIdeal J)) ∧
        (∀ (Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom Y (L.level 0)),
          f.IsStrict → ∃ d : LogFanChart Y (T.level 0),
            d.Compatible (L.chart 0) f (𝟙 (T.level 0).space) ∧
            ∃ K : LogFanTower T, K.level 0 = Y ∧ HEq (K.chart 0) d ∧
              ∃ q : LogFanTower.StrictComparison L K, HEq (q.map 0) f) ∧
        ∀ (K : LogFanTower T) (f : EtaleLogHom (K.level 0) (L.level 0)),
          f.IsStrict →
          (K.chart 0).Compatible (L.chart 0) f
            (𝟙 (T.level 0).space) →
          ∃! q : LogFanTower.StrictComparison L K, q.map 0 = f) ∧
    (∀ (m n : ℕ) (S : FineFan.Tower.{u} m) (T : FineFan.Tower.{u} n)
      (a : LogFanSegment S T) (L : LogFanTower T) (K : LogFanTower S)
      (h : K.level 0 = L.level (a.index 0)),
      HEq (K.chart 0) (L.chart (a.index 0)) →
        ∃ q : a.Comparison L K,
          (q.forward 0).base = eqToHom (congrArg FineSaturatedLogScheme.scheme h) ∧
            ∃ g : EtaleLogHom (K.level 0) (K.level 0), g.IsIdentity ∧ HEq (q.forward 0) g) := by
  sorry

end AlgebraicGeometry
