/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineLogSchemeMorphisms
public import Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent

import Sheaf.AlgebraicGeometry.FineLogEtaleDescent
import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup

/-!
# Effective polarized étale descent for fine log schemes

Source: ILO VI 1.1 and VIII 3.3.8, printed pp. 69, 107--108; Stacks Project,
Tags 0D3C, 02WW, 04W8, 034C and 023Q
(blueprint: lem-trf-polarized-fine-log-etale-descent).

The base charts carry the pulled-back log structure. Consequently a log map from `X_i`
to the strict chart `U_i` is exactly a log map to `S` over the prescribed scheme map.
The overlap log isomorphism is specified on every common étale test scheme, naturally
under restriction. This presents the usual log isomorphism on the fibre product, without
choosing new copies of its canonical pulled-back log structures.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The logarithmic lift of a polarized scheme descent datum. The components of
`logTheta` identify the two restricted log sheaves on the specified scheme relation.
Their naturality, structural-map equation, diagonal, cocycle and base compatibility
are precisely log isomorphisms over the strict base overlaps.
Source: ILO VI 1.1, VIII 3.3.8; Stacks Tags 02WW and 04W8
(blueprint: lem-trf-polarized-fine-log-etale-descent). -/
structure PolarizedFineLogDescentDatum (S : FineLogScheme.{u}) {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S.scheme} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}
    (D : PolarizedSchemeEtaleDescentDatum S.scheme I U uMap X f L hL) where
  localLog : ∀ i, EtaleLogStructure (X i)
  fine : ∀ i, (localLog i).IsFine
  locallyNoetherian : ∀ i, IsLocallyNoetherian (X i)
  localMap : ∀ i, (localLog i).HomAlong S.logStructure (f i ≫ uMap i)
  logTheta : ∀ i j (T : Scheme.{u})
    (a : T ⟶ polarizedOverlap U uMap X f i j) (p : T ⟶ X i) (q : T ⟶ X j)
    [Etale p] [Etale q]
    (_hp : a ≫ polarizedOverlapX U uMap X f i j = p)
    (_hq : a ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = q),
    (localLog i).sectionsAt p ≃* (localLog j).sectionsAt q
  naturality : ∀ i j (T T' : Scheme.{u})
    (a : T ⟶ polarizedOverlap U uMap X f i j) (p : T ⟶ X i) (q : T ⟶ X j)
    [Etale p] [Etale q]
    (hp : a ≫ polarizedOverlapX U uMap X f i j = p)
    (hq : a ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = q)
    (h : T' ⟶ T) [Etale (h ≫ p)] [Etale (h ≫ q)]
    (hp' : (h ≫ a) ≫ polarizedOverlapX U uMap X f i j = h ≫ p)
    (hq' : (h ≫ a) ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = h ≫ q)
    (s : (localLog i).sectionsAt p),
    logTheta i j T' (h ≫ a) (h ≫ p) (h ≫ q) hp' hq'
        ((localLog i).restrictAt p h s) =
      (localLog j).restrictAt q h (logTheta i j T a p q hp hq s)
  alpha : ∀ i j (T : Scheme.{u})
    (a : T ⟶ polarizedOverlap U uMap X f i j) (p : T ⟶ X i) (q : T ⟶ X j)
    [Etale p] [Etale q]
    (hp : a ≫ polarizedOverlapX U uMap X f i j = p)
    (hq : a ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = q)
    (s : (localLog i).sectionsAt p),
    (localLog j).alpha.app (op (Scheme.Etale.mk q)) (logTheta i j T a p q hp hq s) =
      (localLog i).alpha.app (op (Scheme.Etale.mk p)) s
  identity : ∀ i (T : Scheme.{u}) (a : T ⟶ polarizedOverlap U uMap X f i i)
    (p : T ⟶ X i) [Etale p]
    (hp : a ≫ polarizedOverlapX U uMap X f i i = p)
    (hq : a ≫ (D.theta i i).hom ≫ polarizedOverlapX U uMap X f i i = p),
    a = p ≫ polarizedOverlapDiagonal U uMap X f i →
      logTheta i i T a p p hp hq = MulEquiv.refl _
  cocycle : ∀ i j k (T : Scheme.{u}) (p : T ⟶ X i) (q : T ⟶ X j) (r : T ⟶ X k)
    [Etale p] [Etale q] [Etale r]
    (a : T ⟶ polarizedOverlap U uMap X f i j)
    (b : T ⟶ polarizedOverlap U uMap X f j k)
    (c : T ⟶ polarizedOverlap U uMap X f i k)
    (ha : a ≫ polarizedOverlapX U uMap X f i j = p)
    (ha' : a ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = q)
    (hb : b ≫ polarizedOverlapX U uMap X f j k = q)
    (hb' : b ≫ (D.theta j k).hom ≫ polarizedOverlapX U uMap X f k j = r)
    (hc : c ≫ polarizedOverlapX U uMap X f i k = p)
    (hc' : c ≫ (D.theta i k).hom ≫ polarizedOverlapX U uMap X f k i = r),
    a ≫ polarizedOverlapUj U uMap X f i j = b ≫ polarizedOverlapUi U uMap X f j k →
    c ≫ polarizedOverlapUj U uMap X f i k = b ≫ polarizedOverlapUj U uMap X f j k →
      (logTheta i j T a p q ha ha').trans (logTheta j k T b q r hb hb') =
        logTheta i k T c p r hc hc'
  overBase : ∀ i j (T : Scheme.{u})
    (a : T ⟶ polarizedOverlap U uMap X f i j) (p : T ⟶ X i) (q : T ⟶ X j)
    [Etale p] [Etale q]
    (hp : a ≫ polarizedOverlapX U uMap X f i j = p)
    (hq : a ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = q)
    (W : S.scheme.Etale) (k : T ⟶ W.left)
    (hi : k ≫ W.hom = p ≫ (f i ≫ uMap i))
    (hj : k ≫ W.hom = q ≫ (f j ≫ uMap j))
    (s : S.logStructure.monoidSheaf.obj.obj (op W)),
    logTheta i j T a p q hp hq ((localMap i).sectionMap W (Scheme.Etale.mk p) k hi s) =
      (localMap j).sectionMap W (Scheme.Etale.mk q) k hj s

/-- A polarized fine log descent, with labelled strict chart maps inducing the specified
log transitions as well as the specified scheme and line-module transitions.
Source: ILO VIII 3.3.8; Stacks Tags 02WW and 04W8
(blueprint: lem-trf-polarized-fine-log-etale-descent). -/
structure PolarizedFineLogRealization {S : FineLogScheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S.scheme} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}
    {D : PolarizedSchemeEtaleDescentDatum S.scheme I U uMap X f L hL}
    (E : PolarizedFineLogDescentDatum S D) where
  pair : PolarizedDescentPair U uMap X f L
  realizes : IsPolarizedDescentRealization D pair
  logStructure : EtaleLogStructure pair.Y
  fine : logStructure.IsFine
  locallyNoetherian : IsLocallyNoetherian pair.Y
  map : logStructure.HomAlong S.logStructure pair.g
  chartMap : ∀ i, (E.localLog i).HomAlong logStructure (polarizedChartMap pair i)
  strict : ∀ i, (chartMap i).IsStrictEtale
  overBase : ∀ i, (chartMap i).CompEq map (E.localMap i)
  transition : ∀ i j (T : Scheme.{u})
    (a : T ⟶ polarizedOverlap U uMap X f i j) (p : T ⟶ X i) (q : T ⟶ X j)
    [Etale p] [Etale q]
    (hp : a ≫ polarizedOverlapX U uMap X f i j = p)
    (hq : a ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = q)
    (W : pair.Y.Etale) (k : T ⟶ W.left)
    (hi : k ≫ W.hom = p ≫ polarizedChartMap pair i)
    (hj : k ≫ W.hom = q ≫ polarizedChartMap pair j)
    (s : logStructure.monoidSheaf.obj.obj (op W)),
    E.logTheta i j T a p q hp hq ((chartMap i).sectionMap W (Scheme.Etale.mk p) k hi s) =
      (chartMap j).sectionMap W (Scheme.Etale.mk q) k hj s

/-- One global polarized log isomorphism respecting the base and all labelled charts.
Strictness over the scheme isomorphism makes the log map an isomorphism, including
its unique inverse, without choosing a second inverse datum.
Source: ILO VIII 3.3.8; Stacks Tag 023Q and full faithfulness in Tag 04W8
(blueprint: lem-trf-polarized-fine-log-etale-descent). -/
structure PolarizedFineLogRealizationIso {S : FineLogScheme.{u}} {I : Type v}
    {U : I → Scheme.{u}} {uMap : ∀ i, U i ⟶ S.scheme} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ U i} {L : ∀ i, (X i).Modules}
    {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}
    {D : PolarizedSchemeEtaleDescentDatum S.scheme I U uMap X f L hL}
    {E : PolarizedFineLogDescentDatum S D} (d d' : PolarizedFineLogRealization E) where
  pairIso : PolarizedDescentPairIso d.pair d'.pair
  logMap : d.logStructure.HomAlong d'.logStructure pairIso.schemeIso.hom
  strict : logMap.IsStrictEtale
  overBase : logMap.CompEq d'.map d.map
  chart : ∀ i, (d.chartMap i).CompEq logMap (d'.chartMap i)

/-- Morphisms of fine log schemes over `S` glue uniquely for strict étale source covers.
Agreement on double overlaps is expressed by all cones of fine log schemes to the two
cover members. This is exactly equality on the strict pullback, which is itself fine
and locally Noetherian; every such cone factors through it.
Source: ILO VI 1.1, VIII 3.3.8; Stacks Tag 023Q
(blueprint: lem-trf-polarized-fine-log-etale-descent). -/
def FineLogMorphismsAreStrictEtaleLocal (S : FineLogScheme.{u}) : Prop :=
  ∀ (T Z : FineLogScheme.{u}) (t : T.Hom S) (z : Z.Hom S)
    (A : Type w) (Tₐ : A → FineLogScheme.{u}) (q : ∀ a, (Tₐ a).Hom T),
    (∀ a, (q a).logMap.IsStrictEtale) →
    (∀ x : T.scheme, ∃ (a : A) (y : (Tₐ a).scheme), (q a).base y = x) →
    ∀ g : ∀ a, (Tₐ a).Hom Z,
      (∀ a, (g a).CompositesEq z (q a) t) →
      (∀ (a b : A) (R : FineLogScheme.{u}) (r : R.Hom (Tₐ a)) (s : R.Hom (Tₐ b)),
        r.CompositesEq (q a) s (q b) → r.CompositesEq (g a) s (g b)) →
      ∃! h : T.Hom Z, h.CompEq z t ∧ ∀ a, (q a).CompEq h (g a)

/-- Effective polarized fine-log descent, conditional fs descent, unique compatible
isomorphism, and locality of log morphisms for the strict étale source topology.
Source: ILO VI 1.1 and VIII 3.3.8, printed pp. 69, 107--108; Stacks Tags 0D3C,
02WW, 04W8, 034C and 023Q (blueprint: lem-trf-polarized-fine-log-etale-descent).

Proof:
1. Apply lem-trf-polarized-scheme-etale-descent, forgetting log structures. Its normalized
   theta and lambda cocycles and its affine-local ampleness hypothesis give the scheme,
   invertible module and all labelled scheme and module identifications.
2. The chart maps X_i → X are the base changes of U_i → S. By
   lem-weil-pbc-etale-covering-base-change they form a jointly surjective étale cover.
   Apply lem-trf-etale-local-noetherian-descent to make X locally Noetherian.
3. The given log transitions live on X_i ×_X X_j by the scheme realization equations.
   Their naturality, identity and cocycle give the datum for
   lem-trf-fine-log-structure-etale-descent. Glue a fine log structure and its strict charts.
4. Apply the arbitrary-monoid-sheaf map clause of the same lemma to f⁻¹ M_S → M_X:
   the local maps agree by overBase. The result is the required log map over S.
5. If every local log structure is fs, the saturated-chart clause of the same lemma
   gives fs charts for the descended log structure.
6. For two descents, lem-weil-pbc-fpqc-finer-than-etale and
   lem-weil-pbc-fpqc-representable-descent glue the chart comparisons and their inverses.
   Scheme uniqueness forces the comparison over S. Polarized scheme descent supplies
   the compatible line-module isomorphism. The arbitrary-monoid-sheaf clause glues the
   log comparisons and their inverses; uniqueness proves their inverse and base equations.
   Every compatible isomorphism has these same scheme, line and log maps.
7. For the final morphism assertion, apply the same two fpqc lemmas to glue the underlying
   local maps T_a → Z. Their composites to S agree with t, hence the result is over S.
8. Strictness identifies M_{T_a} with the restriction of M_T. The local log maps thus
   give maps g⁻¹ M_Z → M_T on the cover, agreeing on its double overlaps. Apply the
   arbitrary-monoid-sheaf clause to glue them uniquely. Their composites from M_S agree
   locally, hence globally by the same uniqueness. Scheme and log-map uniqueness together
   prove the uniqueness of the log S-morphism. -/
theorem exists_polarizedFineLog_of_etaleDescent (S : FineLogScheme.{u}) :
    (∀ (I : Type v) (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S.scheme)
      (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ U i) (L : ∀ i, (X i).Modules)
      (hL : ∀ i, Scheme.Modules.IsInvertible (L i))
      (D : PolarizedSchemeEtaleDescentDatum S.scheme I U uMap X f L hL)
      (E : PolarizedFineLogDescentDatum S D),
      ∃ d : PolarizedFineLogRealization E,
        ((∀ i, (E.localLog i).IsFineSaturated) → d.logStructure.IsFineSaturated) ∧
        ∀ d' : PolarizedFineLogRealization E,
          ∃ e : PolarizedFineLogRealizationIso d d',
            ∀ e' : PolarizedFineLogRealizationIso d d', e' = e) ∧
    FineLogMorphismsAreStrictEtaleLocal.{u, w} S := by
  sorry

end AlgebraicGeometry
