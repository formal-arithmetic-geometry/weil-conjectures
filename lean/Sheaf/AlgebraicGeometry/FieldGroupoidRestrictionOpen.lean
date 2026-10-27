/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidDoubleRestriction
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Restriction of an absolute field groupoid

Source: Stacks Project, Tags 02VB and 04LQ
(blueprint: lem-sfb-field-groupoid-restriction-open).

The arrow scheme is `(B ×[U] R) ×[U] B`, with target the first endpoint and
source the last endpoint. The middle-coordinate identities and groupoid laws
specify the identity, inverse and composition uniquely, hence give exactly the
usual formulas on triples over every test scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The middle arrow projection from the restriction of a scheme groupoid.
Source: Stacks Project, Tag 02VB, and the dotted arrow of Tag 04LQ
(blueprint: lem-sfb-field-groupoid-restriction-open). This is the actual composite
of the two fibre-product projections, without any choice of an arbitrary map. -/
noncomputable def groupoidRestrictionMiddle {U R B : Scheme.{u}}
    (s t : R ⟶ U) (q : B ⟶ U) : pullback (groupoidSaturationMap s t q) q ⟶ R :=
  pullback.fst (groupoidSaturationMap s t q) q ≫ pullback.snd q t

/-- Arbitrary field restriction gives the usual groupoid operations and an open,
surjective middle projection. Source: Stacks Project, Tags 02VB and 04LQ
(blueprint: lem-sfb-field-groupoid-restriction-open).

Here `q` is written out as `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
The existential operations have prescribed middle coordinates. Their endpoint
coordinates are forced by `IsGroupoidScheme`: identity has equal endpoints,
inverse exchanges them, and a composite retains the outer endpoints. Thus they
are exactly `(u,e(q(u)),u)`, `(v,i(r),u)` and `(u,c(r,r'),w)` on triples.
In the composition clause, `h` is composability upstairs and `hm` is the induced
composability downstairs. The pullback equations imply the existence of `hm`
for every `h`; universal quantification over its proof does not weaken the clause.
All schemes and fields lie in a common arbitrary ambient universe.

Proof, following the five steps of the DAG node:
1. Construct identity, inverse and composition by the two pullback universal
   properties. For identity use `(id,e q,id)`. For inverse exchange endpoints
   and apply `i` in the middle. For composable triples the middle arrows satisfy
   `s(r) = q(v) = t(r')`; compose them using `c` and retain the outer endpoints.
   The source and target equalities of the original groupoid ensure that each
   constructed map lands in the required pullback (def-pc-fibre-product and
   def-a1-groupoid-scheme). These morphisms give the displayed middle formulas.
2. On every test scheme check units, inverse laws and associativity in the middle
   coordinate using the original groupoid axioms. Endpoints agree identically.
   Pullback uniqueness gives the scheme equalities. Naturality follows because
   all operations are morphisms (def-a1-groupoid-scheme).
3. Put `B = Spec K ×[Spec k] R`, using `t`. The restricted arrows are precisely
   `B ×[Spec k] Spec K`, with `B → Spec k` induced by `s`. The middle projection
   factors through `B`, and each factor is a base change of `q`. Field spectra
   have exactly one point, so `q` is surjective (def-weil-affine-spectrum).
4. Apply lem-sc-scheme-over-field-universally-open to both base changes of `q`,
   first along `t`, then along `B → Spec k`. Apply
   lem-weil-pbc-surjective-base-change to the same two squares. Both factors are
   open and surjective. These results impose no finiteness condition.
5. Composites of open maps are open, since the image of an open is successively
   open. Composites of surjections are surjective, by lifting a point twice.
   This proves the two topological conclusions for the actual middle projection.
No relative equality `s = t`, finiteness, separability or perfection is assumed. -/
theorem field_groupoid_restriction_open
    (k K : Type u) [Field k] [Field K] [Algebra k K] {R : Scheme.{u}}
    (s t : R ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : IsGroupoidScheme s t e i c) :
    (∃ (eK : Spec (CommRingCat.of K) ⟶
        pullback (groupoidSaturationMap s t
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (iK : pullback (groupoidSaturationMap s t
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
        pullback (groupoidSaturationMap s t
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (cK : pullback
        (groupoidRestrictionSource s t (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (groupoidRestrictionTarget s t (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⟶
        pullback (groupoidSaturationMap s t
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      IsGroupoidScheme
        (groupoidRestrictionSource s t (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (groupoidRestrictionTarget s t (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        eK iK cK ∧
      eK ≫ groupoidRestrictionMiddle s t
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ e ∧
      iK ≫ groupoidRestrictionMiddle s t
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          groupoidRestrictionMiddle s t
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ i ∧
      (∀ (T : Scheme.{u})
        (a b : T ⟶ pullback (groupoidSaturationMap s t
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (h : a ≫ groupoidRestrictionSource s t
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          b ≫ groupoidRestrictionTarget s t
            (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (hm : (a ≫ groupoidRestrictionMiddle s t
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫ s =
          (b ≫ groupoidRestrictionMiddle s t
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫ t),
        (pullback.lift a b h ≫ cK) ≫ groupoidRestrictionMiddle s t
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          pullback.lift
            (a ≫ groupoidRestrictionMiddle s t
              (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (b ≫ groupoidRestrictionMiddle s t
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hm ≫ c)) ∧
    Surjective (groupoidRestrictionMiddle s t
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
    IsOpenMap (groupoidRestrictionMiddle s t
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

end AlgebraicGeometry
