/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidDoubleRestriction
public import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange

/-!
# Perfect-field restriction of a morphism of field groupoids

Source: Stacks Project, Tag 04Q9, first proof paragraph; Tags 04LQ and 02VB
(blueprint: lem-sfb-field-groupoid-perfect-restriction).

The two groupoids are indexed by `Fin 2`. The existing restriction source and target
use the parenthesization `(V' ×[V] R) ×[V] V'`. The middle projection below forgets
both new endpoint coordinates. All operations are characterized by these coordinates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The arrow-coordinate projection of the restriction of an absolute groupoid.
Source: Stacks Project, Tags 02VB and 04LQ, dotted arrow in the restriction diagram
(blueprint: lem-sfb-field-groupoid-perfect-restriction). -/
noncomputable def groupoidRestrictionProjection {V R V' : Scheme.{u}}
    (s t : R ⟶ V) (g : V' ⟶ V) : pullback (groupoidSaturationMap s t g) g ⟶ R :=
  pullback.fst (groupoidSaturationMap s t g) g ≫ pullback.snd g t

/-- A morphism of absolute groupoids on a field spectrum restricts to a perfect field,
with the induced operations and arrow map, and homeomorphic arrow projections.
Source: Stacks Project, Tag 04Q9, first proof paragraph, with Tags 04LQ and 02VB
(blueprint: lem-sfb-field-groupoid-perfect-restriction).

The equation for `g` fixes the canonical spectrum map. The restricted sources and
 targets fix the endpoint coordinates. Their groupoid laws fix the endpoint formulas
for units, inverses and composition. The three displayed middle-coordinate formulas
therefore specify exactly `(x,e(gx),x)`, `(y,i(r),x)` and `(x,c(r,u),z)` on test points.
Both compatibility proofs for a composable pair are quantified: the pullback equations
ensure that the old compatibility exists whenever the new one does. Similarly, `hs'`
and `ht'` ensure that the map used in the last composition equation is the canonical
map on composable pairs. Its two endpoint equations and its projection equation specify
`a'(x,r,y) = (x,a(r),y)` uniquely. No finiteness assumption is present.

Proof, following the node:
1. By lem-weil-pbc-perfect-purely-inseparable-overfield choose a perfect purely
   inseparable extension K/k, for example the perfect closure inside an algebraic
   closure. In characteristic zero one may take k itself. Let g be its spectrum map.
2. On H-points of the iterated pullback use triples (x,r,y). Define the restricted
   source and target by y and x, the unit by (x,e(gx),x), inverse by (y,i(r),x), and
   composition by ((x,r,y),(y,u,z)) ↦ (x,c(r,u),z). The original source, target, unit
   and inverse equations give the pullback compatibilities; the universal property
   in def-pc-fibre-product constructs these as scheme morphisms.
3. The original groupoid identities give the restricted identities on all three
   coordinates. Associativity follows from c(c(r,u),v) = c(r,c(u,v)); pullback
   uniqueness gives equality of scheme morphisms. Naturality is precomposition.
4. Define a' on triples by (x,a(r),y). The five assumed operation compatibilities
   imply the corresponding restricted compatibilities coordinate by coordinate.
   Both composites to R₂ have middle coordinate a(r), proving the projection square.
5. For either j, the middle projection factors as two successive base changes of g,
   first along t j, then along the resulting source map. Each factor is a homeomorphism
   by lem-pc-homeo-pure-insep, so their composite is a homeomorphism. These arguments
   use no finite type, quasi-compactness or other finiteness condition. -/
theorem exists_perfect_field_groupoid_restriction
    (k : Type u) [Field k] (R : Fin 2 → Scheme.{u})
    (s t : ∀ j : Fin 2, R j ⟶ Spec (CommRingCat.of k))
    (e : ∀ j : Fin 2, Spec (CommRingCat.of k) ⟶ R j)
    (i : ∀ j : Fin 2, R j ⟶ R j) (c : ∀ j : Fin 2, pullback (s j) (t j) ⟶ R j)
    (hG : ∀ j : Fin 2, IsGroupoidScheme (s j) (t j) (e j) (i j) (c j))
    (a : R 0 ⟶ R 1) (hs : a ≫ s 1 = s 0) (ht : a ≫ t 1 = t 0)
    (he : e 0 ≫ a = e 1) (hi : i 0 ≫ a = a ≫ i 1)
    (hc : c 0 ≫ a = pullback.map (s 0) (t 0) (s 1) (t 1) a a
      (𝟙 (Spec (CommRingCat.of k)))
      ((Category.comp_id (s 0)).trans hs.symm)
      ((Category.comp_id (t 0)).trans ht.symm) ≫ c 1) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), PerfectField K ∧
      ∃ (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)),
        g = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧
        ∃ (e' : ∀ j : Fin 2, Spec (CommRingCat.of K) ⟶
            pullback (groupoidSaturationMap (s j) (t j) g) g)
          (i' : ∀ j : Fin 2, pullback (groupoidSaturationMap (s j) (t j) g) g ⟶
            pullback (groupoidSaturationMap (s j) (t j) g) g)
          (c' : ∀ j : Fin 2,
            pullback (groupoidRestrictionSource (s j) (t j) g)
              (groupoidRestrictionTarget (s j) (t j) g) ⟶
                pullback (groupoidSaturationMap (s j) (t j) g) g)
          (a' : pullback (groupoidSaturationMap (s 0) (t 0) g) g ⟶
            pullback (groupoidSaturationMap (s 1) (t 1) g) g),
          (∀ j : Fin 2,
            IsGroupoidScheme (groupoidRestrictionSource (s j) (t j) g)
              (groupoidRestrictionTarget (s j) (t j) g) (e' j) (i' j) (c' j) ∧
            e' j ≫ groupoidRestrictionProjection (s j) (t j) g = g ≫ e j ∧
            i' j ≫ groupoidRestrictionProjection (s j) (t j) g =
              groupoidRestrictionProjection (s j) (t j) g ≫ i j ∧
            (∀ (H : Scheme.{u})
              (r v : H ⟶ pullback (groupoidSaturationMap (s j) (t j) g) g)
              (h : r ≫ groupoidRestrictionSource (s j) (t j) g =
                v ≫ groupoidRestrictionTarget (s j) (t j) g)
              (h₀ : (r ≫ groupoidRestrictionProjection (s j) (t j) g) ≫ s j =
                (v ≫ groupoidRestrictionProjection (s j) (t j) g) ≫ t j),
              pullback.lift r v h ≫ c' j ≫ groupoidRestrictionProjection (s j) (t j) g =
                pullback.lift (r ≫ groupoidRestrictionProjection (s j) (t j) g)
                  (v ≫ groupoidRestrictionProjection (s j) (t j) g) h₀ ≫ c j) ∧
            IsHomeomorph (groupoidRestrictionProjection (s j) (t j) g).base) ∧
          ∃ (hs' : a' ≫ groupoidRestrictionSource (s 1) (t 1) g =
              groupoidRestrictionSource (s 0) (t 0) g)
            (ht' : a' ≫ groupoidRestrictionTarget (s 1) (t 1) g =
              groupoidRestrictionTarget (s 0) (t 0) g),
            e' 0 ≫ a' = e' 1 ∧ i' 0 ≫ a' = a' ≫ i' 1 ∧
            c' 0 ≫ a' =
              pullback.map (groupoidRestrictionSource (s 0) (t 0) g)
                (groupoidRestrictionTarget (s 0) (t 0) g)
                (groupoidRestrictionSource (s 1) (t 1) g)
                (groupoidRestrictionTarget (s 1) (t 1) g) a' a'
                (𝟙 (Spec (CommRingCat.of K)))
                ((Category.comp_id _).trans hs'.symm)
                ((Category.comp_id _).trans ht'.symm) ≫ c' 1 ∧
            a' ≫ groupoidRestrictionProjection (s 1) (t 1) g =
              groupoidRestrictionProjection (s 0) (t 0) g ≫ a := by
  sorry

end AlgebraicGeometry
