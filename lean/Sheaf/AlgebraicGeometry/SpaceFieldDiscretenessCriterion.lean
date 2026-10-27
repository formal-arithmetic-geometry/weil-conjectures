/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Discreteness and local quasi-finiteness over a field

Source: Stacks Project, Decent Spaces, Tags 0ACA and 088J
(blueprint: lem-sfb-space-field-discreteness-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic space locally of finite type over a field, the atlas topology is
 discrete exactly when every representable étale scheme chart is locally quasi-finite
 over that field. If the relative diagonal is representable by closed immersions, a
 finite point set is discrete. No quasi-compactness or nonemptiness is assumed.

Source: Stacks Project, Decent Spaces, Tag 0ACA, (2) iff (5) and (1) implies (2),
with Tag 088J for the separated case
(blueprint: lem-sfb-space-field-discreteness-criterion).

Proof:
1. Regard X as its discrete fibred groupoid. Its sheaf condition, representable
   diagonal and étale atlas make it Deligne--Mumford
   (def-trf-algebraic-space, def-sfb-stable-pointed-moduli-groupoids).
   The finite-type and point-topology notions agree with the stack notions by
   lem-sfb-stack-finite-type-calculus and lem-sfb-stack-point-topology.
   Apply lem-sfb-dm-field-etale-chart-quasifinite to get the forward implication.
2. Conversely, choose a point-surjective open étale atlas by
   lem-a1-space-affine-etale-cover. Local quasi-finiteness of each chart and
   lem-weil-pbc-quasi-finite-at-point-isolated make each chart singleton open:
   the fibre over the unique point of Spec k is the whole chart. Its image is
   an open singleton in X. Surjectivity proves discreteness.
3. For the last clause factor the absolute diagonal through X ×_k X.
   The second map to X ×_Z X is a base change of the field diagonal, induced by
   the surjection k ⊗_Z k → k. Use def-weil-closed-immersion,
   lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-closed-immersion-base-change and lem-weil-pbc-closed-immersion-comp.
   Affine tests are spectra of quotient rings, hence quasi-compact by
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact. This proves absolute
   quasi-separatedness as needed by lem-sfb-space-qc-etale-fibre-bound.
4. For an affine étale chart V, that bound gives finite geometric fibres.
   Choose geometric representatives using def-weil-algebraic-closure.
   By lem-a1-space-point-open-calculus each geometric fibre maps onto its point
   fibre. Thus the point fibres are finite, and finite |X| makes |V| finite.
5. The chart is locally of finite type. By pqf-lem-locqf-fibre-discrete its
   scheme fibre over the field is discrete; def-pc-scheme-fibre identifies its
   topology with that of V. Refine the atlas by affine open components as in
   lem-a1-space-affine-etale-cover. These remain representable étale charts:
   scheme base changes are open subschemes of the original chart base changes,
   and étaleness (def-weil-etale-morphism) is local on the source.
   Their open point maps send open singletons to open singletons covering X.
   For the empty space the assertions are vacuous; no finite atlas is needed. -/
theorem space_field_discreteness_criterion {S : Scheme.{u}} (k : Type u) [Field k]
    (s : Spec (CommRingCat.of k) ⟶ S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj (Over.mk s))
    (hft : ∀ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
      IsEtale a → LocallyOfFiniteType (yoneda.preimage (a ≫ f)).left) :
    (DiscreteTopology (Point X.obj.obj) ↔
      ∀ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
        IsEtale a → (yoneda.preimage (a ≫ f)).left.IsLocallyQuasiFinite) ∧
    (IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f) →
      Finite (Point X.obj.obj) → DiscreteTopology (Point X.obj.obj)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
