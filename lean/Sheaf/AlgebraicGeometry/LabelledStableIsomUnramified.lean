/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProjectiveCurveIsomGraphs
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields
import Mathlib.Algebra.DualNumber
import Sheaf.AlgebraicGeometry.GeometricTangentUnramified
import Sheaf.AlgebraicGeometry.ReducedNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The parameter scheme of labelled stable-curve isomorphisms

Source: Stacks Project, moduli-curves.tex, Tag 0DSQ, scheme realization by projective
isomorphism graphs and closed marking equalizers; curves.tex, Tags 0E67 and 0E68;
varieties.tex, Tag 0B2G; de Jong (1997), §3.8
(blueprint: lem-sfb-labelled-stable-isom-unramified).

The subtype consists of isomorphisms over the test scheme satisfying equality of
marked sections as scheme morphisms. Naturality is expressed by the canonical
base-change maps. The universal labelled isomorphism is `e J (𝟙 J)`; naturality
with a map `a : T ⟶ J` says that `e T a` is its pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The fixed-permutation labelled Isom functor of two stable pointed curves over a
locally Noetherian base is represented by a separated finite-type unramified scheme.
The bijections apply to every test scheme, and their naturality supplies the universal
labelled isomorphism `e J (𝟙 J)`. There is no connectedness or reducedness restriction
on a test scheme, and `Fin 0` has its unique permutation.

Source: Stacks Project, Tag 0DSQ with projective graph realization and closed marking
equalizers, Tags 0E67, 0E68 and 0B2G; de Jong (1997), §3.8
(blueprint: lem-sfb-labelled-stable-isom-unramified).

Proof plan:
1. Over affine opens of S, finite generators of the projective-bundle presentations
   embed both curves into finite projective spaces
   (lem-trf-projective-bundle-affine-presentations,
   lem-weil-pbc-closed-immersion-products). They are flat and finitely presented by
   def-sfb-stable-pointed-curve, with one-dimensional geometric fibres. Projective
   implies proper and separated (lem-pc-projective-proper); separatedness descends
   from the base-open cover (lem-sfb-separated-lfp-target-open-locality).
2. Apply lem-sfb-projective-curve-isom-graphs on these opens. The universal graph
   gives its isomorphism by its second projection composed with the inverse first
   projection. Glue these natural graph representatives using
   lem-sfb-isom-graph-representatives-zariski-gluing. The unlabelled parameter is
   separated and finitely presented, hence finite type.
3. For each label pull back the closed diagonal of W' along the two maps from the
   unlabelled parameter: the universal isomorphism applied to the source marking,
   and the permuted target marking. Intersect these finitely many closed equalizers
   (def-pc-fibre-product, lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-closed-immersion-products); for no labels take the whole parameter.
   Their universal properties identify maps from every test scheme with exactly
   the labelled isomorphisms, naturally under pullback. Restrict the universal graph.
4. The closed immersion into the unlabelled parameter is proper
   (lem-weil-pbc-closed-immersion-proper), so composition is finite type
   (lem-sfb-finite-type-composition-base-change). Its diagonal is the pullback of
   the unlabelled diagonal, using that a closed immersion is a monomorphism.
   Hence the labelled parameter remains separated.
5. At a geometric point an isomorphism over dual numbers reducing to u0 differs
   from the constant extension of u0 by an infinitesimal automorphism fixing all
   markings. The geometric fibre is reduced nodal, proper, connected and nonempty.
   Its markings are distinct and smooth by stability and smooth base change.
   Its canonical component normalizations are smooth projective connected curves
   (lem-sfb-nodal-completed-normalization-model, def-weil-pbc-reduced-normalization).
   Stability gives 2g-2 plus the number of special points positive on each component:
   at least three special points in genus zero, at least one in genus one, and
   automatic positivity in higher genus. Thus
   lem-sfb-marked-nodal-infinitesimal-fields makes that automorphism the identity.
6. The natural representing bijections identify all geometric dual-number lifts
   through a fixed point with this unique constant lift. Apply
   lem-sfb-geometric-tangent-unramified to the finite-type parameter. Empty fibres
   satisfy the criterion vacuously. The equalizers represent scheme morphism
   equations on arbitrary tests, including disconnected and nonreduced schemes;
   dual numbers are used only to test unramifiedness. -/
theorem exists_labelled_stable_isom_unramified
    {S W W' : Scheme.{u}} [IsLocallyNoetherian S]
    (f : W ⟶ S) (f' : W' ⟶ S) (n : ℕ)
    (s : Fin n → (S ⟶ W)) (s' : Fin n → (S ⟶ W'))
    (hs : ∀ i : Fin n, s i ≫ f = 𝟙 S) (hs' : ∀ i : Fin n, s' i ≫ f' = 𝟙 S)
    (hstable : IsStablePointedCurve f s hs)
    (hstable' : IsStablePointedCurve f' s' hs') (σ : Equiv.Perm (Fin n)) :
    ∃ J : Over S, IsSeparated J.hom ∧ LocallyOfFiniteType J.hom ∧
      QuasiCompact J.hom ∧ IsUnramified J.hom ∧
      ∃ e : ∀ T : Over S, (T ⟶ J) ≃
        {a : (Over.pullback T.hom).obj (Over.mk f) ≅
            (Over.pullback T.hom).obj (Over.mk f') //
          ∀ i : Fin n, f.baseChangeSection (s i) (hs i) T.hom ≫ a.hom.left =
            f'.baseChangeSection (s' (σ i)) (hs' (σ i)) T.hom},
        ∀ (T' T : Over S) (h : T' ⟶ T) (a : T ⟶ J),
          baseChangeMap f h ≫ (e T a).val.hom.left =
            (e T' (h ≫ a)).val.hom.left ≫ baseChangeMap f' h := by
  sorry

end AlgebraicGeometry
