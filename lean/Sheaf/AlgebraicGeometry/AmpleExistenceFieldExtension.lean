/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent
import Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-! # Existence of ample invertible modules descends along field extensions

Source: Stacks Project, Varieties, Tag 0BDC, lemma-ample-after-field-extension
(blueprint: lem-sfb-ample-existence-field-extension).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- If a scheme over a field acquires an absolutely ample invertible module after
an arbitrary field extension, it already admits an absolutely ample invertible module.
Only existence is asserted; the resulting module need not pull back to the supplied one.

Source: Stacks Project, Varieties, Tag 0BDC, lemma-ample-after-field-extension
(blueprint: lem-sfb-ample-existence-field-extension).

Proof:
1. Choose an ample invertible module `L` on `X_K`. Its ampleness makes `X_K`
   quasi-compact by `def-weil-pbc-ample-invertible-module`. The field-extension
   map and its base changes are surjective by `lem-pc-field-extension-surjective`
   and `lem-weil-pbc-surjective-base-change`. Thus `X` is quasi-compact by
   `lem-weil-pbc-continuous-image-quasi-compact`.
2. By `lem-weil-pbc-ample-scheme-separated` and `lem-pc-separated-quasi-separated`,
   `X_K` is quasi-separated. The scalar extensions of affine opens are affine by
   `lem-weil-pbc-fibre-product-affine-spectra`. Their intersections are quasi-compact
   by `lem-weil-pbc-quasi-separated-affine-cover-criterion`(1), and surject onto the
   corresponding intersections on `X`. Apply
   `lem-weil-pbc-continuous-image-quasi-compact` and clause (2) of that criterion
   to the cover by all affine opens to conclude that `X` is quasi-separated.
3. Write `K` as the directed union of its finitely generated `k`-subalgebras `A_i`.
   The system is small and nonempty, contains `k`, and any two finite generating
   sets lie in their finitely generated union. By `lem-weil-pbc-limit-affine-transition`
   and `lem-weil-pbc-scheme-over-limit`, the schemes `X_i = X ×_k Spec A_i` have
   affine transitions and limit `X_K`. Their projections to `X` are affine by
   `lem-weil-pbc-affine-morphism-permanence`(1), hence quasi-compact and
   quasi-separated by clause (3). They are therefore quasi-compact and
   quasi-separated by `lem-weil-pbc-qcqs-morphism-permanence`(2).
4. By `lem-trf-invertible-affine-limit-descent`, descend `L` to an invertible module
   `L_i` at some stage. By `lem-trf-ample-affine-limit-descent`, after increasing
   that stage its pullback is ample. These are the absolute ampleness predicates;
   no finite-type assumption on `X` is used.
5. The algebra `A_i` is nonzero, being a subalgebra of a field. By
   `lem-weil-pbc-proper-ideal-contained-in-maximal`, choose a maximal ideal `m`.
   Its residue field `k'` is a finitely generated `k`-algebra, hence finite over `k`
   by `lem-weil-pbc-zariski-lemma`.
6. The quotient map gives a closed immersion `Spec k' ⟶ Spec A_i` by
   `def-weil-closed-immersion`; its base change `X_{k'} ⟶ X_i` is a closed immersion
   by `lem-weil-pbc-closed-immersion-base-change`. The restriction of `L_i` is ample
   by `lem-trf-ample-restrict-closed-immersion`.
7. A finite `k`-basis of `k'` gives, on every affine open `Spec B` of `X`, a finite
   free `B`-basis of `B ⊗[k] k'`, using `lem-weil-pbc-fibre-product-affine-spectra`.
   It is flat by `lem-sc-affine-standard-cover-finite-free-local-fp-flat`. If the
   multiplication constants are `c_rst` and `1 = ∑ u_t e_t`, its presentation is
   `B[T_1,...,T_d]/(T_r*T_s - ∑ c_rst*T_t, 1 - ∑ u_t*T_t)`: the relations reduce
   every polynomial to a linear combination of the `T_t`, and independence of the
   basis makes the resulting surjection injective. Thus `X_{k'} ⟶ X` is finite,
   flat and locally of finite presentation, hence finite locally free by
   `def-pc-finite-locally-free`. It is surjective by
   `lem-pc-field-extension-surjective` and `lem-weil-pbc-surjective-base-change`.
8. Apply `lem-sfb-finite-locally-free-ample-existence` to this surjective finite
   locally free morphism and the ample module from step 6. This produces an ample
   invertible module on `X`, with no assertion that it pulls back to `L`.
-/
theorem exists_isAmple_of_field_extension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hK : ∃ L : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules,
      ∃ hL : L.IsInvertible,
        @IsAmple (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L hL) :
    ∃ M : X.Modules, ∃ hM : M.IsInvertible, @IsAmple X M hM := by
  sorry

end AlgebraicGeometry.Scheme.Modules
