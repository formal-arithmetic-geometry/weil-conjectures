/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.GenericFiniteAlgebraSplitting

/-!
# Scheme-level generic splitting of a finite morphism

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-generic-finite-scheme-splitting).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A finite map over an integral Noetherian affine base has a dense open on every
subopen of which an etale surjective base change splits its source into finitely
many open components universally homeomorphic to the cover.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation;
steps 1 and 2 of `lem-weil-pbc-finite-map-generic-lisse-preservation`.
(blueprint: lem-weil-pbc-generic-finite-scheme-splitting).

Proof: Write S = Spec A and Z = Spec B, using affineness of finite morphisms.
Apply `lem-weil-pbc-generic-finite-algebra-splitting` to B over A. Its nonzero
c defines a dense principal open U, and its finite etale surjective algebra A'
provides the cover of U. The product decomposition of the reduced tensor algebra
identifies its spectrum with a finite disjoint union of spectra of the factors.
The reduction map is a universal homeomorphism, hence these open-and-closed
components lift uniquely to open-and-closed components of the unreduced source.
Their maps to Spec A' are finite universal homeomorphisms: reduction does not
change integrality, surjectivity, or universal injectivity. For V contained in U,
base change the cover and each component to V. Etaleness, finiteness, surjectivity,
and universal homeomorphisms survive this base change. The pulled-back components
are disjoint opens and cover the source. Their composite maps to the restricted
cover have the required property. If the finite algebra is zero, the source is
empty and the family has no components; the supremum of the empty family is top
in the lattice of opens of the empty source. The choice of U uses no sheaf. -/
theorem exists_dense_open_finite_scheme_splitting
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g] :
    ∃ U : S.Opens, Dense (U : Set S) ∧
      ∀ (V : S.Opens), V ≤ U →
        ∃ (T : Scheme.{u}) (p : T ⟶ V.toScheme),
          IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ (n : ℕ) (W : Fin n → (pullback g (p ≫ V.ι)).Opens),
            (⨆ i, W i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
            ∀ i, IsUniversalHomeomorphism
              ((W i).ι ≫ pullback.snd g (p ≫ V.ι)) := by sorry

end AlgebraicGeometry.Scheme
