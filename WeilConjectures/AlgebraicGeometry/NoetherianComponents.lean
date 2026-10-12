/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Irreducible components of Noetherian schemes, flat open maps, normal étale schemes

Three elementary facts used by the Noetherian theory of constructible étale sheaves:

- `AlgebraicGeometry.Scheme.finite_irreducibleComponents` (blueprint
  `lem-weil-pbc-noetherian-finite-components`): a Noetherian scheme has finitely many
  irreducible components.
- `AlgebraicGeometry.universallyOpen_of_flat_of_locallyOfFinitePresentation` (blueprint
  `lem-weil-pbc-flat-lfp-open`): a flat morphism locally of finite presentation is universally
  open, in particular open (`AlgebraicGeometry.Scheme.Hom.isOpenMap`).
- `AlgebraicGeometry.Scheme.exists_isClopen_isIntegral_of_etale` (blueprint
  `lem-fin-etale-normal-components`): a Noetherian scheme étale over a normal integral scheme is
  a finite disjoint union of open and closed normal integral subschemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `lem-weil-pbc-noetherian-finite-components`: Finitely many irreducible components.

A Noetherian scheme has finitely many irreducible components. -/
theorem Scheme.finite_irreducibleComponents (X : Scheme.{u}) [IsNoetherian X] :
    (irreducibleComponents X).Finite :=
  TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- Blueprint `lem-weil-pbc-flat-lfp-open`: Flat finite-presentation morphisms are open.

A flat morphism locally of finite presentation is universally open: it is open, and so is every
base change of it. This is Mathlib's `AlgebraicGeometry.UniversallyOpen.of_flat`. -/
theorem universallyOpen_of_flat_of_locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] : UniversallyOpen f :=
  UniversallyOpen.of_flat f

/-- Blueprint `lem-fin-etale-normal-components`: Normal components after étale pullback.

Let `f : W ⟶ Y` be étale with `W` Noetherian and `Y` normal integral (an integral scheme all
of whose local rings are integrally closed). Then `W` is a finite disjoint union of open and
closed subschemes `W_a` which are normal integral. -/
theorem Scheme.exists_isClopen_isIntegral_of_etale {W Y : Scheme.{u}} (f : W ⟶ Y) [Etale f]
    [IsNoetherian W] [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃ (n : ℕ) (U : Fin n → W.Opens), (∀ a, IsClopen (U a : Set W)) ∧
      Pairwise (fun a b ↦ Disjoint (U a) (U b)) ∧ ⨆ a, U a = ⊤ ∧
      ∀ a, IsIntegral (U a).toScheme ∧
        ∀ w : (U a).toScheme, IsIntegrallyClosed ((U a).toScheme.presheaf.stalk w) :=
  sorry

end AlgebraicGeometry
