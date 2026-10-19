/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Monomial modules of stable subsets

Source: the basis construction in the proof of `lem-per-monomial-module-tor-devissage`,
Step 4, used for ILO, Travaux de Gabber, Exposé X 1.3(vii) and Lemma 1.5
(blueprint: def-per-monomial-subset-span).
-/

@[expose] public section

universe u v

namespace AddMonoidAlgebra

/-- The group algebra with scalars restricted along the given monoid map.
Its monomial action is `z^q [t] = [h(q) + t]`.
Source: ILO Exposé X 1.3(vii), Lemma 1.5, and the monomial basis construction
(blueprint: def-per-monomial-subset-span). -/
noncomputable def monomialAmbient {Q : Type u} [AddCommMonoid Q]
    {G : Type v} [AddCommGroup G] (h : Q →+ G) : ModuleCat.{v} (AddMonoidAlgebra ℤ Q) :=
  (ModuleCat.restrictScalars (mapDomainRingHom ℤ h)).obj
    (ModuleCat.of (AddMonoidAlgebra ℤ G) (AddMonoidAlgebra ℤ G))

/-- The monomial span of a subset of the ambient group. For a subset stable under
translation by `h(Q)`, this is precisely the free abelian group on that subset,
with the translation action of `Z[Q]`. The empty subset gives the zero submodule.
Source: ILO Exposé X 1.3(vii), Lemma 1.5, and the monomial basis construction
(blueprint: def-per-monomial-subset-span). -/
noncomputable def monomialSubsetSpan {Q : Type u} [AddCommMonoid Q]
    {G : Type v} [AddCommGroup G] (h : Q →+ G) (T : Set G) :
    Submodule (AddMonoidAlgebra ℤ Q) (monomialAmbient h) :=
  Submodule.span (AddMonoidAlgebra ℤ Q)
    ((fun t : G ↦ (single t (1 : ℤ) : monomialAmbient h)) '' T)

end AddMonoidAlgebra
