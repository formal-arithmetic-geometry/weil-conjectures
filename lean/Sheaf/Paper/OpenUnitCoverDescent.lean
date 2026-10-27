/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull

/-!
# Descent of the actual derived open unit

Source: Stacks 08FI and 0D6F; localization and descent steps of the scalar-to-lisse
argument in blueprint direct-images paragraph (3).
(blueprint: lem-sfb-open-unit-cover-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- An open unit is invertible if the units on a pro-etale cover are invertible.
The open on each chart is formed directly over X; the canonical pullback associator
identifies it with the successive base change of the open on Y. The module N is arbitrary.

Source: Stacks, sites-cohomology.tex, restrict-K-injective-to-open (08FI) and
unbounded-cohomology-of-open (0D6F); blueprint six-functor stability, direct-images
paragraph (3), agent scalar-to-lisse sublemma, steps 1--4 and 7--8.
(blueprint: lem-sfb-open-unit-cover-descent).

Proof: Pass to section-ring module sheaves by the exact operations equivalence. Each
covering map is a site object, and its inverse image is exact slice restriction. Restrict
a K-injective resolution of the inverse image of N under the open: it remains K-injective
by the exact extension-by-zero adjoint. On a site object V of a chart, both the restricted
direct image and the direct image on the chart are the sections of that resolution on
V times_X U. The pullback associator is induced by the projections and gives the same
restriction map on sections. Hence this identifies the restricted unit, not just its
endpoints, with the unit for pullback.snd U.ι (cover.f i composed with a). Transport the
ordinary/K-injective comparison to the specified K-flat adjunction; its transpose is the
identity, so the identified unit is exactly the one in the statement. The hypothesis
makes every restricted unit invertible. Derived restrictions along a covering family
jointly reflect isomorphisms: exact restriction commutes with cohomology, the ordinary
covering restrictions detect isomorphisms of cohomology sheaves, and unbounded derived
isomorphisms are detected by all cohomology functors. Apply this to the unit and transport
back through the equivalence. An empty cover causes no exception since its base has only
zero sheaves. No local freeness or scalar cohomology assumption is used.
-/
theorem isIso_open_unit_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.Opens)
    (Y : Scheme.{u}) (a : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (hlocal : ∀ i : 𝒰.I₀,
      IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ
        (pullback.snd U.ι (𝒰.f i ≫ a))).unit.app
          ((DerivedCategory.singleFunctor _ 0).obj
            ((CondensedRing.upperStar Λ (𝒰.f i)).obj N)))) :
    IsIso ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ
      (pullback.snd U.ι a)).unit.app ((DerivedCategory.singleFunctor _ 0).obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale
