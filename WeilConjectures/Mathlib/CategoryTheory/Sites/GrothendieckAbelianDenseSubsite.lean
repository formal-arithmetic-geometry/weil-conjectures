/-
Copyright (c) 2026 Weil Conjectures Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil Conjectures Contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Grothendieck abelian sheaf categories, along an essentially small dense subsite

`WeilConjectures/CategoryTheory/GrothendieckAbelian/Sheaf.lean` asserts, with a `sorry`, that
`A`-valued sheaves on the small `Q`-site of `P`-schemes form a Grothendieck abelian category
when `A` is Grothendieck abelian. Its docstring says the proof is "the site is essentially
small, so the sheaf category is equivalent to a category of sheaves on a small site, which is
Grothendieck abelian".

The small étale site is *provably not* essentially small, so that sentence cannot be taken at
face value. Mathlib reaches the étale case through the affine dense subsite
`AlgebraicGeometry.Scheme.AffineEtale.Spec` instead, and states the result inside a `variable`
block asking the coefficient category to be concrete
(`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`), which makes the whole chain look
concreteness-dependent.

It is not. **Concreteness is used only to produce `CategoryTheory.HasSheafify`**; the transport
of the Grothendieck abelian structure across a dense subsite asks nothing of `A` beyond
`Abelian` and `IsGrothendieckAbelian`. This file records that transport with the coefficient
hypotheses it really needs, and instantiates it at the small étale site of a scheme.

## Main results

* `CategoryTheory.Sheaf.isGrothendieckAbelian_of_isDenseSubsite`: if `C` is essentially small,
  `G` is a dense subsite inclusion whose sheaf-pushforward is an equivalence, and `A` is
  Grothendieck abelian and admits sheafification on the small model of `J`, then `Sheaf K A` is
  Grothendieck abelian.
* `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_of_hasSheafify`: the
  instantiation at `AffineEtale.Spec S`, for any Grothendieck abelian `A`.

## Scope

Nothing here discharges the `sorry`. What remains is exactly one statement, with no algebraic
geometry in it — sheafification on a *genuinely small* site with Grothendieck abelian
coefficients. Mathlib has no such instance: its only construction of sheafification for a
general topology is the plus-plus construction of `Mathlib/CategoryTheory/Sites/LeftExact.lean`,
which needs `A` concrete. That statement is *also* the whole residue of the sheafification
`sorry` in `WeilConjectures/CategoryTheory/GrothendieckAbelian/HasSheafify.lean`, so the two
`sorry`s share one obligation rather than having one each.

The general-`P` site `P.Over ⊤ U` is not addressed: it has no reason to be essentially small and
no reason to carry an essentially small dense subsite, so the general-`P` statement is missing
more than a smallness binder — it is missing the dense-subsite datum that
`AlgebraicGeometry.Scheme.AffineEtale` supplies in the étale case.

## Implementation note

`IsGrothendieckAbelian (Sheaf K A)` cannot even be *stated* without `Abelian (Sheaf K A)`, which
needs `HasSheafify K A`. The `haveI`s therefore appear in the statement as well as in the proof;
this is the `AB5OfSize_of_univLE` idiom. Supplying the sheafification hypothesis as a term
argument instead makes the statement fail to elaborate, with an error that reads like a missing
instance and is not one.
-/

@[expose] public section

universe u' u u₂ u₃

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.Sheaf

/-- Transport of the Grothendieck abelian structure on a sheaf category along an essentially
small dense subsite whose sheaf-pushforward functor is an equivalence.

The coefficient category is asked only to be abelian, Grothendieck abelian, and to admit
sheafification on the small model of `J`; in particular it is **not** asked to be concrete. -/
theorem isGrothendieckAbelian_of_isDenseSubsite {C : Type u₂} [Category.{u} C] {D : Type u₃}
    [Category.{u} D] (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [EssentiallySmall.{u} C] [G.IsDenseSubsite J K]
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A]
    [(G.sheafPushforwardContinuous A J K).IsEquivalence] :
    haveI : HasSheafify J A := hasSheafifyEssentiallySmallSite.{u} _ _
    haveI : HasSheafify K A := Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K G
    IsGrothendieckAbelian.{u} (Sheaf K A) :=
  haveI : HasSheafify J A := hasSheafifyEssentiallySmallSite.{u} _ _
  haveI : HasSheafify K A := Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K G
  haveI : IsGrothendieckAbelian.{u} (Sheaf J A) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  IsGrothendieckAbelian.of_equivalence
    (G.sheafPushforwardContinuous A J K).asEquivalence.symm

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

/-- The category of `A`-valued sheaves on the small étale site of a scheme is Grothendieck
abelian for **any** Grothendieck abelian coefficient category `A` admitting sheafification on
the small model of the affine étale site — no concreteness on `A` is required.

Mathlib's `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology` is this
statement inside a concrete `variable` block; the concreteness there serves only to discharge
the sheafification hypothesis. -/
theorem isGrothendieckAbelian_sheaf_smallEtaleTopology_of_hasSheafify (S : Scheme.{u})
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [HasSheafify ((equivSmallModel S.AffineEtale).inverse.inducedTopology
      (AffineEtale.topology S)) A] :
    haveI : HasSheafify (AffineEtale.topology S) A := hasSheafifyEssentiallySmallSite.{u} _ _
    haveI : HasSheafify S.smallEtaleTopology A :=
      Functor.IsDenseSubsite.hasSheafify_of_isEquivalence (AffineEtale.topology S)
        S.smallEtaleTopology (AffineEtale.Spec S)
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology A) :=
  Sheaf.isGrothendieckAbelian_of_isDenseSubsite (AffineEtale.topology S) S.smallEtaleTopology
    (AffineEtale.Spec S) A

end AlgebraicGeometry.Scheme
