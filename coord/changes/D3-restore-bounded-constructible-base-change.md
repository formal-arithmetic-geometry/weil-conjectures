# AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleBaseChangeOfPreserves

## Reason

Restore the missing module assigned by coord/rework.tsv (cluster-restore reversion,
2026-10-20). The authoritative archive contains four complete definitions and zero holes.
The live source is absent, although its node attachment and archived consumer remain.
Restoring this source repairs that missing interface; this is not a proof-hole closure.

## Old

The live path lean/Sheaf/Paper/BoundedConstructibleBaseChange.lean is absent.
The unchanged authoritative source is preserved at
quarantine/Sheaf/Paper/BoundedConstructibleBaseChange.lean. Its complete contents,
restored verbatim by this delivery, are quoted in New below.

## New

Restore the live path with exactly the archived source:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!
# Base change for every coefficient with constructible pushforward

Source: the blueprint, `sec-six-functors-basics`, unit `sk-def-sfb-base-change-morphism`
(blueprint: sk-def-sfb-base-change-morphism).

The pullback comparison is the existing `boundedConstructiblePullbackSquareComparison`.
The three steps below use the conditional restricted pushforward and its actual restricted
adjunction, with precisely the unit--comparison--counit formula of the source. The imported
coefficient constructions include the finite-subextension-valued condensed algebraic closure.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (H : PreservesBoundedConstructiblePushforwards Λ k)

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- Insert the unit of `Lf'^* ⊣ Rf'_*` after `Lg^* Rf_*`.
Source: blueprint `sk-def-sfb-base-change-morphism`, first step
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeUnitStepOfPreserves :
    boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H f' ℓ).unit

variable {f g f' g'} in
/-- Transport the unit-inserted functor by the canonical pullback-square comparison, built
from the two composition isomorphisms and the equality in `sq`.
Source: blueprint `sk-def-sfb-base-change-morphism`, second step
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeSquareStepOfPreserves (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') ≅
      (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') :=
  Functor.squareTransport (boundedConstructibleLowerStarOfPreserves Λ H f)
    (boundedConstructibleLowerStarOfPreserves Λ H f')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq)

/-- Contract the counit of `Lf^* ⊣ Rf_*` under `Lg'^*` and `Rf'_*`.
Source: blueprint `sk-def-sfb-base-change-morphism`, third step
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeCounitStepOfPreserves :
    (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H f ℓ).counit
    (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The base-change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*`, in diagrammatic composition order,
for every commutative square and every commutative condensed ring whose derived pushforwards
preserve bounded constructible complexes. Its data are the specified unit insertion,
canonical square transport and counit contraction, with no cartesian or proper hypothesis.
Source: blueprint unit `sk-def-sfb-base-change-morphism`
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeOfPreserves (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f' :=
  boundedConstructibleBaseChangeUnitStepOfPreserves Λ ℓ H f g f' ≫
    (boundedConstructibleBaseChangeSquareStepOfPreserves Λ ℓ H sq).hom ≫
      boundedConstructibleBaseChangeCounitStepOfPreserves Λ ℓ H f f' g'

end AlgebraicGeometry.ProEtale.CondensedRing
```

All four signatures, bodies, public imports, universes and attributes are unchanged from
the archive. Pushforward preservation remains the explicit hypothesis H for arbitrary
commutative condensed coefficients. The square is only commutative. The transformation
is the actual restricted adjunction unit, canonical pullback comparison, and counit.
The imported comparison keeps its existing upstream declaration and definition.

## Users

Source-only tools/downstream.py --allow-missing reports zero live downstream modules and
zero live uses of boundedConstructibleBaseChangeOfPreserves. A second scan of both live
roots and both quarantine roots finds the archived direct consumer listed below. The
other three restored names have no external source use in those roots.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed; not edited | Archived public importer. Its preservation specialization and IsIso assertion on the actual exchange component retain identical types and meanings; no adaptation. |

The unchanged consumer's use at .app K is checked by a separate scratch compilation of
that component type. A further scratch equality uses the existing upstream unit-square-counit theorem, then rfl,
to check that for finiteness coefficients the OfPreserves map equals the existing upstream
boundedConstructibleBaseChange. The upstream map has no_expose, so a bare rfl is insufficient.
The complete archived consumer is not restored or changed in this delivery.

The current node's Lean attachment and mathematical statement already describe these exact
definitions; all node fields and dependency edges are retained. No target statement or
meaning changes, so no target semantic review is reopened by a definition change.

## Status

landed 20261021T020103-L-2584121 2026-10-21 (merge of deliver/D3/Sheaf.Paper.BoundedConstructibleBaseChange)
