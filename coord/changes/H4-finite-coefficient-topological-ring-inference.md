# Finite coefficient topology proof inference

## Reason

The finite-level comparison is proved, but the item repeatedly exceeded its
60-second compile limit. A synchronous trace identified repeated inference of
`IsTopologicalRing (spEllQuotient ℓ E n)` (one call exceeded one second), and
repeated normalization of the completed integral limit in later transition proofs.

## Old

`spEllPointRing`, `spEllPointReduction`, and `spEllPointTransition` bound the
bottom topology and its `DiscreteTopology` proof, then synthesized the topological
ring proof at each use of the continuous-function construction.

## New

Each existing discrete-topology binding in these three definitions is followed by
`letI : IsTopologicalRing (spEllQuotient ℓ E n) := DiscreteTopology.topologicalRing`
(with `n + 1` at the corresponding transition source). This names Mathlib's already
available proof; it supplies no new data. `IsTopologicalRing` is a proposition, so
proof irrelevance makes the returned objects and morphisms definitionally equal to
their original values. The quotient rings, discrete topologies, quotient homomorphisms,
and continuous-function maps are unchanged.

The file also locally prioritizes the existing completeness instances of sheaves
and abelian groups. After the integral transition identity and composition proofs,
`spIntegralTwist` and `spIntegralTwistSystem` are locally irreducible during the
remaining proofs. These instance and reducibility attributes are not exported.
No declaration signature or public import changes.

## Users

A source search over both library roots found these direct users of the affected
point-coefficient constructions (including `spEllPointRingObj`):

| Module | Effect |
| --- | --- |
| Sheaf.Paper.ProEtaleTateTwists (H4) | Explicit proof arguments and local elaboration hints; the returned coefficient objects and maps are preserved. |
| Sheaf.Paper.CartesianCoefficientTwists | Same coefficient objects, reduction maps and morphism types by definitional equality; unchanged. |
| Sheaf.Paper.DiagonalIntegralRootMap | Same coefficient object in the free-module unit; unchanged. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | Same coefficient object in the free-module unit; unchanged. |

No other module is edited or forcibly adapted. Definitional preservation applies
to all transitive consumers, including the targets. The independent definition-change
review should check the preservation demonstrated below; no target statement or
mathematical object is changed or weakened.

## Validation

The following probe compares all three modified declarations directly against
their original construction bodies by `rfl`. It is a temporary compile check, not a new library module or DAG item.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ProEtaleTateTwists
public import WeilConjectures.NumberTheory.Padics.IntegersModPow

/-! Temporary checks of definitional preservation. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale
variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem preserves_spEllPointRing (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllPointRing.{u} ℓ E n =
    (
      letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
      letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
      Profinite.continuousMapRingSheaf (spEllQuotient ℓ E n)
    ) := rfl

theorem preserves_spEllPointReduction (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllPointReduction.{u} ℓ E n =
    (
      letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
      letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
      letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
          (Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk (spTateEllIdeal ℓ E n))
            (spEllQuotient_finite_continuous ℓ E n).2)
    ) := rfl

theorem preserves_spEllPointTransition (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spEllPointTransition.{u} ℓ E n =
    (
      letI : TopologicalSpace (spEllQuotient ℓ E (n + 1)) := ⊥
      letI : DiscreteTopology (spEllQuotient ℓ E (n + 1)) := ⟨rfl⟩
      letI : TopologicalSpace (spEllQuotient ℓ E n) := ⊥
      letI : DiscreteTopology (spEllQuotient ℓ E n) := ⟨rfl⟩
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
          (Profinite.continuousMapRingSheafMap
            (Ideal.Quotient.factor (spTateEllIdeal_succ_le ℓ E n)) continuous_of_discreteTopology)
    ) := rfl

end AlgebraicGeometry.ProEtale
```

## Status

The item compiled cleanly in 34.5 seconds. All three preservation checks compiled
cleanly in 6.5 seconds. The temporary probe source is removed from the packet;
the exact tested code is preserved above for independent replay.
