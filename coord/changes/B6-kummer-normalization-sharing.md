# Kummer normalization definitions

## Reason

The proof compiles, but the concrete specialization originally took 68 seconds.
Profiler output isolated 25 seconds in the target alias and another 25 seconds
checking the final specialization. Both signatures independently expanded the same
normalization expressions. Share the existing normalization constants by defining
them in the new compatibility module and publicly reexporting them from the item.
Their names, binders, universes, attributes, and bodies are unchanged. No target
statement or definition meaning changes.

## Old

In `Sheaf.Paper.KummerStrictTargetTransport`:

```lean
/-- The positive Kummer unit after the comparison isomorphism on units.
This is the actual Ext composite, named to share its coefficient constructions
rather than checking the concrete sheaf abelian structures at each occurrence.
Source: the units-comparison composite in the diagonal tower proof, step (4)
(blueprint: lem-sfb-kummer-strict-target-transport). -/
@[irreducible] def kummerComparedUnit (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (n : ℕ) :
    Ext.{u + 1} ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
      ((cartierForget (diagonalResidue.{u} ℓ n) W).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) W)) 1 :=
  (Ext.mk₀ (cartierUnitsComparison W)).comp
    (cartierProKummerUnit (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
      (by simpa using hW.pow (n + 1))) (zero_add 1)

/-- The actual roots comparison equation, named before derived specialization.
Source: diagonal tower system proof, step (3), target normalization
(blueprint: lem-sfb-kummer-strict-target-transport).
This is precisely the canonical underlying-map equation, with no chosen data. -/
def kummerRootNormalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (H : DiagonalSystems ℓ W)
    (roots : H ⋙ diagonalForget ℓ W ≅
      Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (n : ℕ) (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)) : Prop :=
  HEq ((diagonalForget ℓ W).map t.hom)
    (roots.hom.app (op n) ≫ cartierProRootMap (diagonalResidue.{u} ℓ n)
      (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W
      (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1)))

```

## New

In `Sheaf.Paper.KummerStrictAdjunctCompatibility`:

```lean
/-- The positive Kummer unit after the comparison isomorphism on units.
This is the actual Ext composite, named to share its coefficient constructions
rather than checking the concrete sheaf abelian structures at each occurrence.
Source: the units-comparison composite in the diagonal tower proof, step (4)
(blueprint: lem-sfb-kummer-strict-target-transport). -/
@[irreducible] def kummerComparedUnit (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (n : ℕ) :
    Ext.{u + 1} ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
      ((cartierForget (diagonalResidue.{u} ℓ n) W).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) W)) 1 :=
  (Ext.mk₀ (cartierUnitsComparison W)).comp
    (cartierProKummerUnit (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
      (by simpa using hW.pow (n + 1))) (zero_add 1)

/-- The actual roots comparison equation, named before derived specialization.
Source: diagonal tower system proof, step (3), target normalization
(blueprint: lem-sfb-kummer-strict-target-transport).
This is precisely the canonical underlying-map equation, with no chosen data. -/
def kummerRootNormalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (H : DiagonalSystems ℓ W)
    (roots : H ⋙ diagonalForget ℓ W ≅
      Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (n : ℕ) (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)) : Prop :=
  HEq ((diagonalForget ℓ W).map t.hom)
    (roots.hom.app (op n) ≫ cartierProRootMap (diagonalResidue.{u} ℓ n)
      (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W
      (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1)))

```

The item publicly imports `Sheaf.Paper.KummerStrictAdjunctCompatibility`.
The item's existing public `CanonicalSheafExt` import is preserved. Its five other
definitions/structures and its theorem signature are unchanged. The new
compatibility proposition uses the shared constants instead of expanding their
bodies; the final proof unfolds only the new proposition alias.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalCartierAdjunctUniqueness | unclaimed | Same names and definitions reexported; compile unchanged. |
| Sheaf.Paper.KummerSheafPredicates | unclaimed | Same names and definitions reexported; compile unchanged. |
| Sheaf.Paper.DiagonalFiniteCartierNormalization | unclaimed | Same names and definitions reexported; compile unchanged. |
| Sheaf.Paper.KummerTransportAssembly | unclaimed | Same names and definitions reexported; compile unchanged. |

All four direct importers compiled unchanged against this packet using
`lcompile.py --all`; their verification-only copies were removed. No forced
adaptations or changes to their existing signatures were needed.

## Status

landed 20261027T112320-L-1570535 2026-10-27 (merge of deliver/B6/Sheaf.Paper.KummerStrictTargetTransport)
