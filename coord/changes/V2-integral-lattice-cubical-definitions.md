# IntegralLatticeCubical definitions: acyclic import interface

## Reason

The assigned contraction theorem must use the two existing DAG proof dependencies
CubicalBoundaryCoordinateProjections and CubicalSignedCoordinateHomotopy. Both currently
import IntegralLatticeCubicalContraction for its definitions, so importing either from the
assigned module creates an import cycle. Extract the ten existing definitions unchanged to
IntegralLatticeCubicalDefs and publicly reexport them from the original module. Adapt only
the two dependency imports. No mathematical definition or theorem signature changes; the
source-library root is untouched. No target meaning changes.

## Old

The following declarations lived in IntegralLatticeCubicalContraction:

```lean
/-- Coordinate subsets in degree `a`; empty outside the range from zero to `r`.
Source: the displayed basis in the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
def Directions (r : ℕ) (a : ℤ) := {I : Finset (Fin r) // (I.card : ℤ) = a}

/-- The free abelian group on the cubical cells in degree `a`.
Source: the basis clause of the DAG statement; freeness is Mathlib's `Module.Free`.
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
abbrev Chains (r : ℕ) (a : ℤ) := ((Fin r → ℤ) × Directions r a) →₀ ℤ

/-- The symbol `[v,I]`, with value zero when `I` has the wrong cardinality.
Source: the zero-extension convention in the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def cell (r : ℕ) (a : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)) : Chains r a :=
  if h : (I.card : ℤ) = a then Finsupp.single (v, ⟨I, h⟩) 1 else 0

/-- The standard basis vector `u_i` of the lattice.
Source: the first sentence of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
def unitVector (r : ℕ) (i : Fin r) : Fin r → ℤ := Pi.single i 1

/-- The integral alternating cubical differential, extended linearly from the given basis.
Source: DAG displayed differential, compared with Stacks Tag 0623's alternating differential
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def boundary (r : ℕ) (a : ℤ) : Chains r a →ₗ[ℤ] Chains r (a - 1) :=
  Finsupp.linearCombination ℤ fun c ↦
    ∑ i ∈ c.2.val, (-1 : ℤ) ^ (c.2.val.filter (fun j ↦ j < i)).card •
      (cell r (a - 1) (c.1 + unitVector r i) (c.2.val.erase i) -
        cell r (a - 1) c.1 (c.2.val.erase i))

/-- The same boundary from degree `a + 1` into degree `a`, with canonical degree transport.
Source: the indices in the DAG contraction and exactness clauses
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def incomingBoundary (r : ℕ) (a : ℤ) :
    Chains r (a + 1) →ₗ[ℤ] Chains r a :=
  (LinearEquiv.cast (R := ℤ) (M := Chains r) (add_sub_cancel_right a 1)).toLinearMap.comp
    (boundary r (a + 1))

/-- The augmentation taking each vertex to one.
Source: DAG augmentation clause
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def augmentation (r : ℕ) : Chains r 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun _ ↦ 1

/-- The section taking one to the vertex at the origin, with actual specified data.
Source: DAG section clause
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def sectionMap (r : ℕ) : ℤ →ₗ[ℤ] Chains r 0 :=
  LinearMap.toSpanSingleton ℤ (Chains r 0) (cell r 0 0 ∅)

/-- The endomorphism `e`, equal to section times augmentation in degree zero and zero
elsewhere: the cell constructor makes the displayed empty direction zero in other degrees.
Source: DAG definition of `e`
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def originProjection (r : ℕ) (a : ℤ) : Chains r a →ₗ[ℤ] Chains r a :=
  Finsupp.linearCombination ℤ fun _ ↦ cell r a 0 ∅

/-- Translation by a lattice vector on cubical chains, leaving directions unchanged.
Source: DAG translation formula
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def translate (r : ℕ) (a : ℤ) (w : Fin r → ℤ) :
    Chains r a →ₗ[ℤ] Chains r a :=
  Finsupp.linearCombination ℤ fun c ↦ cell r a (c.1 + w) c.2.val

```

Both coordinate modules contained:

```lean
public import Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction
```

## New

The declarations above, with verbatim signatures and bodies, live in
Sheaf.AlgebraicTopology.IntegralLatticeCubicalDefs. The original module reexports them:

```lean
public import Sheaf.AlgebraicTopology.IntegralLatticeCubicalDefs
```

Both coordinate modules use that same public import. The original module privately imports
the two coordinate lemmas, proves the total contraction by list induction, and deduces
exactness. All other consumers keep their original imports.

## Users

`tools/downstream.py Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction --uses
IntegralLatticeCubical.Chains` reports the following full downstream closure (including
the changed module itself). All listed public declarations keep their names and types.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction | V2 | Definitions moved unchanged to publicly reexported IntegralLatticeCubicalDefs; theorem proved. |
| Sheaf.AlgebraicTopology.CubicalBoundaryCoordinateProjections | unclaimed (G5 proof landed) | Public import changed to definitions module; no declaration changes. |
| Sheaf.AlgebraicTopology.CubicalPartitionBoundaryExpansion | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.AlgebraicTopology.CubicalPartitionGradedEquivariance | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.AlgebraicTopology.CubicalSignedCoordinateHomotopy | unclaimed (G6 proof landed) | Public import changed to definitions module; no declaration changes. |
| Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeCharacterKoszulBoundary | H6 | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeCubicalAugmentationEvaluation | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeCubicalMultiplicationRoof | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeCubicalSheafResolution | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeInjectiveKoszulAcyclicity | S6 | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeKoszulInjectiveNormalization | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeKoszulTotalTriangles | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison | unclaimed | No source change; same public declarations and definition bodies remain visible. |
| Sheaf.CategoryTheory.LatticeOrderedKoszulProducts | H7 | No source change; same public declarations and definition bodies remain visible. |

The G5 and G6 proofs landed during this session; both modules are now unclaimed.
Their complete newly landed sources were refreshed, preserving every declaration,
proof and proof import. Their original imports close an import cycle against the item proof;
`tools/import_direction.py may` explicitly rejects each proposed parent-to-coordinate
import. The only changed source line in each module replaces the parent import by the
shared definitions import. All signatures, visibility and theorem proofs are verbatim.
This is an import-cycle repair; compiling against a stale pre-repair parent artifact
would not test the source graph. The adapted modules compile in the delivered acyclic set.

## Status

landed 20261025T071213-L-140746 2026-10-25 (merge of deliver/V2/Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction)
