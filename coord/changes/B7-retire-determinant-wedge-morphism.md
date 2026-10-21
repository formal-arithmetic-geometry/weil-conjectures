# AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_exists

## Reason

Complete the duplicate retirement assigned by coord/retire-items.tsv:1560.
The Sheaf item already has zero holes. The adopted theorem is proved and
implements the same wedge morphism with exteriorPower and wedge in place of
exteriorSheaf and exteriorSheafSection. No source-library file is modified.

Migrate the sole direct consumer, DeterminantShortExactExists, to a private
import of the adopted theorem. It obtains the canonical morphism psi directly,
then constructs phi = eA.hom ≫ psi ≫ eB.inv using the existing canonical exterior
sheaf comparisons. Move the proved private hom-wedge helper from the retired
item to the consumer. Tensor-section naturality, the hom-wedge identities,
the official formula for psi and the inverse-wedge identity prove the exact
legacy formula for phi. The existing splitting-cover proof establishes IsIso
psi and hence IsIso phi; its final inverse isomorphism has the unchanged formula.
The consumer's public signature, public imports, visibility and docstring are
verbatim. This removes a redundant conversion from legacy to canonical powers.

The original consumer compiled against the empty retired module fails at its
old line 68 with `Unknown identifier determinant_wedgeMorphism_exists`.
The adapted consumer compiles cleanly in 4.4 seconds. The unchanged next consumer,
DeterminantShortExact, compiles against the adaptation in 3.3 seconds. The new
private import is permitted by import_direction.py. The other private imports
are used for local splitting, split-local bijectivity, comparison transport,
and Hom.isIso_of_forall_bijective_app respectively.

Retain the mathematical node and redirect its Lean attachment to the adopted
theorem, with its official statement verbatim and its actual local-construction
and gluing dependencies. Remove the comparison dependency from this node, where
it no longer occurs, and retain it in the updated sole parent's proof. Scanning
stmt_deps, proof_deps and proof-step uses across all DAG nodes found precisely
lem-sc-determinant-short-exact-exists as its parent. The retirement row and the
current source agree; there is no rework or return entry for this item.
The fixed unit's determinant construction, local splitting and gluing route
stay intact. The formulas and comparison isomorphisms apply to all ranks and
opens, including rank zero, the empty open and scheme, and zero section rings;
there is no cancellation by a nonzero coefficient or extra rank assumption.
No target statement or definition it uses changes meaning.

## Old

```lean
theorem determinant_wedgeMorphism_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] :
    ∃ φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

## New

The duplicate declaration is withdrawn through deleted.txt. Its proved adopted
replacement is:

```lean
theorem determinant_wedgeMorphism_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] :
    ∃ φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (wedge (M
```

The legacy consumer's public declaration is preserved by the transport above.

## Users

Holders below are those of the inspected shared claim snapshot. All downstream
modules reported by tools/downstream.py --uses are listed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | B7 | Retired duplicate; node retained on the proved adopted theorem. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Private import migrated; proved private helper moved here; proof transports the adopted morphism to its unchanged public formula. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged; compiles against the adapted consumer. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged; its dependency's public signature, imports and definitions are preserved. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged; its dependency's public signature, imports and definitions are preserved. |

## Status

landed 20261021T023301-L-2944426 2026-10-21 (merge of deliver/B7/Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism)
