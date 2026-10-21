# AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_local_data and determinant_wedgeMorphism_of_local_data

## Reason

Retire the duplicate Sheaf module listed in coord/retire-items.tsv, row 1465,
under the human's retirement hand-off of 2026-10-20. The item has zero holes;
this is a retirement and compatibility repair, not a new proof-hole closure.
The official twin is proved and uses exteriorPower and wedge. Its local-data
and gluing statements implement the same construction in that representation.

The sole direct consumer, Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism,
privately imports the official twin and ExteriorSheafPowerComparison. Its proof
applies the official local-data theorem and gluing theorem in the same order,
then precomposes the resulting global map with the tensor of the two comparison
hom maps and postcomposes with the target comparison inverse. The moved, proved
private helper derives the hom wedge formula from the inverse wedge formula.
Tensor-section naturality and the comparison formulas prove the unchanged public
exteriorSheaf statement. The unused private Mathlib exterior-power basis import
is removed. The consumer's public signature, public imports, definitions and
docstring are unchanged. No upstream source file or target statement changes.

The item is withdrawn through deleted.txt. Both attached nodes now point to the
official twin, with verbatim official Lean statements and the actual official
proof dependencies. The parent construction node records the official local-data
and gluing calls followed by comparison transport. The unit statement and route
stay unchanged. An actual dependency-field scan (stmt_deps, proof_deps and step
uses, excluding provenance) found no other parent of the two local nodes; the
updated parent points to their retained official attachments. The official
constructions and comparisons work in degree zero, on empty opens and schemes,
and over zero section rings; no extra hypotheses or arbitrary choices of data
are introduced.

## Old

```lean
theorem determinant_wedgeMorphism_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] :
    ∀ (U : X.Opens), ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))

theorem determinant_wedgeMorphism_of_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (hlocal : ∀ (U : X.Opens), ∃ φU : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
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

The duplicate declarations are withdrawn. Their proved official replacements are:

```lean
theorem determinant_wedgeMorphism_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] :
    ∀ (U : X.Opens), ∃ φU : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶
      exteriorPower S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))

theorem determinant_wedgeMorphism_of_local_data {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (hlocal : ∀ (U : X.Opens), ∃ φU : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶
      exteriorPower S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

The consumer retains its original exteriorSheaf statement through the comparison
transport above. Its axiom check and downstream compile results are in report.md.

## Users

The downstream.py --uses scan lists the five modules below. A source import scan
of lean/ and quarantine/ finds only DeterminantWedgeMorphism as a direct consumer.
No claim file for that consumer is present in the shared claim records; it is
unclaimed. The other four modules keep their source and statements verbatim.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Replace private import, move proved private helper, transport official global map; public API unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged; consumes preserved API. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged; consumes preserved API. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged; consumes preserved API. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged; consumes preserved API. |

The original direct consumer compiled against an empty withdrawn stub fails at
line 64 with `Unknown identifier determinant_wedgeMorphism_of_local_data` and
then at line 65 with `No goals to be solved`. The adapted consumer compiles.
Only its import and the necessary representation transport change, together
with removal of the unused private proof import.

## Status

landed 20261021T021023-L-2692789 2026-10-21 (merge of deliver/N4/Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal)
