# AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_glue_family

## Reason

Retire the zero-hole duplicate listed in coord/retire-items.tsv row 1345 under
the human's 2026-10-20 hand-off in retire-sheaf-twins-20261020.md. The official
twin already proves the same mathematical statement, using exteriorPower and
wedge in place of exteriorSheaf and exteriorSheafSection.

The sole direct consumer, DeterminantWedgeMorphismLocal, imports the official
twin privately. Its existing comparison helper and exteriorSheafPowerIso
transport the supplied family to the official exterior powers: precompose
each map with the inverse tensor comparison and postcompose with the target
comparison. The inverse wedge equations, tensorHom_app_tmulSection, the given
family formula and the forward wedge equation prove the official family
formula. Apply the official gluing theorem, then precompose its global map
with the forward tensor comparison and postcompose with the inverse target
comparison. The same equations prove the original displayed conclusion.

This is a proof transport, with no definition changes, new hypotheses, public
helpers, choices of arbitrary data, or holes. The family chosen from hlocal is
used in the transport. Both public consumer signatures, their visibility and
public imports remain verbatim. No source-library file or target changes, and
no target statement review is reopened by a changed definition. The comparison
is defined in every degree; rank zero, degree zero, empty opens/schemes and zero
rings require no extra assumptions or separate constructions.

The duplicate is withdrawn through deleted.txt. Its node now attaches to the
existing official theorem with its verbatim statement and actual quotient /
kernel / epiDesc proof dependencies. The consumer node records the comparison
transport. A scan of actual DAG dependencies found no other parent of the glue
node; provenance mentions in blueprint.from are retained. The unit's realized
statement and steps remain unchanged.

## Old

The duplicate declared:

```lean
theorem determinant_wedgeMorphism_glue_family {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (φU : ∀ U : X.Opens, exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶
      exteriorSheaf S.X₂ r₂)
    (hformula : ∀ (U : X.Opens)
      (a : Fin r₁ → S.X₁.val.obj (op U))
      (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
      (∀ i, S.g.val.app (op U) (c i) = b i) →
      (φU U).val.app (op U)
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

Its additional private kernel-comparison helpers are removed with the duplicate.
The consumer privately imported the duplicate and applied this theorem directly.

## New

The unchanged official declaration is:

```lean
theorem determinant_wedgeMorphism_glue_family {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (φU : ∀ U : X.Opens, exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶
      exteriorPower S.X₂ r₂)
    (hformula : ∀ (U : X.Opens)
      (a : Fin r₁ → S.X₁.val.obj (op U))
      (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
      (∀ i, S.g.val.app (op U) (c i) = b i) →
      (φU U).val.app (op U)
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

Its module is WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue.
The consumer keeps its original exteriorSheaf API using the explicit transport
above. The node new-wedge-glue-family points at this official implementation.

## Users

The downstream.py --uses scan lists six downstream modules. Only the local-data
consumer imports the duplicate or calls its declaration. A source scan of lean/
and quarantine/ found no other imports or uses requiring adaptation. Current
claim records have no holder for these consumers. Every listed module is checked
by an individual server compile against the adapted consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged; API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged; API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged; API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged; API preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Replace one private import; transport family and global map in the gluing proof. Public signatures unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged; API preserved. |

Repair validation (2026-10-21, return C-68115, returned head 681151c2c):
reconciled the retained packet against the current source. The same sole
consumer still needs migration, and the retirement request still applies.
The adapted consumer compiled cleanly on the server in 4.8 seconds. The
fresh delivery is based on current sheaf-dag; no unrelated missing source
file is part of this change.

## Status

landed 20261021T014711-L-2446156 2026-10-21 (merge of deliver/J4/Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue)
