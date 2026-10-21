# AlgebraicGeometry.Scheme.Modules.determinant_shortExact_exists

## Reason

Retire the duplicate assigned by coord/retire-items.tsv:1647 under the human's
retire-sheaf-twins-20261020.md hand-off. The item currently has zero holes and no
current rework entry. The returned delivery was mathematically approved, but its
landing failed because the fixer named this record without its repository path.
The repaired packet includes the record at its full delivery path,
coord/changes/K4-retire-determinant-short-exact-exists.md. The packet is rebased
onto current sheaf-dag and its complete adopted signature is restored here and
in the item node; the former copies were truncated inside the wedge formula.
The adopted theorem proves the same determinant existence statement using exteriorPower and wedge. Preserve every adopted
source-library declaration unchanged.

Its sole direct consumer, Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact,
privately imports the adopted module. For its canonical isomorphism e0, let eA
be the tensor of the outside exteriorSheafPowerIso comparisons and eB the middle
comparison. The legacy isomorphism is eB ≪≫ e0 ≪≫ eA.symm. Its inverse is
eA.hom ≫ e0.inv ≫ eB.inv. The moved, proved private hom-wedge helper and
tensorHom_app_tmulSection rewrite the first factor; the adopted formula then
rewrites e0.inv, and exteriorSheafPowerIso_inv_wedge rewrites the last factor.
The original uniqueness proof using exteriorSheafTensor_lift_hom_ext remains.
Public signatures, public imports and visibility of the consumer stay verbatim.
No object is chosen from an unproved existence statement and no hole is added.

The original consumer fails against the withdrawn item's empty module at line 69:
`Unknown identifier determinant_shortExact_exists`. The adapted consumer compiles
cleanly. The unclaimed consumer is adapted under the unclaimed-module rule.
The declaration-local transparency option permits the same existing comparison
calculations previously performed inside the retired item. All calculations
apply to rank zero, empty opens, the empty scheme, and zero section rings.

The item node points to the unchanged adopted declaration, with its statement
verbatim and its proof following the canonical wedge morphism, local splitting,
and local bijectivity proof. Its parent node now records comparison transport.
The comparison dependency leaves the item node but remains in the parent node.
The only current stmt_deps/proof_deps/proof-step parent is
lem-sc-determinant-short-exact. The unit's determinant argument is preserved:
the adopted result carries the same local splitting and lift-independent gluing
construction. There is no target statement or definition change.

## Old

```lean
theorem determinant_shortExact_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    ∃ e : exteriorSheaf S.X₂ r₂ ≅ exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₃ r₃ U b)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

## New

Withdraw the duplicate through deleted.txt. Its adopted replacement in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExactExists is:

```lean
theorem determinant_shortExact_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    ∃ e : exteriorPower S.X₂ r₂ ≅ exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

## Users

The downstream scan and direct Lean search found the following consumers.
No claim file for the adapted consumer was present at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | K4 | Retire duplicate; retain node on adopted theorem. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Private import migrated and inverse wedge formula transported; public interface preserved. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged transitive consumer; compiled against adaptation. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged transitive consumer; compiled against adaptation. |
| WeilConjectures.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Adopted replacement; unchanged. |

## Status

landed 20261021T061457-L-1780492 2026-10-21 (merge of deliver/K4/Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists)
