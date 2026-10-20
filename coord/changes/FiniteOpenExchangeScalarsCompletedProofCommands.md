# AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars

## Reason

Complete the two remaining proofs without changing public statements or data.
The new proof sections scope transparency options and local irreducibility to
avoid expanding the chosen inverse-image construction during mate calculations.
The tower sections also keep Scheme.proEtaleRingModulePullback folded. The new
helpers are private and fully proved. The two tactic-replay linters are disabled
inside this file to avoid replaying the large categorical proof terms; ordinary
elaboration, kernel checking, and delivery axiom checks remain enabled.

The existing private sequence_iso helper is also refactored to accept explicit
forward/inverse component maps and inverse equations instead of dependent
isomorphism records. Its proof and its two tower uses are adapted together; this
avoids repeated mapIso projection reductions during kernel checking.

These are proof-elaboration commands and private proof changes only. No existing exported definition,
instance, signature, public import, target meaning, or consumer changes.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
```

The private sequence helper previously took:

```lean
(e : ∀ n, X n ≅ Y n)
(h : ∀ n, s n ≫ (e n).hom = (e (n + 1)).hom ≫ t n)
```

The existing tower sections locally mark their scalar comparison definitions
irreducible, but do not mark Scheme.proEtaleRingModulePullback irreducible.

## New

```lean
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
```

The new private proof sections use:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Scheme.proEtaleRingModulePullback
```

The private sequence helper now takes:

```lean
(f : ∀ n, X n ⟶ Y n) (g : ∀ n, Y n ⟶ X n)
(fg : ∀ n, f n ≫ g n = 𝟙 _) (gf : ∀ n, g n ≫ f n = 𝟙 _)
(h : ∀ n, s n ≫ f n = f (n + 1) ≫ t n)
```

The resulting tower isomorphism has exactly these forward and inverse
components. The two existing tower proofs provide the original exchange maps,
with the inverse equations proved by functoriality.

The irreducibility attribute is also added to the two existing tower-proof
sections. All these commands are file-local or section-local. The private
pushRes_apply theorem is moved earlier, unchanged, for the new compositor proof.
Two proof-only `import all` lines expose the already proved coordinate and
mate-pasting helpers; the seven unused direct proof imports are removed.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars --names`
and the corresponding `--direct --names` scan both returned no modules in the
current source import graph. No consumer adaptation is required: every existing
public signature and data body is unchanged, and the new commands do not propagate
through imports. DAG parents continue to use the same statements and definitions.
No statement or definition repair is requested.

| module | group holding it | effect |
| --- | --- | --- |

## Status

landed 20261020T235530-L-1186177 2026-10-20 (merge of deliver/A3/Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars)
