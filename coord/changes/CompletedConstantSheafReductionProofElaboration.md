# Sheaf.Paper.CompletedConstantSheafReduction

## Reason

Stage-3 preflight (d) requires a change record because the proof edits add elaboration
options and a local reducibility attribute. These commands support elaboration of the
explicit tensor/sheafification comparisons and avoid unfolding the constructed unit
isomorphism during the projective-retract proof. They change no existing declaration's
signature, visibility or defining data. The reducibility attribute applies to a new
private proof helper and is local to the current section. The options apply to this
module's elaboration; importers do not acquire them. No target meaning changes.

## Old

The module's option header was:

```lean
set_option autoImplicit false
```

There was no `constantChange_unit` private helper or reducibility command for it.

## New

The option header is:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The new private unit isomorphism is followed by:

```lean
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] constantChange_unit
```

Individual new proof declarations also use the same local backward-elaboration option.
All existing public declarations retain their original statements and visibility.
The new public algebra theorem is in its own new module and has its own new DAG node.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedConstantSheafReduction | T4 | Proof elaboration only; no public interface or data change. |

No external consumer can reference the private helper or inherit its local attribute.
The downstream scan for `constantChange_unit` concerns a newly added private name;
there are no existing external users to adapt. Existing importers continue to see
exactly the same public declarations. No module held by another group is edited.

## Status

landed 20261019T192838-L-1875455 2026-10-19 (merge of deliver/T4/Sheaf.Paper.CompletedConstantSheafReduction)
