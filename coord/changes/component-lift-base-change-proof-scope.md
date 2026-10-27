# Sheaf.Paper.ComponentLiftBaseChange

## Reason

The proof introduces private proved helpers and scopes their elaboration option to a
section. The static interface checker flags the added section/options commands.
This record documents their scope. Every existing public signature and definition
body is unchanged. The option controls elaboration of proof terms only and is restored
at section end; the public theorem has the same option scoped to its declaration.

## Old

After `affineComponentMap`, the original file proceeds directly to the existing
docstring and `component_lift_base_change`, with the theorem proof `:= by sorry`.
The only explicit file option is:

```lean
set_option autoImplicit false
```

## New

The existing `autoImplicit` command is unchanged. Immediately after `affineComponentMap`:

```lean
section

set_option backward.isDefEq.respectTransparency false
```

The section contains only private helpers with complete proofs (and explicit data
constructions whose chosen maps are uniquely characterized). After those helpers:

```lean
end

set_option backward.isDefEq.respectTransparency false in
```

The final scoped command applies to the existing public theorem, whose signature is
unchanged and whose proof is complete. No instance, attribute, notation, public import
or existing definition body is changed. The added proof import is private:
`import Sheaf.Paper.RelativeComponentLiftPullbackSpace`.

## Users

`python3 tools/downstream.py Sheaf.Paper.ComponentLiftBaseChange --uses
AlgebraicGeometry.ProEtale.component_lift_base_change` reports zero downstream modules;
the only textual use is the declaration in the item itself. The DAG parent retains the
same statement and dependency. No target definition is changed or requires renewed
statement review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ComponentLiftBaseChange | C1 | Private proof scope and complete theorem proof. |

## Status

landed 20261023T123358-L-1178355 2026-10-23 (merge of deliver/C1/Sheaf.Paper.ComponentLiftBaseChange)
