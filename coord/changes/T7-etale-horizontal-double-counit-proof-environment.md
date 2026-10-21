# Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit proof elaboration

## Reason

The completed proofs need the abstract inverse-image and derived-adjunction
interfaces kept folded while simplifying the mate identities. Local irreducibility
attributes provide that control. The main counit proof also needs a larger
recursion depth for nested composite adjunctions and relaxed transparency during
definitional equality checks. The refinement proof needs the same transparency
setting to identify the chosen compact-support functor with the candidate of its
chosen compactification.

The compositor theorem retains its original assumptions. Its completed proof does
not use four automatically included section assumptions, so its unused-section
variable warning is disabled for that theorem instead of changing its signature.

These commands are local to this module or to individual declarations and do not
change the attributes seen by importers. Every existing public signature, both
non-theorem bodies, and all four public imports are verbatim unchanged. No target
statement or definition meaning changes. The whole file compiled without warnings
in 12.5 seconds. This record documents the command changes flagged by preflight.

## Old

The existing elaboration setting was:

```lean
set_option autoImplicit false
```

There were no local irreducibility attributes and no theorem-scoped recursion,
transparency, or linter settings. All five theorem proofs were `by sorry`.

## New

Retained `set_option autoImplicit false` and added, inside the existing namespace:

```lean
attribute [local irreducible] upperStar etaleLowerShriek
  Functor.mapDerivedCategory derivedEtaleLowerShriekUpperStarAdjunction
```

The main counit theorem is preceded by:

```lean
set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
```

The refinement theorem is preceded by:

```lean
set_option backward.isDefEq.respectTransparency false in
```

The compositor theorem is preceded by:

```lean
set_option linter.unusedSectionVars false in
```

Added seven completely proved private helpers: `conjugate_transport`,
`mate_change_right_adjoints`, `mate_top`, `mate_bottom`, `mate_cube`, `pullComp`,
and `support_paste_inv`: six lemmas and one constructed isomorphism. All five existing theorem bodies are complete. No
existing definition body, signature, visibility, or public import is changed.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit
--uses etaleHorizontalDoubleCounit` reports zero downstream modules and only the
item itself as a textual user. A source search confirms that the declarations
currently occur only in the item. This is consistent with its parent's proof still
being unfinished and citing its DAG node; the item and its attachment are retained.
No module is withdrawn and no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit | T7 | Five proofs completed; local proof elaboration settings added; public interface preserved. |

## Status

landed 20261021T130159-L-2598879 2026-10-21 (merge of deliver/T7/Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit)
