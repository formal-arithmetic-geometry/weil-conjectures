# AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange

## Reason

Restore the quarantined item and repair its deterministic timeout against the current
trace-counit dependency. The original file has zero textual holes. An initial compile
of that file, with profiling enabled, stopped after 120 seconds. The repaired proof
compiles in 7.1 seconds.

Reuse the existing proof instances cached in DerivedCategoryModule, retain let bindings,
and protect the derived-category category structure locally from unfolding. These are
proof and elaboration changes only. The local instance attributes concern propositions
(HasSheafify and IsGrothendieckAbelian); they install no new category data and export no
instance. Transparency remains respected. The helper applies the componentwise
isomorphism criterion instead of rewriting its IsIso occurrence, and its simplification
uses only the listed category identities without implicit definitional proof synthesis.

## Old

The original module has only this elaboration option:

```lean
set_option autoImplicit false
```

Its first local irreducibility command is:

```lean
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
```

The private helper uses:

```lean
  rw [exceptionalBaseChange_eq_mate, NatTrans.isIso_iff_isIso_app]
```

and ends its cancellation argument with:

```lean
      simpa only [Category.assoc, NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc] using hc K)
```

## New

```lean
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
```

```lean
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
```

```lean
  rw [exceptionalBaseChange_eq_mate]
  apply (NatTrans.isIso_iff_isIso_app _).2
```

```lean
      simpa -implicitDefEqProofs only
        [Category.assoc, NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc] using hc K)
```

All theorem signatures, definition bodies, imports, docstrings, and the main theorem's
proof body are preserved verbatim from the quarantined source. No target or definition
used by a target changes meaning. Profiling options are absent from the delivery.

## Users

The item is absent from the live tree, so tools/downstream.py reports an unknown module.
A direct import search of both lean/ roots and both quarantine/ roots finds exactly the
following consumer. Its original source is compiled against the repair using a temporary
sandbox copy, which is removed before delivery. It is unclaimed at the time of inspection.
The joint check compiled the item in 34.4 seconds and the consumer in 35.0 seconds,
both cleanly and within 60 seconds. No consumer edit is needed, and the quarantine
archive is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange | unclaimed | Same exceptional base-change theorem and imports; unchanged consumer checked against the repaired item. |

The node lem-asd-projective-line-exceptional-base-change keeps its existing Lean attachment,
statement, and dependencies. The finite splitting, diagonal adjunction, counit equation,
and mate argument still implement the same unit route.

## Status

landed 20261026T104350-L-795127 2026-10-26 (merge of deliver/C2/Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange)
