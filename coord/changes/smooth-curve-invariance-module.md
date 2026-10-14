# AlgebraicGeometry.bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension

## Reason

The old import graph was
`SmoothBaseChange.Derived -> Theorem -> Induction -> Vanishing -> AlgClosedExtension
-> AlgClosedExtensionInjectiveAcyclic`. Proving the last module using smooth base change
would therefore close an import cycle. The curve theorem in AlgClosedExtension already
has an independent proof from connected-curve invariance and finite-component assembly.
It does not use the general qcqs field-extension theorem in the same file.

Move exactly that proved curve declaration into
`Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension`. The original source module publicly
imports it, preserving access to its original name and signature. Vanishing privately
imports the curve module directly. This removes its accidental public dependency on
general qcqs invariance. Both edited existing modules are unclaimed in the local claim
snapshot; these are freely adapted modules under the forced-adaptations instruction of
2026-10-12, not adaptations of another group's held item.

## Old

Location: `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension`.

```lean
theorem bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension {k : Type u}
    [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] {k' : Type u} [Field k']
    [IsAlgClosed k'] [Algebra k k'] (d : ℕ) (hd : (d : k) ≠ 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (C.constantZMod d) q)
```

Vanishing's relevant public import:

```lean
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension
```

## New

Location: `Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension`. Same declaration,
visibility, universes, binders, attributes and proof (the explanatory docstring is updated):

```lean
theorem bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension {k : Type u}
    [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] {k' : Type u} [Field k']
    [IsAlgClosed k'] [Algebra k k'] (d : ℕ) (hd : (d : k) ≠ 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (C.constantZMod d) q)
```

`AlgClosedExtension` reexports the new module using `public import
Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension`. Vanishing uses the proof-only import
`import Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension`.

No definition or mathematical statement changes, including the general qcqs theorem
left in the original module. No target in Challenge.lean changes, and no target-definition
semantic review is reopened. The existing curve node's Lean attachment changes location;
its statement, proof steps and dependencies stay identical. The blueprint unit's
curve input and proof route are retained.

## Users

`tools/downstream.py` reports 107 modules downstream of the original module, but only
the following two actual users of the relocated declaration. Exact-name rg and
`downstream.py Vanishing --uses bijective_cohomologyMap_constantZMod` also find no
code user of the general qcqs theorem downstream of Vanishing. Vanishing no longer reexports
either invariance theorem through this import. The direct importers WeilConjectures and
Induction compile with the delivered modules; no declaration signature changes.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Curve declaration relocated; publicly reexported from its original import path. General theorem and proof unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Public import of general invariance replaced by a private proof import of curve invariance; every declaration and proof unchanged. |

Single-file compilation of both adapted modules and the complete delivered set succeeds.
The maintainer's global build remains the check of the complete library after landing.

## Status

landed 20261014T161711-L-1952065 2026-10-14 (merge of deliver/X2/Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic)
