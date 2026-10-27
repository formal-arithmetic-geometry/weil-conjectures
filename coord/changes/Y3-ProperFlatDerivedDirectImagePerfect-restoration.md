# AlgebraicGeometry.properFlat_derivedDirectImage_perfect

## Reason

Restore the module quarantined in coord/rework.tsv on 2026-10-20. Its recorded
compiler error at line 57 is an unsolved universe constraint `?u + 1 = u` while
elaborating the restriction functor in private `perfect_of_iso`. The sheaf-of-modules
universe of `overFunctor` was implicit. Both restriction transports must use the
same universe u as the module categories in their signatures.

The source is quarantine/Sheaf/AlgebraicGeometry/ProperFlatDerivedDirectImagePerfect.lean.
It is restored to lean/Sheaf/AlgebraicGeometry/ProperFlatDerivedDirectImagePerfect.lean.
The archive is preserved. This is a zero-hole proof-elaboration repair, not a withdrawal.

## Old

In private `perfect_of_iso`:

```lean
  exact ⟨U, hx, K, hK, ⟨(SheafOfModules.overFunctor
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm ≪≫ c⟩⟩
```

In private `perfect_Q_transport`:

```lean
  let F := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U
```

All archived declaration signatures and imports are the reference, unchanged.

## New

In private `perfect_of_iso`:

```lean
  exact ⟨U, hx, K, hK, ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm ≪≫ c⟩⟩
```

In private `perfect_Q_transport`:

```lean
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
```

These are the only two edits to the archived Lean file. No definition, signature,
attribute, public import, target meaning or proof route changes. All five private
helpers and the public theorem remain fully proved. The node's Lean attachment,
proof and proof dependencies remain accurate and are preserved.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect
--allow-missing --uses properFlat_derivedDirectImage_perfect` reports zero live
importers. Searches of quarantine/ also identify these archived consumers. No claim
file names any of them in this snapshot. They are retained without adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | quarantined; no claim found | Applies unchanged public theorem with the same arguments. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | quarantined; no claim found | Applies unchanged public theorem with the same arguments. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | quarantined; no claim found | Imports all and uses unchanged private isFinitePresentation_of_isZero helper. |

The DAG parents lem-sc-proper-flat-right-adjoint-direct-sums and
lem-sc-proper-flat-right-adjoint-open-support still need this node. The unit route
in sk-thm-picard-duality is unchanged. No consumer or parent dependency is removed.
No forced adaptations are required because all signatures and imports are unchanged.

Validation: lcompile.py compiled the restored module without errors or warnings in
47.6 seconds. Text comparison confirms the public theorem, including its entire
proof, is unchanged from the archive. All Lean lines have at most 100 characters;
there are zero sorry tokens. The three required searches were run through msearch:
Lean Finder found exact-functor/flatness declarations but no shorter direct-image
result; Loogle did not recognize IsPerfect; Mathlib grep found no matching theorem.
Stacks Tag 0B91(1) explicitly gives the retained route through 0A1H with O_X[0].

## Status

landed 20261025T124449-L-2026910 2026-10-25 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect)
