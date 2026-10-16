# Reuse the public regular-module isomorphism

## Reason

Repair reviewer X-6ac00's H4 return for head `6ac00d95e`: the private
`AlgebraicGeometry.ProEtale.regularRingIso` duplicated an existing proof.
Delete that entire declaration and reuse the already-public, more general
`CategoryTheory.Mod.regularIsoOfIsIso` from
`WeilConjectures/Mathlib/CategoryTheory/Monoidal/Mod.lean:461`.

## Old

The returned matrix module introduced a private `regularRingIso` definition
with the same proof as the existing library comparison, and called it as
`fp_map _ _ K (regularRingIso eR) hN`.

## New

Remove that entire private declaration and use
`fp_map _ _ K (Mod.regularIsoOfIsIso eR.hom) hN`.
The substitution changes no other declaration or proof body. The current second
reading additionally removes two redundant proof-only imports.
The existing helper has type

```lean
noncomputable def regularIsoOfIsIso {M B : C} [MonObj M] [MonObj B]
    (φ : M ⟶ B) [IsIso φ] [IsMonHom φ] :
    (Mod.comap (inv φ)).obj (Mod.regular M) ≅ Mod.regular B
```

For `φ := eR.hom`, its type is definitionally the required type because
`inv eR.hom = eR.inv`. It needs neither the abelian nor closed assumptions
of Compatibility's private helper. No additional import is needed: the public
module is already in Compatibility's public import closure.

## Difference from the prescribed H4 route

H4 requested publication of F3's private `Mod.regularRingIso` and then its reuse.
That helper remains private in the shared source and F3's retained sandbox.
The alternative above uses an existing public API with the same result, so no
publication or visibility change in F3's module is necessary. This is a deliberate
change from H4's requested helper name, recorded for the independent reader.
The duplicate is removed and no replacement helper is introduced.

## Users

| Module | Holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedFinitePresentationMatrices | A4 | Use the public original regular-module comparison. |
| Sheaf.Paper.CondensedLfpCoefficientModel | A4 | Same statement and proof; dependency no longer duplicates the comparison. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | F3 | No source or visibility changes. |

No existing signature, downstream definition, public import, or hole count changes.
The matrix node's proof text records the public API reuse.

## Status

landed 20261016T073458-L-1079815 2026-10-16 (merge of deliver/A4/Sheaf.Paper.CondensedLfpCoefficientModel)

All four retained modules compile against the shared baseline with `lcompile.py --all`.
There is no Compatibility source or compiled override in the sandbox.
The required command is
`python3 /home/ubuntu/weil-launcher/deliver3.py A4 Sheaf.Paper.CondensedLfpCoefficientModel --no-push`.
Its final output is saved in `scratchpad/h4-public-regular-iso-dry-run.log`.
The independent reader must review the public-helper substitution explicitly.
