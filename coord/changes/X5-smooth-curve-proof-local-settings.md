# Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages proof-local settings

## Reason

The delivery checker conservatively classifies added module commands, including local
reducibility attributes, as an interface change. This record documents those commands.
No existing definition, declaration signature, visibility, target, category instance or
exported reducibility setting changes. The attributes prevent expensive unfolding while
elaborating the private geometric and sheafification proofs; they expire with this module.
The theorem's proof uses these settings and compiles cleanly in 58.1 seconds.

## Old

The original module had these surrounding commands, verbatim:

```lean
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
```

It had no local reducibility attributes or explicit autoImplicit setting. Its three
existing definitions, existing abbreviation and theorem signature are preserved verbatim.

## New

The surrounding commands above remain. The following commands are added verbatim:

```lean
set_option autoImplicit false
```

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  derivedPullback
```

The geometric private theorem alone is elaborated under:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

The final private sheafification lemma and theorem are elaborated after:

```lean
attribute [local irreducible] abelianHigherDirectImageClass canonicalComparison
  Scheme.Modules.higherDirectImage
```

These are proof-local settings, not repairs to the definitions named in the attributes.
The source constants keep their original bodies and exported attributes. There are no
new public data definitions. The sole new public declaration is the raw comparison
statement, documented separately by its new node.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages
--uses smooth_curve_etale_structure_direct_images` finds only the defining module itself.
No downstream file mentions that theorem yet. The import-closure query finds the seven
modules below; all consume exactly the same existing public interface and none is edited.
Their statements therefore retain exactly their previous meanings. Since no definition
changes, no target's statement review is reopened by the proof-local commands.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | X5 | Private proofs and lexical settings; existing public signatures and definitions unchanged. |

Untouched import-closure consumers (ownership need not be queried for an adaptation,
because none is adapted):

- `Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne`
- `Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible`
- `Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility`
- `Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness`
- `Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility`
- `Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule`
- `Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients`

The three definitions, abbreviation and theorem signature were compared directly with
the shared repository and are byte-identical. Public imports are also preserved.

## Status

landed 20261018T071242-L-1683261 2026-10-18 (merge of deliver/X5/Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages)
