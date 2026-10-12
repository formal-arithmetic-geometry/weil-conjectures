# AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage

## Reason

The affine sections proof uses higher-image quasi-coherence. Move its existing declaration
before the affine sections theorem so that Lean can refer to it. The move includes its unchanged
`section QuasiCoherence` and `variable` commands. `open TopologicalSpace` resolves the open-cover
names used by the already completed compact-base vanishing proof. These command changes trigger
the preflight's interface-change bookkeeping check, although every elaborated existing signature
and visibility is preserved. No definition, target statement, or intermediate statement changes.

## Old

The following signature occurred later in the module, in `section QuasiCoherence`:

```lean
variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

theorem isQuasicoherent_higherDirectImage (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent :=
  sorry
```

The namespace-opening command was `open CategoryTheory Limits`.

## New

The identical section and declaration are placed before
`exists_addEquiv_sections_higherDirectImage_H`:

```lean
variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

theorem isQuasicoherent_higherDirectImage (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent :=
  sorry
```

The namespace-opening command is `open CategoryTheory Limits TopologicalSpace`.
Public imports are unchanged; the new comparison import is proof-only.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections | G2 | Its affine sections proof can refer to the earlier declaration; all signatures are unchanged. |
| All importers of Sections | unchanged | Declaration order and local namespace openings do not alter any exported theorem type or definition. No adaptation is required. |

## Status

landed 20261012T202239-L-704236 2026-10-12 (merge of deliver/G2/WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections)
