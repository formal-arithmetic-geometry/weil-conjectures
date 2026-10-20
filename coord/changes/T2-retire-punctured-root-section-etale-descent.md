# AlgebraicGeometry.Scheme.punctured_root_section_etale_descent

## Reason

Retire the assigned duplicate `Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent`
in favor of the adopted `WeilConjectures` twin, as required by the retirement assignment in
`coord/retire-items.tsv`. The source theorem is already proved and is the declaration used by
the only live consumer. No source-library declaration is changed.

## Old

The duplicate Sheaf module declared the section-descent theorem with the
`strictHenselizationRing` interface and imported the duplicate root-limit presentation.

## New

The Sheaf module is withdrawn. The DAG node points to the existing source declaration
`WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent`, whose theorem
uses the adopted `strictHenselization` and `strictLocalizationToBase` interface. The source
module is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting | unclaimed | Uses the adopted source theorem already; no edit required. |

## Status

landed 20261020T233222-L-907515 2026-10-20 (merge of deliver/T2/Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootSectionEtaleDescent)
