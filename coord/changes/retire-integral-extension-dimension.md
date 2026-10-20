# RingHom.integralExtensionDimension

## Reason

Remove the renamed duplicate in the Sheaf tree after redirecting its only remaining
direct importer to the identical, proved source-library theorem. This is the
retirement assigned in `coord/queue.tsv`. No source-library declaration, attribute,
public import or proof is changed. No target statement or definition changes.

## Old

```lean
theorem integralExtensionDimension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
      ∀ (I : Ideal S), I.IsMaximal → (I.comap f).IsMaximal
```

## New

Withdraw the duplicate declaration and its module. Use the existing theorem from
`WeilConjectures.RingTheory.IntegralExtensionDimension`, verbatim:

```lean
theorem IsIntegral.ringKrullDim_le_and_isMaximal_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
      ∀ (I : Ideal S), I.IsMaximal → (I.comap f).IsMaximal
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.IntegralExtensionDimension | P2 | Withdraw the duplicate; attach its existing node to the source theorem. |
| Sheaf.RingTheory.HopfAlgebra.AugmentationHeight | unclaimed | Change only the private proof import and theorem application; same statement and argument. |
| WeilConjectures.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing | unclaimed | Already uses the source theorem; no edit. |

The downstream check lists only the augmentation-height module and the declaration
in its own module as users. The analytically-unramified module was listed as a
consumer in the retirement inventory and has already been redirected. The Sheaf
copy of that module is absent from the current source tree; its source-library
replacement already uses the source theorem. Transitive consumers keep the same
augmentation-height statement and public imports. The attached DAG node now names
the existing source-library theorem. No target semantic review is reopened.

## Status

landed 20261020T144258-L-2260983 2026-10-20 (merge of deliver/P2/Sheaf.RingTheory.IntegralExtensionDimension)
