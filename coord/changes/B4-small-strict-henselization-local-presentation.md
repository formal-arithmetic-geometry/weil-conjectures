# AlgebraicGeometry.Scheme.smallStrictHenselizationRing_local_presentation

## Reason

The item has two implementations with the same fully qualified theorem name:
the Sheaf version on the small coordinate-ring colimit and the retained upstream
version on the larger affine-neighbourhood colimit. The latter uses
`strictHenselization` and `strictLocalizationToBase`; the consumer needs
`strictHenselizationRing` and `strictHenselizationStructuralMap`.
A previous retirement removed the Sheaf theorem without adapting its surviving
divisor-quotient consumer. During this session the shared delivery base refreshed
and restored the Sheaf direct proof. This packet is reconciled with that restored
base: replace its full chart/triples proof with canonical transport from upstream,
and rename the small-colimit result to avoid colliding with the upstream name.

The upstream declaration, proof, public imports and all source-library files stay
unchanged. The consumer's sole proof edit uses the new compatibility name. The
small-colimit theorem has exactly the old hypotheses and conclusion, under a
new name. The existing mathematical DAG node keeps its natural-language statement
and all parent edges; only its Lean attachment and proof are updated. The four
dependency nodes remain needed through the retained upstream proof.

The public structural-map import changes from the Sheaf compatibility module to
the upstream module. Keeping the old public import together with the retained
upstream presentation fails on duplicate `strictHenselizationStructuralMap_eq`
from the Sheaf module and upstream StructuralMapExtension. Both direct importers
compile with the new import. Their existing signatures and statements are unchanged.

The original consumer checked against the delivered item interface reports at line 65:
`Unknown identifier strictHenselizationRing_local_presentation`. The adapted consumer
compiles. Its statement and all other proof lines are byte-for-byte unchanged.
The consumer is unclaimed. No module held by another group is edited.

## Old

The source at session start was a withdrawn stub. The refreshed delivery base
has this proved Sheaf theorem (its direct chart/triples proof is replaced):

```lean
theorem strictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselizationRing barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselizationRing barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselizationRing barY)
```

Its public structural-map import was:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
```

The live consumer's original application is:

```lean
    strictHenselizationRing_local_presentation R barY b hb
```

## New

The item exports the following proved theorem, together with a proved private
comparison of the two structural morphisms:

```lean
theorem smallStrictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselizationRing barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselizationRing barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselizationRing barY)
```

The consumer application becomes:

```lean
    smallStrictHenselizationRing_local_presentation R barY b hb
```

Both rings are actual colimit constructions. Their canonical comparison preserves
coprojections. The proof checks the structural-map equality on a representative leg,
uses the upstream presentation, and transports the algebra map and its universal
cocone along the inverse comparison. All existential witnesses in the conclusion
and the elementwise structural-map equation are retained. No definition or theorem hypotheses or conclusions change; no Challenge declaration or definition is modified.

## Users

`tools/downstream.py` lists these downstream modules for the item. Its declaration
search finds only the divisor-quotient consumer's actual application, besides the
item's own use of the retained upstream theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoordinateBlowupBranchDrop | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation | unclaimed | Proof application renamed; signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | D3 | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | D4 | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.NCMaximalBranchBlowup | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.AlgebraicGeometry.NormalCrossingsStrictification | unclaimed | No source change; all previously used signatures remain identical. |
| Sheaf.TraceFormula.CoordinateMaximalBranchStratum | unclaimed | No source change; all previously used signatures remain identical. |

The immediate next caller
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`
compiles unchanged against the delivered modules. Both the bridge and the adapted
divisor-quotient theorem use only propext, Classical.choice and Quot.sound.
The consumer statements remain unchanged, so no target-statement review is reopened.

## Status

landed 20261020T221044-L-4138130 2026-10-20 (merge of deliver/B4/Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation)
