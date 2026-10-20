# AlgebraicGeometry.Scheme.strictHenselizationRing_local_presentation

## Reason

`coord/retire-items.tsv` assigns retirement of the duplicate
`Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation`. The adopted source
module already proves the same geometric-to-algebraic strict-henselization
presentation. Keeping both modules defines the same public declaration twice.
Use the existing upstream theorem and preserve the DAG node and all parent edges.

## Old

Defined in `Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation`:

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

## New

Use the existing declaration of the same fully qualified name in
`WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation`:

```lean
theorem strictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselization barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselization barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselization barY)
```

The upstream theorem uses the affine-neighbourhood colimit `strictHenselization`
and its canonical `strictLocalizationToBase`; the retired theorem used the
small representative colimit `strictHenselizationRing` and its structural map.
Both present the same pointed étale-neighbourhood diagram, compared by
`smallStrictHenselizationColimitIso`. The theorem still returns a prime
localization, its residue-field separable closure, compatible scalar towers and
algebra structures, the exact structural R-map, and `Algebra.IsStrictHenselization`.
No prime, separability, or structural compatibility clause is dropped.
The upstream proof already constructs this presentation over an arbitrary open
affine chart and specializes to the identity chart. It is preserved verbatim.

The obsolete Sheaf module is withdrawn with `deleted.txt`. Its one current Lean
importer is migrated by changing its private import to the upstream module.
The node's Lean attachment and proof description now point to the retained proof.
The natural-language statement, dependencies, unit route and all parent edges stay.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.CoordinateMaximalBranchStratum | unclaimed | Only the private import changes to the upstream module. The theorem statement and its existing sorry proof are byte-for-byte unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation | unclaimed | Already imports and applies the upstream theorem; no source change. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation | quarantined, unclaimed | Absent from the live library; its archived source and DAG attachment are preserved. Its DAG edge still names the retained presentation node. The live upstream counterpart already uses the retained theorem. |

`tools/downstream.py` lists only the trace-formula module as a current importer.
No live Lean application uses the retired small-colimit theorem: the trace-formula
module's proof is still sorry and uses no theorem body. DAG parents, including
unfinished and quarantined parents, continue to have the presentation statement
through its upstream Lean attachment; no mathematical dependency is pruned.
No Challenge declaration or definition is changed.

## Status

landed 20261020T161323-L-3476889 2026-10-20 (merge of deliver/J3/Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation)
