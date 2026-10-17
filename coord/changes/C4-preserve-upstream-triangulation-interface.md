# AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible_padicIntegers

## Reason

Repair both gate objections in the C4 return at b217ecd04. The adopted source interfaces
must remain verbatim. The previous proposed deletion of the disputed arbitrary-ring
instance and the public structural additions are therefore withdrawn. The valid integral
p-adic variant remains in its own Sheaf module. This is a partial repair: it does not prove
or remove the false arbitrary-ring assertion.

A genuine proof is also supplied for the unclaimed rationalization consumer's existing
bounded-constructibility preservation lemma. Its only new imports are private proof imports.
This closes one pre-existing hole without changing any existing signature or public import.

## Old

The source declaration retained by this repair is:

```lean
instance isTriangulated_boundedConstructible [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible R).IsTriangulated :=
  sorry
```

The source consumer's existing lemma
`AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalars_obj` had proof `sorry`.
The returned proposal removed the displayed instance, added three public structural
instances to that source module, and added a public Sheaf import to its consumer.

## New

All existing source signatures, declaration attributes, definitions and public imports
are identical to the shared repository. The disputed instance and its hole are retained;
its actual declaration now has the explicit dispute comment. The already proved
`isTriangulated_boundedConstructible_of_serre` remains unchanged. The three rejected new
source instances are absent.

The true specialization is in
`Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated`:

```lean
instance isTriangulated_boundedConstructible_padicIntegers :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)).IsTriangulated
```

It has a complete proof from the existing integral constructible Serre theorem and the
conditional source theorem. It does not invoke the disputed arbitrary-ring theorem.
The integral coefficient object and its valuation ring are not redefined.

The existing scalar preservation lemma now proves the normed-algebra inequality for the
induced norm, applies `CondensedRing.integralScalarExtension_exact`, and then applies
`boundedConstructible_leftDerivedExtendScalars_obj`. The definitions of the actual integral
ring and inclusion agree definitionally. Both imported results are used, and both imports
are private. The separate localization instance remains open.

## Users

There is no change to an existing importer-visible interface, so no consumer adaptation
is forced. The source consumer is unclaimed and may be proved under the supplied brief.
No other module is adapted. The new specialization has no existing importer: it records
the sound coefficient-specific variant requested by the return rather than substituting
a weaker statement for the disputed upstream assertion.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory | C4 | Documentation only; all declarations and proofs retained. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | One lemma proved; two private proof imports; public interface retained. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | new in C4 delivery | Fully written integral-coefficient triangulation variant. |

## Status

landed 20261017T024326-L-1172933 2026-10-17 (merge of deliver/C4/WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory)
