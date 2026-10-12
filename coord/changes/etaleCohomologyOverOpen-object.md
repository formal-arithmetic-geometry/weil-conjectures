# AlgebraicGeometry.etaleCohomologyOverOpen

## Reason

The old declaration is false: it uses global cohomology on X on the left rather than
cohomology over j : U to X. Its existing degree-zero obstruction demonstrates the
incompatibility when global sections are nontrivial and restricted sections are trivial.
For the empty open in a nonempty scheme, the constant integer sheaf is a counterexample.
Stacks 03F3 and the unchanged DAG statement require object cohomology.

Keep the original schemes, open/etale hypotheses, coefficient universe, and HasExt
instances. Use the free abelian sheaf on uliftYoneda(j) as the first Ext argument.
Mathlib Sheaf.H' uses the site's Hom universe for the coefficient category, so it cannot
accept the existing AddCommGrpCat.{u + 1} coefficients on the u-Hom etale site.
This explicit large-universe Ext formulation represents the same sections and is proved
by a real representing isomorphism and the exact Ext adjunction, with standard axioms only.
No target declaration or existing data definition is changed. The new comparison and
restriction data are constructed without sorry; their properties are recorded separately.

## Old

```lean
theorem etaleCohomologyOverOpen {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty (Sheaf.H G q ≃+
      Sheaf.H ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) q)
```

## New

```lean
theorem etaleCohomologyOverOpen {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [Etale j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Nonempty (Abelian.Ext
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free)) G q ≃+
      Sheaf.H ((Etale.openImmersionRestriction (A := AddCommGrpCat.{u + 1}) j).obj G) q)
```

The repair additionally exposes the concrete comparison as
AlgebraicGeometry.etaleCohomologyOverOpenEquiv in the new comparison-data module.
The representing and sections helpers are public constructions under
AlgebraicGeometry.EtaleOpenComparison, not private constants in public definition bodies.
Coefficient naturality of this comparison is proved. The three clause declarations are
reused from their defining modules rather than duplicated in the item's module:
- AlgebraicGeometry.etaleCohomologyOverOpenEquiv_naturality, from
  Sheaf.AlgebraicGeometry.EtaleOpenCohomologyComparison;
- AlgebraicGeometry.etaleCohomologyOverOpenEquiv_restriction, from
  Sheaf.AlgebraicGeometry.EtaleOpenCohomologyRestrictionCompatibility;
- AlgebraicGeometry.etaleTensorSectionsSheaf_openIdentification, from
  Sheaf.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentification.

All three modules are publicly imported so downstream users can access the clauses
under their original names. No duplicate wrapper declaration remains. These wrappers
were additions in the refused delivery, not declarations of the existing library.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen | F2 | Corrected and proved object comparison; added all three missing clauses, with two explicit obligations. |
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | N2 | The only direct importer; it never applies the declaration, explicitly imports EtaleTensorSectionsSheaf, and compiles unchanged against the delivered module. No adaptation. |

The downstream scan found 131 transitive importers, but none mentions the declaration.
The direct importer passes single-file compilation against the changed module, including
the removed public imports, so the interfaces used by transitive importers are unchanged.
There is no forced adaptation. The prose DAG statement is unchanged. The return's
three missing clauses are now encoded by public declarations, with coefficient naturality
proved and the other two supplied by named public obligations in new modules. The old
quasi-coherent proof step and all five dependencies are restored; inverse-image restriction
is additionally restored in the exactness step. No target statement changes.

## Status

landed 20261012T151907-L-2287849 2026-10-12 (merge of deliver/F2/Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen)
