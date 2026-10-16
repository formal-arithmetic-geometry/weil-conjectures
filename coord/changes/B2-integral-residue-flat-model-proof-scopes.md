# Flat-model proof scopes and ordinary compatibility lemma

## Reason

The proof needs explicit derived-functor factorization and inverse-mate calculations.
Repeated synthesis of canonical module-category tensor and resolution structures made
compilation expensive. Private wrappers cache these actual canonical constructions.
Their instance registrations are local to the private proof-calculation section;
the public target statement is outside that section. The final proof installs the
same structures locally, after its signature has been elaborated. No private helper
occurs in the public target signature.

The static interface checker flags added open, notation, variable and attribute
commands. This record documents their scope, together with the one new ordinary
compatibility theorem. No existing public definition or theorem signature changes.

## Old

`Sheaf.Paper.IntegralResiduePullFlatModel` publicly imported only its square-data
interface, opened the standard categorical namespaces, made `leftDerivedFunctor`
locally irreducible, and had one unproved `residueExchangePull_flatModel` theorem.
There was no `Sheaf.Paper.IntegralResiduePullOrdinaryUnit` module.

## New

The same public import and exact target signature are retained. Three proof-only
imports in the assigned module supply flat preservation, the ordinary unit lemma,
and the symmetry API for deriving natural isomorphisms. Additional scope commands,
the canonical-structure caches and all generic calculation helpers are local/private
proof infrastructure.
The proof uses no new axioms. The new public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_ordinary_unit` states
only the ordinary homotopy-category scalar-unit compatibility. Its complete signature,
source and proof plan are in its new module and matching DAG node. It is fully proved
by the geometric/scalar mate identities and passage to the homotopy category.
It introduces no proof hole or new chosen data. Its public import is the narrower
`Sheaf.Paper.ContinuousIntegralCoefficients`; the derived square-data module is
not needed for this ordinary statement. Its underlying-sheaf comparison module
is imported only for the proof, using `import all` to reuse its existing private
`moduleUnit_forget` theorem. The duplicate local helper and its unused `True`
argument are removed entirely.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResiduePullFlatModel | B2 | Completed proof with original signature and canonical instances. |
| Sheaf.Paper.IntegralResiduePullSquareIsIso | unclaimed | Sole direct importer and textual consumer; application and statement unchanged, no adaptation. |
| Sheaf.Paper.IntegralResiduePullOrdinaryUnit | B2 (new) | Proved ordinary compatibility theorem, used only by the assigned item. |

All transitive consumers receive the existing flat-model theorem statement;
private proof scopes change no definitions used downstream. There are no forced
adaptations and no target statement review is reopened.

## Status

landed 20261016T180844-L-2345227 2026-10-16 (merge of deliver/B2/Sheaf.Paper.IntegralResiduePullFlatModel)
