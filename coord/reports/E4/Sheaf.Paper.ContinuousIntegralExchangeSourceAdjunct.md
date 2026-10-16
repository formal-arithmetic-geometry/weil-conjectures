## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_source_adjunct`
without changing its statement, hypotheses, universes or visibility. The proof combines two
formal identities: the exchange adjunct and the coefficient push/pull counit identity. The
latter is proved from Mathlib's iterated mate/conjugation theorem, and is transported through
the fully faithful bounded constructible inclusions using the restricted counit formula.
The combining calculation is a proved private categorical lemma, not a new assumed statement.

Added `Sheaf.CategoryTheory.AdjunctionSquareExchange`, a completely proved generic construction
of exchange by its adjoint, with naturality, adjunct and unit–square–counit equality lemmas.
Adapted the unclaimed source module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` to use it,
keeping the old definition's signature, public visibility and `@[no_expose]` setting.
Proved equation and adjunct API lemmas make the presentation usable without exposing its body.
Its equality theorem
proves the resulting transformation is precisely the original one. Its adjunct API avoids
expanding the concrete three-step term. No other group's module was edited.

Change record: `coord/changes/E4-exchange-adjoint-presentation.md`.

Validation: all three delivery modules compile with no warnings. The item also compiles after
removing the redundant exploratory Monoidal import. LowerShriekDefs and the direct parent
ContinuousIntegralExchangeEquality compile against the changed source. ProperApp also compiles against the final hidden-body source. The target signature is unchanged
verbatim. Axiom checks show only propext, Classical.choice and Quot.sound for the new generic
construction and its equality theorem. Concrete restricted declarations additionally inherit
existing upstream sorryAx; no new axiom or hole is introduced. The second reader runs the required dry run and delivery after the checks below.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_exchange_source_adjunct`
(node `lem-weil-pbc-continuous-integral-exchange-source-adjunct`).

No new holes, no split-offs and no sorry left in any delivered module. This is a proof, not a
decomposition into new unproved statements. Existing imported obligations elsewhere in the
library are unchanged. The new categorical constructor chooses no witnesses from existence
results; its components are explicit adjunction hom-equivalence images.

## No longer needed

Removed the redundant direct proof imports
`Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse` and
`Sheaf.Paper.ContinuousIntegralScalarExact` from the item. The exploratory direct import of
`WeilConjectures.CategoryTheory.ModuleObjects.Monoidal` was also removed after compilation
confirmed that the needed API is already available transitively. The exactness result remains used
transitively for the derived coefficient comparison, so its DAG dependency is retained.
The category-definition dependency is retained for the actual categories and restricted exchange.
The second reader also removed the redundant direct proof import of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`: it is
already publicly imported by `ContinuousIntegralComparisons`, including the new proved API.
No globally reachable node or module is withdrawn. No geometric exchange theorem, properness
hypothesis, push-comparison isomorphism or additional descent result is needed for this proof.

The new presentation does not need to unfold the three concrete step transformations in the
item's proof. They remain as the specified old construction and appear in the proved equality
API; they are not deleted or claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was correct. The old concrete exchange representation was expensive to convert during kernel checking.
An exported reflexivity/definitional-equation lemma is incompatible with `@[no_expose]`; the
final API instead uses ordinary proved equalities. Keeping `@[no_expose]` prevents expensive
downstream unfolding. A compatibility check of ProperApp identified this requirement, and its
baseline compiled successfully. The abstract categorical calculation itself compiles. The proved adjunct presentation fixes that computational obstacle and
preserves the map as a natural transformation. The target statement has not been weakened.

The lower preservation theorem
`boundedConstructible_rightDerivedLowerStar_obj` was already marked STATEMENT-DISPUTED in
`Derived.BoundedConstructible`; this delivery does not alter or resolve that upstream issue.
No new mathematical dispute is introduced.

## New nodes

`def-weil-pbc-adjunction-square-exchange` records the explicit generic adjunct presentation,
its naturality, adjunct formula and proved equality with the unit–square–counit construction.
All its Lean declarations are proved. Identity adjunctions, identity comparisons and empty
categories are covered by the generic categorical proof, with no geometric assumptions or
nonemptiness requirements. The item node and the existing condensed-category node now record
this representation and equality route. The change record is
`coord/changes/E4-exchange-adjoint-presentation.md`.


## Second reading by E4

1. **Interfaces and meaning: pass.** Compared every delivered module with the read-only
   repository using `diff` and the declaration parser. All six existing declaration statements
   (one in the item, five in MorphismDefs), their surrounding variables, universes, visibility
   and hypotheses are byte-identical. The only changed existing definition body is
   `boundedConstructibleBaseChange`, declared in the change record. Its proved equality with
   the old unit–square–counit natural transformation preserves every component and hence the
   meaning of downstream statements and targets. Repeated `downstream.py --uses` confirms
   the record's 56 downstream modules and 15 textual users. No forced adaptations occur.

2. **Proof and trust: pass.** Independently compiled all three delivery modules in import
   order with `lcompile.py`, without errors or warnings. Read every proof, including the
   exchange naturality and equality calculation, the iterated-mate coefficient identity,
   restriction of the counit through the fully faithful inclusion, and the final normal-form
   calculation. There is no `sorry` or forbidden declaration mechanism in the delivered Lean.
   Scratch copies with appended `#print axioms` show only `propext`, `Classical.choice` and
   `Quot.sound` for the generic constructor and its properties. The concrete definition,
   equality/adjunct API and item theorem additionally contain the existing imported `sorryAx`;
   no new hole is introduced. Independently compiled the unchanged downstream modules
   `LowerShriekDefs`, `ProperApp` and `ContinuousIntegralExchangeEquality` against the
   sandbox overlay; all three pass without warnings. All construction data are explicit
   hom-equivalence images;
   no arbitrary witness of unproved existence is selected.

3. **New statements and searches: pass.** No split-off statements or new holes exist.
   The generic constructor's naturality, adjunct identity and equality are all proved for
   arbitrary categories. Identity adjunctions and comparisons satisfy these same formulas;
   for an empty domain the component equations are vacuous. There is no nonemptiness or
   geometric assumption hidden in this API. Repeated searches with different wording using
   LeanFinder (Beck–Chevalley/right mates), Loogle (`mateEquiv_counit_symm`), Mathlib grep
   (triangle identities and restricted counits), and `rg` over the library confirm that the
   relevant shorter tools are Mathlib's mates and hom-equivalence identities. The coefficient
   proof already uses them. `mateEquiv` uses the original expanded composite; the new explicit
   adjunct presentation and proved equality address the documented conversion cost without
   introducing different exchange data.

4. **Route and pruning: pass.** The proof calculates the source side using the specified
   exchange, adjunctions and coefficient comparisons; it does not assume the complete desired
   exchange equality. The unit `sk-thm-properbasechange` and each of its `realized` steps are
   untouched. All old proof dependencies remain mathematically used, including scalar
   exactness through the integral comparison construction. The report lists every removed
   direct import, and no globally reachable module is claimed as pruned. The generic module's
   public imports are needed by its public statements; MorphismDefs publicly imports its new
   API because an exported equation names the generic constructor.

5. **DAG and records: pass after a metadata repair.** Read the two edited existing nodes,
   the new node, their dependencies, and the unit record against the Lean. Their proof steps
   and origins describe the actual naturality, mate, counit and representation-equality route.
   The new node has the required source, searches, creation, blueprint, unit and Lean fields.
   Added its complete public declaration list so its naturality and three equality/adjunct
   lemmas are indexed along with the constructor. The change record explicitly requests the
   normal target-definition review and supplies equality with the old definition as evidence.

**Changes made by this reader:** removed the redundant direct MorphismDefs import from the
item; indexed all five public declarations of the generic module in its DAG node; updated this
report. The mathematical proofs and definition presentation were retained.
