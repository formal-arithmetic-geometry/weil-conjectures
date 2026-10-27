## What changed

The remaining comparison in `Sheaf.Paper.WeilCompactSupportCohomology` is reduced
to open-only and proper-only realization statements, followed by the existing
normalized common-stage compact-support compositor. The proof represents the open
extension by G and the higher proper image by H, identifies the originally chosen
higher shriek object with H through the fully faithful Weil embedding, then
composes the underlying comparisons under standard cohomology. The supplied
integral-model isomorphism is mapped by the coefficient functor and its literal
value equation gives the required output.

New proof imports are `WeilIndOpenRealization`, `WeilIndProperHigherRealization`,
and `FieldShriekCompositionQcqs`. The two realization statements have their own
modules and nodes. `WeilGeometricFiberProperties` proves the elementary geometric
base-change properties they need below the item, avoiding a circular import.
A proved private equality-transport lemma avoids unfolding the normalized derived
limit when a geometric compactification is copied along the composition equality.
All existing declaration signatures, visibility, public imports and definition
bodies in the item remain unchanged. No other group's module is adapted and no
source-library declaration is changed. The normalized coefficient actions are
existentially eliminated only inside the proof; no definition chooses arbitrary
operation data from their existence statement.

The main module compiles cleanly through `lcompile.py` in 4.5 seconds. The two
new theorem interfaces and the geometric helper compiled earlier in 31–36 seconds
per file. The delivery validation recompiles the final packet in import order after the
duplicate helper instances were removed.

## Proved and sorry left

The launch baseline has one hole in the item:
`WeilConjectures.zlWeilHigherShriek_compactSupportComparison`, node
`def-zl-weil-compact-support-cohomology`. Its new body is a combining proof from
the two separately named realization inputs. The earlier representability and
compactification-independence combining proofs were already present at launch
and are not counted as new work by E3.

Two holes are introduced, each in its own module, with source and proof in words:

- `WeilConjectures.zlIndWeilOpenShriek_realization`,
  `lem-zl-ind-open-realization`.
- `WeilConjectures.zlIndWeilProperHigher_realization`,
  `lem-zl-ind-proper-higher-realization`.

This is a decomposition of one original hole into two independent geometric
realization results, not a net reduction in holes and not a complete proof of
those results. The geometric-fibre helper module and compactification-value transport lemma
have zero holes. No axiom or hole inside a definition is introduced.

The open statement has no proper leg or cohomology degree. The proper statement
has no open leg, composite compactification or integral representative. Thus
neither restates the original compact-support comparison under a new name.
Both include zero sheaves, empty schemes and identity morphisms; the proper
comparison also includes degree zero. The statements quantify over every
normalized action and every representing isomorphism. Full faithfulness makes
the represented object unique up to the isomorphism used here.

## No longer needed

No original import, declaration, module, DAG node, or unit step is removed.
Three duplicate geometric-fibre helper declarations were removed during development:
the existing `SfCommonStageWeilCohomology` base-change API already supplies their
structure-map finite-type and quasi-compactness instances.
The comparison uses the existing geometric coefficient composition theorem;
it does not require importing `CommonStageWeilShriek`, which imports the item,
or the absolutely separated open/closed localization packages. Their stronger
hypotheses are not silently added. Existing representability and refinement
inputs remain necessary to the other proofs in the module.

## Where the brief, the DAG or earlier work was wrong

The historical route note describes a saved four-module packet. That packet was
absent from this sandbox. Current repository sources already contain Q9's landed
representability and compactification-independence combining proofs, leaving
only the recorded-value comparison. The required initial delivery attempt
reported `FAILED: report.md is missing`; nothing was pushed by that attempt.
The rework entry was inspected before copying: the current item is present,
and no quarantined source or attachment is withdrawn. There is no current
numbered return entry for this item in E3's returns.

The existing open/proper representability theorem signatures assert existence
of representatives but do not identify their underlying constructible carriers.
Their natural-language proofs describe the needed realization, but those words
cannot be used as a Lean conclusion. The two new statements expose exactly
these missing open-only and proper-only comparisons.

Barrett, *The derived category of the abelian category of constructible sheaves*,
Theorem 1.1 (https://arxiv.org/pdf/2005.10859, page 1), was read directly. It covers
the ordinary constructible heart over algebraically closed fields, with finite
or ell-adic coefficients, on separated varieties. The descent to nonseparated
finite-type schemes, this specific ind model, finite coefficient stages and Weil
pairs remains part of the proper realization obligation; the cited theorem
alone does not formally discharge it. Existing abstract Ind realization results
instead concern finitely presentable subcategories of a given ambient category
and do not identify this constructible derived realization.

The source's canonical ind-derived definition is retained. Replacing it by
cohomology of an adjoint-defined compact-support functor would evade this
comparison while forcing changes to its genuine ind-derived consumers.

## New nodes

`def-zl-weil-geometric-fiber-properties` attaches the fully proved lower geometric
helper module. It gives canonical morphism compatibility, base-change permanence and
the coefficient-prime unit proof, with no cohomological assertion. Existing
structure-map base-change instances are imported and reused.

`lem-zl-ind-open-realization` attaches
`lean/Sheaf/Paper/WeilIndOpenRealization.lean`: realization of a represented open
extension against the normalized identity-proper coefficient action.

`lem-zl-ind-proper-higher-realization` attaches
`lean/Sheaf/Paper/WeilIndProperHigherRealization.lean`: the ordinary proper higher
image realization against the normalized identity-open coefficient action.

Blueprint search for `ind.*realization|realization.*ind|Barrett|represented` returned
zero matching blueprint nodes; the ancestor lookup confirms
`lem-zl-composition-weight-bound`. Broader searches for `open extension` and
`proper direct image` returned 11 and 26 blueprint matches; their normalized
site operations, proper-heart bounds and Ext continuity do not state this
comparison for the prescribed common-stage equivariant ind model.
The new nodes serve its first paragraph and keep
the realized unit route.

The original node's proof plan now follows the actual combining proof and cites
these two interfaces and the existing coefficient composition and action-existence
nodes. All nodes keep the original chapter and unit route. No existing statement
or definition is changed, so there is no change record or forced adaptation.

The open and proper realization nodes cite the existing coefficient realization,
operation-reduction and standard-heart nodes as tools from their own chapters. The
open argument additionally needs the normalized integral open-reduction comparison
and open standard-class preservation. These supply lower geometric facts, rather
than a different route around the composition unit. No `tool_uses` approval is
added by the worker.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
