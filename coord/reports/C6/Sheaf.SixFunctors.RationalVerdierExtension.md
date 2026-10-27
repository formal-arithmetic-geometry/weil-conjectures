## What changed

`Sheaf.SixFunctors.RationalVerdierExtension` now constructs the comparison rather
than choosing an `Extension` from an unproved existence statement. Its statement
and existing docstring are unchanged.

The proof applies `IntegralFiniteExtension.comparison_invertibility` to the
supplied ordinary presentations. It proves invertibility of beta as the composite
of v and internal Hom into u, reflects both maps into the constructible full
subcategories, and maps the resulting isomorphisms through rational localization.
The object equations of A, B and rational scalar extension supply explicit
`eqToIso` transports. The integral-origin normalization equations are proved by
the heterogeneous equality API. `NatIso.ofComponents` assembles these actual
components once their naturality is supplied.

Three new modules isolate distinct remaining compatibility calculations:
`RationalVerdierComparisonNaturality`, `RationalVerdierComparisonEvaluation`, and
`RationalVerdierComparisonBiduality`. The last takes the evaluation square as a
hypothesis and asserts its consequence for biduality. The item contains a complete
Lean proof combining these lemmas with its explicit construction. There is no
new definition, arbitrary chosen datum, changed existing signature, or adaptation
of another existing module. The four added imports in the item are proof imports.

## Proved and sorry left

The original module has one hole, `WeilConjectures.RationalVerdier.extension_exists`.
It has been closed by decomposition, with no direct `sorry` remaining in the item.
This is not counted as an unconditional proof of that original hole: zero of the
one original holes is proved outright, one is decomposed, and three holes are
added. The actual localized component constructions, their invertibility, their
normalizations, and the final assembly are fully proved Lean.

Every new hole is the whole proof of a public theorem, one per module:

- `WeilConjectures.RationalVerdier.localizedBeta_naturality`, node
  `lem-coef-rational-verdier-comparison-naturality`;
- `WeilConjectures.RationalVerdier.normalizedExtension_evaluation`, node
  `lem-coef-rational-verdier-comparison-evaluation`;
- `WeilConjectures.RationalVerdier.evaluation_implies_biduality`, node
  `lem-coef-rational-verdier-comparison-biduality`.

None restates comparison existence: the first concerns a supplied family of
arrows and asserts only naturality, the second concerns a supplied normalized
Extension and asserts only evaluation compatibility, and the third derives only
the biduality square from evaluation and natural symmetries. In particular none
supplies the isomorphisms, their inverses, or the normalization proof used to
construct the item.

The unchanged original item compiled against published artifacts, so the recorded
older missing-import failure is not reproduced. The complete delivery is checked
in import order with `lcompile.py` and by `deliver3.py` before push. No debugging
options or temporary proof holes remain in the item.

## No longer needed

No original Lean import is removed: the sole original public import,
`Sheaf.SixFunctors.RationalVerdierModels`, is required by the statement.
No module is withdrawn or claimed globally pruned.

The item's former direct proof dependency on the whole
`lem-coef-integral-finite-extension` theorem is replaced by its narrower
`lem-sf-integral-finite-extension-invertibility` sublemma, which applies directly
to the supplied A.ordinary and B.ordinary. Its chosen presentation, finite-reduction,
identity and composition conclusions are not used in the construction.

The former direct dependencies `def-weil-derived-pullback-tensor-hom` and
`lem-fix-constructible-tensor-completion` are needed by the remaining compatibility
calculations and are recorded there, rather than by the item's assembly proof.
They remain needed transitively. `def-weil-rationalization-karoubi` remains a direct
proof dependency for the object equation and localization functor. The rational
and algebraically closed operations downstream of RationalVerdier are not
imported: in particular RationalVerdierEvaluationAdjoints would introduce a cycle.
The unit route and all parent dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier node represented construction, rational naturality, completion
normalization, and transposition to biduality as one step. The stated integral
finite-extension theorem supplies its compatibility squares for its own chosen
presentations, so those squares cannot simply be applied to arbitrary supplied
A and B. The proof now uses its universally quantified invertibility sublemma
for construction and states the remaining three calculations precisely.

The naturality hypotheses on the two signed symmetries are retained and used in
the biduality step. No claim is made that a SignedSymmetry fixed only on literal
K-flat pairs determines its values elsewhere without naturality. The new statements
were checked on identity coefficient embeddings, zero objects, and empty X: the
same tensor and transpose formulas apply, and no nonzero or positive-degree
assumption has been added. The biduality lemma permits an arbitrary dualizing
isomorphism satisfying the evaluation square; it does not silently assume a
canonical normalization of that isomorphism.

## New nodes

`lem-coef-rational-verdier-comparison-naturality`, realized by
`WeilConjectures.RationalVerdier.localizedBeta_naturality`, isolates the
naturality calculation for localized beta arrows, with their exact integral
normalization. It assumes no natural isomorphism or comparison existence.

`lem-coef-rational-verdier-comparison-evaluation`, realized by
`WeilConjectures.RationalVerdier.normalizedExtension_evaluation`, isolates
the ordinary-to-completed tensor conjugation and localization of the evaluation
transpose for a supplied normalized comparison.

`lem-coef-rational-verdier-comparison-biduality`, realized by
`WeilConjectures.RationalVerdier.evaluation_implies_biduality`, isolates the
second transpose: natural Koszul symmetries and the supplied evaluation square
imply the square for the actual prescribed bidual maps.

All three come from paragraph 3 of the current rational Verdier proof and the
last transposition paragraphs of the current integral finite-extension proof.
Their docstrings and DAG records include complete proof sketches. The searches
used LeanSearch, LeanFinder, Loogle and Mathlib/project grep; they found generic
adjunction and natural-isomorphism assembly tools, but no existing theorem giving
these completed, presentation-normalized calculations. Blueprint and DAG searches
found no duplicate component statement. No change record is required for an
existing interface: all existing signatures and public imports are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierComparisonBiduality": "b5f9173213e417569d998aefef01a43cc186fd20", "Sheaf.SixFunctors.RationalVerdierComparisonEvaluation": "07cf6a5b79f9111c1fd9715b210ed50441977d59", "Sheaf.SixFunctors.RationalVerdierComparisonNaturality": "c0e1097a0fa8045343c640c81b7471d9526866e1", "Sheaf.SixFunctors.RationalVerdierExtension": "eb03a68ef0c262d17b9fb672cbd50ff32a56c64c"}, "results": {}, "time": "2026-10-27T23:50:20+0800", "transitive": 0, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
