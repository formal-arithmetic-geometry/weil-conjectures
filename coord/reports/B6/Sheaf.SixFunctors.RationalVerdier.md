## What changed

Decomposed `WeilConjectures.coef_rational_verdier` into four genuine subarguments:
existence of one normalized rational duality datum; existence of the normalized comparison
for one finite coefficient embedding; the identity equation; and the composition equation.
The top-level proof uses classical choice locally to select a family of datum witnesses
and normalized comparisons, retains their normalization proofs, then applies the unit and
composition statements to those same choices. It introduces no public chosen data.

Moved the eleven existing `RationalVerdier` definitions to
`Sheaf.SixFunctors.RationalVerdierModels` and publicly reexported them from the original
module. This breaks the otherwise unavoidable cycle between the interfaces and their
proof-step modules. Existing names, signatures, constructor fields, category definitions,
completion normalization, evaluation and biduality formulas are preserved. The slow
completion witness projection is bounded as described in
`coord/changes/B6-rational-verdier-models-and-completion.md`.

## Proved and sorry left

The original hole `WeilConjectures.coef_rational_verdier`
(node `thm-coef-rational-verdier`) is replaced by a complete assembly proof.
This is a **decomposition**, not a completed proof of rational Verdier duality:
one upper hole is closed and four strictly smaller holes are added, for net minus three.
The item module contains zero remaining holes. No definition contains a hole.
The elementary helper RationalVerdier.third_exists_first is fully proved and introduces
no hole or new assumption; it only permutes existential witnesses.

The four remaining public theorem holes, one per new module, are:

- `WeilConjectures.RationalVerdier.datum_exists`
  (`lem-coef-rational-verdier-datum`, `Sheaf.SixFunctors.RationalVerdierDatum`);
- `WeilConjectures.RationalVerdier.extension_exists`
  (`lem-coef-rational-verdier-extension`, `Sheaf.SixFunctors.RationalVerdierExtension`);
- `WeilConjectures.RationalVerdier.extension_unit`
  (`lem-coef-rational-verdier-unit`, `Sheaf.SixFunctors.RationalVerdierUnit`);
- `WeilConjectures.RationalVerdier.extension_composition`
  (`lem-coef-rational-verdier-composition`, `Sheaf.SixFunctors.RationalVerdierComposition`).

Each is exactly a public named `:= by sorry` theorem with its source, complete proof in
words, blueprint reference and DAG node. The first omits all extension comparisons;
the second assumes the two single-field data and omits coherence; the last two assume
the relevant normalized comparisons and assert separate coherence equations. None
restates the original simultaneous family-and-coherence conclusion.

Edge cases checked at statement level: empty X; zero and torsion integral representatives;
E equal to the ground field; identity embeddings; towers with repeated fields. The
normalization hypotheses pin the actual u, beta, unit and associator. No injectivity or
faithfulness of rationalization is assumed. In particular rationally zero torsion inputs
do not permit cancellation through localization.

Validation before the final local unfolding refinement: all six delivered modules
compiled successfully together in dependency order
with lcompile.py --all (exit 0). The delivery tool also performs its independent compile,
axiom probe and preflight. No import-closure proof completion is claimed.

## No longer needed

No mathematical node or module is withdrawn. The seven original arguments all remain
in the four new proof-step nodes, including the integral-to-completed tensor correction.
The unit record has no realized steps to bypass, and its route through integral and
rational coefficient duality is retained.

The original item no longer directly imports the following prospective proof imports:
`Sheaf.Paper.IntegralResidueTor`,
`Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`,
`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`,
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`,
`Sheaf.Paper.FiniteTorAmplitude`, `Sheaf.CategoryTheory.ScalarLocalization`,
`Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`,
`Mathlib.LinearAlgebra.TensorProduct.Basic`, `Mathlib.RingTheory.Localization.Away.Basic`,
`Sheaf.Paper.PbcRationalTransport`,
`Sheaf.Paper.IntegralOperationsPreserveConstructible`.
The datum step retains IntegralResidueTor, PbcRationalTransport and
IntegralOperationsPreserveConstructible in its stated proof-dependency plan. Other declarations
are available through existing public interface imports. No import-closure pruning
or net proof progress is claimed. The old top-level tool_uses entries for
prop-weil-pbc-rational-transport, lem-pur-integral-operations-preserve-constructible
and lem-fix-constructible-tensor-completion are removed only from the assembly node;
the corresponding arguments and dependencies stay in its new subnodes.

## Where the brief, the DAG or earlier work was wrong

The current blueprint proof and blueprint_update describe condensed coefficient
categories and scalar-six comparisons, while the reviewed Lean statement uses the
recorded raw localization and the older explicit seven-step integral rationalization
argument. This delivery retains the assigned statement and its defining interfaces;
it does not silently replace raw localization by a different category. The new nodes
cite the current blueprint's corresponding single-field/comparison/coherence clauses
and record the full earlier rationalization arguments that implement this interface.

The model-interface compile timed out at 60 seconds. Earlier profiling identified
42.2 seconds in kernel checking completionChain._proof_4. A proved generic witness-permutation helper
avoids re-expanding the full tensor-completion predicate, and the model module compiles
in 32.7 seconds. The change record gives
the exact original and replacement construction. The first delivery attempt timed out and pushed nothing; local unfolding controls
were then refined without altering any predicate or arrow. No timeout limit was raised and no
file was split to evade the time limit: model extraction exists to eliminate an
interface/proof dependency cycle.

## New nodes

`lem-coef-rational-verdier-datum` realizes original steps 1--5, for one fixed coefficient
field and coherent dualizing input. Its statement has none of the coefficient extension
or family coherence conclusion.

`lem-coef-rational-verdier-extension` realizes original step 6, for one embedding and two
given normalized data. It supplies only the normalized comparison and its evaluation
and biduality squares.

`lem-coef-rational-verdier-unit` realizes the identity half of step 7 for an already given
normalized comparison. It preserves the exact localization formula for tensor multiplication.

`lem-coef-rational-verdier-composition` realizes the associator half of step 7 for three
already given normalized comparisons. It preserves the exact integral associator formula.

All four inherit the item's chapter and unit, and carry actual msearch.py search records.
The existing definition ownership record points to the relocated model module.
Change record: `coord/changes/B6-rational-verdier-models-and-completion.md`.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer correction (stage-3 review of 06a6b628351b)

`extension_exists` was stated for arbitrary data `A`, `B`. `IntegralVerdier.SignedSymmetry`
pins `swap` only on literal pairs `(Q P, Q Q)` of K-flat complexes and asks no naturality,
while `delta` uses the swap at `(RHom(K, ω), K)`, whose object is a `Localization.lift`
value. A datum whose swap is negated off those pairs has `bidual = -δ`. It is still a
`Datum`, but the biduality clause of `ExtensionProperties` fails against a canonical `B`.
The counit choices of the ordinary presentations cancel between δ and β, so the
symmetry is the only free part. The single-field step is now `datum_exists`: a datum whose
swap is natural in both variables. `extension_exists` takes that naturality for `A` and `B`
as hypotheses (`hA`, `hB`), and the assembly passes the chosen naturality proofs.

