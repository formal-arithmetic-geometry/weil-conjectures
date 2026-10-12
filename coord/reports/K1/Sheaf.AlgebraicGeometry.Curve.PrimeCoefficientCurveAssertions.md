## What changed

Removed the returned first-half and second-half restatements and their imports. The target now
uses dense-open localization, the finite-etale filtration and trace witness, and two substantive
geometric reductions: constant lower-shriek assertions on reduced curves and transfer through the
finite cover. Both helper proofs remain explicit named `sorry`s with complete source-based proofs
in their docstrings.

## Proved and sorry left

`primeCoefficientCurveAssertions` is proved by a real witness extraction and application of the
transfer theorem. `reducedConstantLowerShriekAssertions` remains `sorry` at node
`k1-reduced-constant-lower-shriek-assertions`; `filteredFiniteCoverLowerShriekTransfer` remains
`sorry` at node `k1-filtered-finite-cover-lower-shriek-transfer`.

## No longer needed

Removed `PrimeCoefficientCurveAssertionsFirstHalf` and `PrimeCoefficientCurveAssertionsSecondHalf`,
their imports, nodes, and cyclic dependencies. The retained route uses the existing dense-open and
finite-locally-constant reduction declarations plus the two substantive helper nodes.

The baseline imports only `WeilConjectures.AlgebraicGeometry.Curve.Assertions`; that public
import is preserved. The first/second-half modules mentioned above belonged to a returned,
unlanded attempt and are absent from this delivery. No baseline module is removed.

The following old direct `proof_deps` are moved below the two geometric helper nodes, rather
than claimed to be globally obsolete. All remain in the revised proof-dependency closure:

- `def-nagata-scheme-theoretic-closure`
- `def-sc-constant-sheaves`
- `def-weil-pbc-constructible-torsion`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-eight-curve-assertions`
- `def-weil-pbc-etale-constructible-sheaf`
- `def-weil-pbc-extension-by-zero`
- `def-weil-pbc-finite-open-comparison`
- `def-weil-pbc-primary-torsion`
- `def-weil-pbc-scheme-reduction`
- `etale-proposition-etale-reduced`
- `lem-sc-smooth-normal`
- `lem-weil-pbc-closed-immersion-finite`
- `lem-weil-pbc-constructible-torsion-modules-agree`
- `lem-weil-pbc-curve-assertions-dense-open`
- `lem-weil-pbc-curve-assertions-finite-pushforward`
- `lem-weil-pbc-curve-assertions-retract`
- `lem-weil-pbc-finite-closed-map-finite-fibres`
- `lem-weil-pbc-finite-composition`
- `lem-weil-pbc-finite-over-separated-finite-type`
- `lem-weil-pbc-finite-permanence-over-separated`
- `lem-weil-pbc-finite-pushforward-constructible-noetherian`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-integral-incomparability`
- `lem-weil-pbc-noetherian-finitely-many-components`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-weil-pbc-reduced-curve-normalization`
- `lem-weil-pbc-zero-dimensional-cohomology`
- `lem-weil-pbc-zero-dimensional-field-extension`
- `lemma-weil-pbc-eight-curve-devissage`
- `lemma-weil-pbc-finite-pushforward-extension-zero`
- `lemma-weil-pbc-smooth-curve-artin-schreier`
- `lemma-weil-pbc-smooth-curve-kummer-localization`
- `thm-pqf-zmt-factorization`
- `thm-sc-main`

No global node or module pruning is claimed. The two helpers publicly import only the assertion
package and open-immersion lower-shriek definitions needed by their signatures; the broad
`Reductions` imports and the transfer helper's `LocallyConstantReduction` import were removed.
The item's reduction and finite-etale imports remain private proof imports.

## Where the brief, the DAG or earlier work was wrong

The returned delivery merely restated the target clauses and created direct dependency cycles.
Those declarations were removed. The repaired helpers are strict geometric parts of the planned
argument, carry self-contained hypotheses, point to the item's proper unit, and document complete
proofs from Stacks 03SG, 0A3Q, 03SD, 0GJ1, 0A5C and 0A5D.

## New nodes

`k1-reduced-constant-lower-shriek-assertions` and
`k1-filtered-finite-cover-lower-shriek-transfer` are substantive reductions. Their `blueprint.from`
records the item's nearest blueprint ancestor and their proof dependencies are independently
established lower results.

## Earlier second reading (a previous round; superseded)

The repaired target proof has no clause restatement: it extracts the dense-open localization
witness and the finite-etale filtration, then applies the two strict geometric helper statements.
The helper hypotheses are self-contained and their nodes depend only on lower declarations; no
cycle remains. The target signature is unchanged and the unit `sk-thm-p1` route is retained.

## Second reading by K1

1. **Visible contract: pass.** Compared every delivered module with the baseline. The only
existing module changes are four private proof imports and the body of
`AlgebraicGeometry.IsCurve.primeCoefficientCurveAssertions`. Its signature and existing
comments/docstring are byte-for-byte unchanged. The helper modules are new; no existing
definition, statement, target, public import or attribute changes. No change record is needed.

2. **Lean proof: pass as a partial reduction.** All three modules compile without errors or
warnings through `lcompile.py --all`, including after narrowing the helper imports. Scratch
copies with `#print axioms` for each of the three declarations show precisely `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The original theorem has no local `sorry`;
the only two delivered `sorry`s are the named helper theorems listed above. It is still
conditional on those and on the existing open localization/finite-etale reductions, so this
is not an axiom-free completion. No axiom, unsafe/opaque declaration, implementation override,
foreign code or definition containing `sorry` occurs.

3. **Split statements: pass.** Read both signatures and their full natural-language proofs,
and verified their mathematical routes against Stacks
[03SG](https://stacks.math.columbia.edu/tag/03SG),
[0A3Q](https://stacks.math.columbia.edu/tag/0A3Q),
[03SD](https://stacks.math.columbia.edu/tag/03SD), and
[0A5C](https://stacks.math.columbia.edu/tag/0A5C).
The constant helper is the strict constant lower-shriek case on reduced curves. The transfer
helper assumes the constant case and a concrete finite-etale filtration plus unit retraction,
and performs only compactification, filtration and retract transfer. Neither renames the item.
Checked empty X/U/V, empty filtration (n=0, whose endpoint and retraction force G=0), identity
covers, zero G, zero-dimensional components, characteristic r and characteristic different
from r. No connectedness or prime-to-r degree is needed once the witnesses are supplied.
A nonzero r-torsion stalk can be p-primary only when p=r; invertible torsion with noninvertible
r forces G=0 and hence its pullback/pushforward to be zero. The smooth and normalization
cases exist as lower declarations, but neither helper's whole statement already exists.
Independent second-reader leanfinder, loogle and Mathlib grep searches used different queries
and found no matching result. LeanSearch was unavailable; its actual failure is recorded.
Library and upstream searches located SmoothCalculations, normalization, dense-open,
finite-pushforward and retract reductions; no short proof closes either helper in a few minutes.

4. **Route and pruning: pass after repair.** The main proof first establishes r-annihilation,
uses the existing dense-open equivalence, extracts the existing finite-etale witnesses, then
applies the two strict geometric steps. All imports are used by signatures or proof.
The old direct dependencies are exhaustively listed under No longer needed and remain below
the helpers. `dag/units/sk-thm-p1.json` and its `realized` fields are preserved; the constant
helper explicitly retains `thm-sc-main` and its smooth curve-calculation route. There is no
claim of global pruning or bypass of a unit step.

5. **DAG/Lean agreement: pass after repair.** The item's three proof steps and four direct
dependencies agree with its Lean proof. New nodes now have self-contained mathematical
statements, exact multiline Lean signatures, accurate source places and proof origins, full
step-by-step dependencies, correct chapter/unit/blueprint ancestry, and actual logged search
queries/results. `proof_deps` is the union of step uses; all referenced IDs exist. Checked the
revised dependency closure for cycles, including statement dependencies. No helper depends on
the item it is used to prove.

**Changes made in this reading:** narrowed both helper imports; repaired the two helper nodes'
statements, verbatim Lean signatures, source/proof records, dependencies and search records;
restored the smooth unit computation dependency; completed the direct-dependency pruning
inventory and clarified that no baseline module is globally pruned. The working main proof
and all three theorem signatures were preserved. The two helper proofs remain open.
