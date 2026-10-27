## What changed

Reduced `SheafOfModules.OrdinaryLineScalar.ordinary_line_derived_scalar_comparison`
by constructing its ordinary and derived natural isomorphisms separately and
assembling their balanced formulas, representative equation, flat-model preservation,
and evaluation compatibility into the existing `Comparison` record.

`OrdinaryLineScalarBalancedComparison` constructs the ordinary comparison using the
existing sheafified binary scalar tensor isomorphism, transports the prescribed signed
power map on the second factor, and proves naturality and both generator formulas.
`OrdinaryLineScalarFlatDescent` restricts to flat-term K-flat representatives and uses
fully faithful precomposition to descend the conjugated comparison and its inverse.
The main theorem proves scalar extension preserves flat models using the existing
identity-topos K-flat pullback theorem. `OrdinaryLineScalarEvaluation` isolates the
remaining evaluation compatibility step for the already constructed comparison.

Extracted the existing definitions and structures to `OrdinaryLineScalarData`, which
the old module publicly imports. All moved signatures and bodies remain identical;
no coefficient, twist, evaluation or computation map is redefined or newly chosen.
The original theorem signatures, earlier proofs, and public imports are preserved.
See `coord/changes/ordinary-line-scalar-data-extraction.md` for the extraction and users.

The first complete packet and four unchanged direct consumers compiled. A later
main-file check exceeded the 60-second limit. Profiling showed distributed costs
across several independent proofs, with the large tensor/localization definitions
already locally irreducible. The existing proved `exists_presentations` and
`exists_lineData` clauses and their private helpers are now extracted to
`OrdinaryLineScalarPresentations` and `OrdinaryLineScalarLineData`, with the same
signatures, bodies and public re-exports. The remaining tower and identity proofs
reuse the existing proved private pure-tensor bridge through a proof import.
Validation: the required remote compiler accepted all seven final delivery modules
and all four unchanged direct consumers (`CoefficientTwistsDetailed`,
`FlatLineDerivedReduction`, `IntegralSmoothAdjunctionPresentation`,
`TwistedPullbackReductionData`), with no errors or warnings and with its 60-second
Lean limit enforced. The revised main file reported 45.9 seconds; the extracted
line-data and presentation files reported 26.1 and 8.5 seconds. The consumer elapsed
totals include setup/cache waiting, separately from the enforced Lean limit. Their
unchanged temporary copies were removed after verification. No consumer adaptation
is needed, and no profiling options remain.

## Proved and sorry left

Original item: one hole, in
`SheafOfModules.OrdinaryLineScalar.ordinary_line_derived_scalar_comparison`.
The item now has no direct `sorry`; its remaining evaluation argument is split off.
This is a decomposition, not a proof eliminating the original hole transitively.

New proved theorems:

- `SheafOfModules.OrdinaryLineScalar.ordinary_scalar_line_balanced`
  (`lem-pur-ordinary-line-scalar-balanced-comparison`): ordinary naturality and forward
  and inverse balanced formulas.
- `SheafOfModules.OrdinaryLineScalar.ordinary_scalar_line_flat_descent`
  (`lem-pur-ordinary-line-scalar-flat-descent`): natural derived isomorphism and its
  representative square for a fixed ordinary comparison.

One hole added and left:

- `SheafOfModules.OrdinaryLineScalar.ordinary_scalar_line_evaluation`
  (`lem-pur-ordinary-line-scalar-evaluation`): evaluation compatibility for an already
  constructed ordinary and derived comparison. It asserts neither comparison existence,
  the inverse formula, flat-model preservation, nor tower or identity compatibility.

Thus one upper hole is reduced to one strictly smaller hole. All earlier proved
clauses remain proved; two have moved to the prerequisite modules. There are no holes in definitions, instances or private helpers.

## No longer needed

No existing public import was removed and no module is withdrawn or globally pruned.
After extracting the proved prerequisites, removed the main file's proof-only imports
of `Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived` and the `import all`
clauses for `SignedLineScalarTensorTower` and `LineUnboundedDerivedTensor`: their
private proof APIs are used only in the new prerequisite modules. The ordinary public
imports of the latter two remain verbatim.
The parent proof no longer cites `def-pur-sheaf-tensor-product` as a separate proof
step; it remains a statement dependency, and the actual tensor is unchanged.
The main construction no longer needs a separate invocation of
`lem-weil-pbc-site-derived-tensor-descent`, the two-variable tensor localization clause: single-variable fully faithful restriction
to resolving representatives suffices. The published site tensor descent module remains needed by
the existing derived-tensor definitions and remains publicly imported. The parent
node's ordinary construction, descent and evaluation steps now cite the corresponding
three smaller nodes; the earlier line-data route is retained in its extracted prerequisite node, and the
tower and identity proofs remain in the item.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The original module has one remaining hole;
the other theorem clauses were already proved and were preserved. No stated dependency
was unavailable merely because its own proof might contain a hole. Splitting the proof
requires an acyclic home for the already existing comparison data, which motivated the
body-preserving definition extraction.

Edge cases checked mathematically: m=0 uses the coefficient unit and multiplication;
negative m uses the recorded dual, with actual signed evaluation; a zero coefficient
ring satisfies the same balanced formulas; arbitrary nonflat ring maps are covered by
identity-topos K-flat pullback; unbounded complexes introduce no new sign because the
signed line is in degree zero. Arbitrary identity-ring line automorphisms are retained,
with their existing comparison_identity_arbitrary theorem unchanged.

The new descent proof uses the existing resolving-representative whiskering node as
a generic localization tool; this does not bypass any statement or proof step of the
unit sk-prop-an, whose realized route is unchanged.

Searches performed: Lean Finder for derived scalar extension and line tensor, and for
localization on K-flat representatives; Loogle for leftDerivedNatIso; Mathlib grep for
scalar tensor comparisons; local rg over both project roots and the dependency nodes.
The matches supply generic localization APIs and ordinary tensor components, not the
complete signed-line normalized derived comparison.

## New nodes

`def-pur-ordinary-line-scalar-data` records the existing definitions moved unchanged to
`OrdinaryLineScalarData`, including `LineData`, `Comparison`, `UnitData` and their
underlying fixed functors, scalar sections and computation maps. Change record:
`coord/changes/ordinary-line-scalar-data-extraction.md`.

`lem-pur-ordinary-line-scalar-balanced-comparison` records the ordinary balanced tensor
isomorphism and its forward and inverse formulas, without a derived or evaluation claim.

`lem-pur-ordinary-line-scalar-flat-descent` records descent of an already specified
ordinary comparison and its defining flat-representative square, without evaluation.

`lem-pur-ordinary-line-scalar-evaluation` records only evaluation compatibility for an
already constructed comparison. Its source, three proof steps, signed normalization
hypotheses, and complete natural-language proof are in its node and module docstring.

`lem-pur-ordinary-line-scalar-presentations` owns the unchanged, already proved
universal scalar presentation and multiplication-unitor existence clause. Its module
is publicly re-exported by the original module.

`lem-pur-ordinary-line-scalar-line-data` owns the unchanged, already proved signed-line
rank, exact termwise tensor, actual evaluation and flat-model construction clause.
Its three proof steps are the original parent steps 1--3, and its public theorem is
re-exported by the original module. No new hole is introduced by either extraction.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
