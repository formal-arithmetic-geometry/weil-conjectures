## What changed

Proved `AlgebraicGeometry.Scheme.smooth_strict_local_field_model_coeff` without changing
its signature or public imports. The proof combines two proved geometric helpers:
`exists_smooth_strict_local_field_coeff_data` constructs the coefficient field and
`smooth_strict_local_field_model_coeff_fraction_trdeg` computes the final transcendence degree.
Both helpers are new modules in `Sheaf.AlgebraicGeometry`.

The new `Sheaf.RingTheory.HenselianSeparablyGeneratedResidueSection` proves
`Algebra.exists_section_of_separating_family`. Lift an algebraically independent
family through the residue map, extend polynomial evaluation to its fraction field,
and use the existing `Algebra.map_into_henselian_colimit` theorem on the remaining
separable algebraic extension. The ind-etale presentation comes from the proved
source-library theorem `IndEtale.of_isSeparable`. No primitive-element or
finite-stage lifting argument is duplicated.

The geometric construction checks the K-linearity of the core residue comparison
using the three structural Spec equations. It obtains an essentially finite-type
point residue extension from the stalk map, applies Mathlib's separating-basis
theorem, and uses the general section theorem. The fraction-field calculation
checks the K-linearity of the core function-field embedding, identifies the generic
residue field with the generic stalk, and applies `trdeg_add_eq` twice.

All four delivered modules compile without errors or warnings through the required
`lcompile.py` interface. The final construction and original theorem compiled in
9.2 and 3.6 seconds. No heartbeat or timeout limit is raised. The explicit
`f := g` argument prevents the expensive algebra-map inference that occurred
with the implicit map. The required `deliver3.py --no-push` dry run passes; nothing is pushed.

The existing node's proof and dependencies now follow these arguments. Three new
nodes record the proved helpers. No existing definition, statement, or visibility
changes, and no forced adaptations or change records are needed. The unit
`sk-prop-sf-cbc` and its realized route are unchanged.

The lifting source was checked against
[Stacks Tag 08HR](https://stacks.math.columbia.edu/tag/08HR), which assembles the
unique henselian lifts through a filtered colimit. The degree computation uses
[Tag 030H](https://stacks.math.columbia.edu/tag/030H). The separating-basis API and
its perfect-field hypothesis were read in the pinned Mathlib source.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.smooth_strict_local_field_model_coeff`
(node `lem-sc-smooth-strict-local-field-model-coeff`).

All three new public theorems are proved, as are their private helpers:

- `Algebra.exists_section_of_separating_family`;
- `AlgebraicGeometry.Scheme.exists_smooth_strict_local_field_coeff_data`;
- `AlgebraicGeometry.Scheme.smooth_strict_local_field_model_coeff_fraction_trdeg`.

No new holes and no split-off obligations remain. This is one hole closed and
zero holes added, not a decomposition into new unproved statements. The existing
geometric core and closed-irreducible dimension theorem are reused as stated
and are not counted as holes closed by this delivery. Independent `#print axioms`
checks now show only `propext`, `Classical.choice`, and `Quot.sound` for them and
for all four delivered public theorems: no `sorryAx` remains in these proofs.

Edge cases: the polynomial-localization construction allows an empty separating
family, and the finite-cardinal calculation covers a=0 and a=d. The coefficient
field is the actual intermediate field `separableClosure kappa(y) Omega`, rather
than the arbitrary geometric-point field Omega. No object is defined by choosing
an arbitrary witness from an unproved mere-existence theorem: the section is
constructed by the proved lifting theorem, and the core residue comparison is
used inside the proof to verify reduction of the constructed section.

## No longer needed

Removed these direct proof imports from the item module:

- `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore`;
- `Sheaf.RingTheory.StrictHenselizationTriples`;
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`;
- `Mathlib.FieldTheory.SeparablyGenerated`;
- `Mathlib.RingTheory.AlgebraicIndependent.Defs`;
- `Mathlib.FieldTheory.SeparableClosure`;
- `Mathlib.FieldTheory.Separable`;
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`;
- `Mathlib.FieldTheory.PrimitiveElement`;
- `Sheaf.RingTheory.HenselianLocalRootLifting`;
- `Mathlib.RingTheory.Henselian`;
- `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`;
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`;
- `Mathlib.AlgebraicGeometry.AffineScheme`.

The item now directly imports only its two proved geometric helpers for its proof.
The core and dimension theorem remain needed through those helpers. Other
previous imports remain reachable through the core or the henselian-colimit
lifting dependencies, so no whole project module is claimed pruned from the
item's import closure.

The coefficient-field argument no longer separately uses
`lem-weil-pbc-finite-separable-extension-primitive-element`,
`lem-weil-pbc-henselian-local-root-lifting`,
`lem-weil-pbc-simple-root-uniqueness`, or
`lem-weil-pbc-affine-open-stalk-localization`.
The first three finite-stage tasks are handled by the existing henselian-colimit
API. At the generic point, the stalk is already a field and its residue map is a
bijective field map, so no new affine-stalk localization calculation is needed.
These are route-level removals, not claims that other target branches stop using
those nodes. All original dependencies still needed for the residue-field,
separating-basis, or degree arguments are recorded on the new helper nodes.

For completeness, every old direct `proof_deps` entry is replaced at the item
by the two helper nodes. The following remain used in the helper arguments:
`lem-sc-smooth-strict-local-field-model-core`,
`lem-weil-pbc-finite-type-residue-field-extension-finitely-generated`,
`lem-weil-pbc-algclosed-fg-field-separating-basis`,
`def-weil-pbc-transcendence-basis`,
`def-weil-pbc-relative-separable-closure`,
`def-weil-pbc-separable-algebraic-extension`, `def-pc-separably-closed`,
`lem-sbc-transcendence-degree-tower`, and
`lem-sc-closed-irreducible-dimension-trdeg`.
`def-kun-transcendence-degree` remains a statement dependency.
Besides the four route removals above, the proof no longer separately invokes
`lem-weil-pbc-strict-henselization-triples`, `def-pc-separable-polynomial`, or
`def-pd-separable-closure`: henselianity comes from the upstream instance, and
separability/relative closure are handled by the recorded Mathlib APIs.
These removals concern this argument, not their uses inside other modules.

The second reading also removed the redundant plain import
`Mathlib.RingTheory.AlgebraicIndependent.Transcendental` from each new geometric
helper; `TranscendenceBasis` publicly imports it already.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or changed hypothesis. The planned finite primitive-element
construction is already packaged by `Algebra.map_into_henselian_colimit`; the
upstream strict-henselization instance already supplies henselianity, so the
coefficient step need not derive it again from triples. The relative-separable-
closure argument is Mathlib's transitivity of separable algebraic extensions.

The auxiliary fraction-field statement needs only the K-algebra map j and its
transcendence degree; separable closedness and residue bijectivity play no role
in this calculation, so they are not extra hypotheses of that helper.

## New nodes

`new-lem-sc-henselian-separably-generated-residue-section` records the general
proved coefficient-section theorem. It uses polynomial localization and the
existing ind-etale henselian-colimit theorem, and leaves no obligation.

`new-lem-sc-smooth-strict-local-field-model-coeff-data` records the proved geometric
coefficient-field construction. It uses the existing core, the finite-type
residue-field and separating-basis results, and the preceding proved section
lemma, and leaves no obligation.

`new-lem-sc-smooth-strict-local-field-model-coeff-fraction-trdeg` records the proved
geometric fraction-field calculation, using the existing core and dimension
formula together with Mathlib's tower formula, and leaves no obligation.

## Second reading by F3

1. **Interfaces: pass.** Compared all four delivered modules with the shared
   repository. Only the item already exists; its entire theorem signature is
   byte-for-byte identical, and all six public imports are unchanged. Its diff
   replaces the proof, updates its explanation, and replaces plain proof imports.
   The other three modules and nodes are new. No existing definition, instance,
   visibility, or other module is changed; no change record is needed.

2. **Proofs and trust: pass.** Independently compiled all four modules in import
   order using `lcompile.py --all`, with no errors or warnings. Scanned every
   delivered Lean file: no `sorry`, axiom, unsafe/opaque declaration, foreign
   implementation, or kernel-check bypass. The delivery's axiom probe checks
   all declarations, including private helpers. Explicit `#print axioms` checks in
   `scratchpad/axioms/lean/CheckAxioms.lean` show only `propext`, `Classical.choice`,
   and `Quot.sound` for all four public delivered theorems, the geometric core,
   and the closed-irreducible dimension theorem. No `sorryAx` is present. The
   earlier worker's description of those upstream results as open was stale;
   their current proofs are reused without claiming them as this delivery's work. The field is the explicitly constructed
   `separableClosure k Omega`; the core comparison `e` is obtained inside this
   propositional proof from the core theorem, whose current source now contains
   its geometric construction. No new definition chooses a comparison from an
   unproved existence theorem. The structural function-field map is checked by
   its generic-point equation. The section uses
   the proved henselian lifting API, and polynomial lifts are chosen only from
   the proved surjectivity of reduction. No hollow data construction is added.

3. **New statements: pass.** Read all three helper statements against their node
   records and proof docstrings. They are proved components of the argument,
   with no split-off unproved theorem. For the section theorem, algebraic
   independence makes every nonzero polynomial lift a unit, its rational-function
   evaluation identifies the actual intermediate field, and `lift_separable_field`
   applies `map_into_henselian_colimit` with both base primes zero and the maximal
   ideal kernel checked explicitly. Read the latter's statement and proof and
   [Stacks 08HR](https://stacks.math.columbia.edu/tag/08HR). The argument covers an
   empty family and the identity residue map of a field, in every characteristic.
   For coefficient data, checked K-linearity using `hK`, `he`, `hκ`, and `hΩ`,
   the essentially finite-type stalk/residue chain, the perfect-field separating
   basis, and the transported separability of l/K(t). For fraction degree,
   checked the generic-stalk/residue equivalence, K-linearity of `i`, and both
   scalar towers against [Stacks 030H](https://stacks.math.columbia.edu/tag/030H).
   Finiteness follows before natural subtraction, so a=0 and a=d are covered.
   Independent LeanFinder and grep searches used the phrases "surjective
   homomorphism", "field embedding section", and residue/right-inverse variants.
   Searched project sources too: `CoefficientResidueSection` and the private
   section in `FirstOrderPowerSeriesComparison` require adic completeness and
   do not give this K-linear henselian statement. No duplicate was found.

4. **Route and pruning: pass after cleanup.** The final proof assembles its two
   strictly smaller, proved geometric conclusions; the general section uses the
   existing ind-etale colimit theorem instead of rebuilding primitive-element
   lifting. Read the separating-basis and tower Mathlib source and the recorded
   dependency declarations. The unit `sk-prop-sf-cbc` has empty `realized.statement`
   and `realized.steps`; neither the unit nor its chapter route is changed.
   The source blueprint file named by the nodes is absent from this machine;
   the available node/unit records, Lean dependencies, and Stacks sources were
   checked instead. Removed two redundant `Transcendental` imports from the new
   geometric helpers. Expanded `No longer needed` to account explicitly for all
   17 old direct dependencies, distinguishing helper uses from route removals.
   No whole module is claimed pruned from the targets' closure.

5. **Nodes: pass after correction.** All four `lean.statement` fields occur
   verbatim in the corresponding Lean modules; each `proof_deps` is exactly
   the union of its proof steps' `uses`. The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`. New nodes carry the required provenance,
   source, searches, chapter/unit, blueprint parent, and complete Lean records.
   Their mathematical statements match the checked hypotheses and conclusions.
   Corrected fraction-degree step 3 to `elementary: false`, because it invokes
   the cited tower theorem before the elementary finite-cardinal subtraction.

Changes in this reading: removed two redundant plain imports, supplied the
source lines in the two new geometric module docstrings, corrected one node's
elementary flag, clarified the data-choice explanation, corrected the stale upstream-obligation
note after explicit axiom checks, and made dependency accounting and this independent review explicit. No proof term or statement required repair. The final dry run
and delivery run below recompile the cleaned files with the full axiom probe.
