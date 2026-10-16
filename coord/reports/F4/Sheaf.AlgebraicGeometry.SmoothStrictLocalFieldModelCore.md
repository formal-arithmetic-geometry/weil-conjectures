## What changed

Proved `AlgebraicGeometry.Scheme.smooth_strict_local_field_model_core` in
`Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore`, with its original signature,
public imports and visibility unchanged. Added a fully proved private chart-presentation
helper that retains the actual geometric prime and the structural-map equations.
Its argument follows the existing private chart proof in
`Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation` and applies
`etale_local_ring_triples` and the localized-triples theorem.

Used the existing residue clause `strictHenselizationResidue`, smooth-stalk regularity,
strict-henselization regularity and dimension, and the finite-type point dimension formula.
Constructed the function-field embedding by the fraction-ring universal property after
faithful-flatness injectivity. Applied the already proved ind-etale separability API to
images of elements of the strict local ring; products and inverses of integral elements
then establish algebraicity for every fraction.

Updated the existing core node's proof, proof dependencies and proof origin to this route.
No other module, definition, signature or target statement was changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.smooth_strict_local_field_model_core`
(node `lem-sc-smooth-strict-local-field-model-core`).

Holes closed: 1. Holes added: 0. Remaining holes in the delivered module: none.
The private theorem `AlgebraicGeometry.Scheme.smooth_chart_local_presentation` is also
fully proved. No split-off modules or new nodes were introduced.

Single-file compilation passed. The final required dry run checks the delivered proof
and its axiom probe against the published build.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.CategoryTheory.Filtered.Final`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
- `Mathlib.RingTheory.Unramified.LocalRing`
- `Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `Sheaf.RingTheory.SmoothOverFieldRegularLocal`
- `Sheaf.RingTheory.StrictHenselizationTriples`

Removed these direct dependencies from the core node:

- `def-weil-finite-type-morphism`
- `def-weil-pbc-relative-separable-closure`
- `lem-weil-pbc-colimit-initial-full-subcategory`
- `lem-weil-pbc-etale-algebra-residue-field-separable`
- `lem-weil-pbc-etale-chart-residue-triples-equivalence`
- `lem-weil-pbc-smooth-over-field-regular-local`
- `lem-weil-pbc-strict-henselization-triples`

The smooth-over-field regular-local obligation is bypassed by the proved source-library
`Smooth.isRegularLocalRing_stalk`. The direct chart equivalence, cofinal restriction,
residue-separability and triples-existence obligations are encapsulated by the existing
`etale_local_ring_triples`, residue theorem and localized-triples API. Some remain
transitive dependencies of those existing modules; this report claims only their removal
as separate obligations/imports of this proof, not global unreachability. The definitions
of finite type and relative separable closure remain in the unchanged statement context;
they are not separate proof steps. `IndPrincipalZariski` is not used.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically usable, but its generic smooth-over-field
regular-local step was unnecessary: the already proved smooth-stalk theorem applies
directly. Its last step also has an existing proved source-library implementation,
`Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing`; no new residue-field construction
or common-stage lemma is needed. The public `strictHenselization_local_presentation`
theorem is specialized to an affine ambient scheme, so its private general chart argument
was reused locally with the prime retained instead of weakening or changing any interface.

The given `hK` compatibility is not needed by this intrinsic ring/function-field proof;
it stays in the signature unchanged. The geometric point guarantees a nonempty affine
chart, regularity gives a genuine domain, and the finite dimension equation handles
a=d and d=0 without extra assumptions. No statement was disputed.

## Second reading by F4

1. **Existing interfaces: pass.** Compared the entire delivered module and node with
   their read-only repository versions. The existing theorem's signature is byte for
   byte identical, and its visibility and all public imports are unchanged. The only
   additional declaration is a private, fully proved theorem. There are no changed
   definitions, new instances, target changes or adaptations of another module.

2. **Proof and axioms: pass.** Read the complete chart helper and main proof, and
   compiled the delivered file cleanly with `lcompile.py`. Compiled a scratch copy
   of the actual delivered source with `#print axioms` for both
   `smooth_chart_local_presentation` and `smooth_strict_local_field_model_core`:
   each reports exactly `propext`, `Classical.choice`, and `Quot.sound`, without
   `sorryAx`. The module contains none of `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern` or `debug.skipKernelTC`. It introduces no definition
   or data chosen from an unproved existence statement. In particular R is the
   already constructed geometric strict henselization, and Q is `FractionRing R`;
   the chosen presentations supply properties and compatible maps of these rings.

3. **New statements and small cases: pass.** No statement is split off and no hole
   is added. The private helper is strictly the affine-chart comparison needed to
   retain the actual prime and the structural map. Read its existing analogue in
   `StrictHenselizationLocalPresentation` and the statements of
   `etale_local_ring_triples` and
   `etaleResidueTriples_localized_isStrictHenselization`. The existing public
   presentation is affine-only and existential in the prime, so it does not supply
   this helper's point identification. A fresh LeanFinder search with different
   wording and searches of both project roots found the existing fraction-field
   API already used here, but no complete replacement for the theorem. Checked
   the dimension argument when d=0 and when a=d: writing the regular stalk's
   dimension as its maximal-ideal spanFinrank makes d=n+a an equality in natural
   numbers before subtraction, so these cases need no positivity assumption.
   The chart is nonempty because it contains y, including at the generic point.
   For algebraicity, the ind-etale theorem is applied to a field Q, hence a local
   ring, with the scalar tower proved from the fraction-field lift equation;
   integrality under inverse is valid over the field Y.functionField, including
   inverse zero. No injectivity of an individual etale-stage map is assumed.

4. **Top-down route, imports and pruning: pass.** Read the proof from its required
   residue, regularity, dimension and fraction-field conclusions down to the
   imported APIs. The helper compares actual cocone legs and then verifies the
   structural equation; regularity is transported across the affine stalk
   localization; faithful flatness proves injection before the fraction-field
   lift is used. The final quotient argument uses the existing proved
   `Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing`, not a new common-stage
   obligation. All added imports serve proofs and are plain imports. The list
   above contains all eleven removed direct imports and all seven removed old
   direct proof-dependency edges. It makes no unsupported claim of global module
   pruning: some removed direct dependencies remain transitive. Read
   `dag/units/sk-prop-sf-cbc.json`; its statement, steps and `realized` record are
   untouched, and the local-calculation route through this core is retained.

5. **DAG agreement: pass.** The sole node changes exactly `proof`, `proof_deps` and
   `proof_origin`. Its unchanged recorded Lean signature matches the theorem,
   and its dependencies equal the union of the proof steps' `uses`. Checked the
   cited Lean records and the relevant residue, affine-triples, localization,
   regularity, dimension and faithfully-flat statements against their applications.
   The functoriality citation uses its existing residue clause, and the mixed
   ind-etale definition record includes the reused `Algebra.IndEtale` declaration.
   No new node or change record is required.

Changes made in this second reading: added this missing independent audit section
and recorded the direct scratch-copy axiom verification. The Lean proof and DAG
metadata required no repair. One original hole is closed and zero holes are added;
this is a proof, not a decomposition.
