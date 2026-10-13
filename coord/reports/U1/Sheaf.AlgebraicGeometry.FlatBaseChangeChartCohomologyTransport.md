## What changed
Replaced the chart cohomology hole with a proof from the geometric coefficient chart
transport and existing cohomology h-map functoriality/basic properties. The proof
constructs inverse additive maps, proves scalar compatibility by two naturalities,
and derives the unit formula by composition and the coefficient unit square.
The original signature and docstring are unchanged. Added one module and node for
the geometric coefficient data, independent of any cohomology degree.

## Proved and sorry left
Closed `AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_chart_cohomology_transport`
(node `new-flat-base-change-chart-cohomology-transport`). Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_chart_coefficient_transport`
(node `new-flat-base-change-chart-coefficient-transport`). This is a decomposition,
not a net hole reduction: the geometric part remains, while the entire passage from
module identities to the cohomology equivalence and its equations is proved.
No other holes are left in the item's module or added by this delivery.

## No longer needed
No existing imports or modules are pruned globally. The original geometric dependencies
are now needed by the coefficient node, and the functoriality dependencies by the original
node. The original node no longer directly needs def-pc-fibre-product,
def-pc-module-pullback, def-pc-tensor-pullback-composition-iso,
lem-weil-pbc-open-immersion-module-pullback-restriction,
def-weil-pbc-flat-base-change-open-choices or def-pc-flat-cohomology-comparison as
proof dependencies; their geometric work belongs to the new coefficient node.
Both original public imports still support the unchanged statement.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt did not implement the passage from coefficient chart data to
cohomology. This passage uses existing proved functoriality and basic properties;
it does not require a new cohomology comparison theorem. A scalar-compatible
additive equivalence alone would not determine the unit formula, so no such
arbitrary-equivalence compatibility claim is introduced. The new node supplies
specific inverse h-maps and a coefficient unit square before cohomology instead.
Empty opens, zero coefficients and degree zero are covered by the same identities.

## New nodes
`new-flat-base-change-chart-coefficient-transport`: the affine scheme chart with inverse
coefficient h-maps, inverse identities, scalar square and coefficient unit square.
This is strictly below the original claim: no degree or cohomology functor occurs.
It follows the original geometric route without changing the unit realization.
No definition or existing interface changes, and no forced adaptations.

Change record: `coord/changes/flat-base-change-chart-local-proof-attributes.md`.
The added attributes are local; the preflight requests a record conservatively.

## Second reading by U1

1. **Existing interface: pass.** Read the repository/sandbox diff of
   `FlatBaseChangeChartCohomologyTransport.lean` and independently compared its
   entire theorem signature up to `:=` byte for byte. It is unchanged, as is its
   docstring. There are no changed definitions or other existing declarations.
   The added helpers are private and proved; all added attributes are local.
   Read the local-attribute change record: it documents no semantic interface change.

2. **Lean proof and axioms: pass as a decomposition.** Compiled both modules in
   import order with `lcompile.py --all`: no errors or warnings (3.5 s and 30.1 s).
   A scratch copy with `#print axioms` for both public theorems and all three
   private helpers compiled cleanly. Helpers use only `propext`, `Classical.choice`
   and `Quot.sound`; public theorems additionally use `sorryAx`, from the declared
   open coefficient theorem. Exactly one literal `sorry` remains, in
   `exists_flatBaseChange_chart_coefficient_transport`; there is no definition,
   arbitrary-witness construction, axiom or forbidden implementation escape.
   The geometric witnesses are eliminated inside a proposition proof, and the
   resulting additive equivalence is returned existentially, never defined publicly
   from an undetermined existence witness.

3. **Split statement: pass.** Read Stacks 02KH (affine-local reduction), 0096
   (module pullback adjunction), 0097 (composition), and 01FB (cohomology h-maps).
   Matched every hypothesis and coefficient clause of the new node to its Lean:
   arbitrary f and g, affine V and W, inclusion eVW, the specified algebraMap,
   and D.unit_square suffice. In the restricted cartesian square, the affine
   isomorphisms identify L with T. Pullback composition, the adjunction-compatible
   tensor/ordinary comparison and restriction comparison identify sigma^* A with M.
   Transposing this isomorphism and its inverse gives phi and psi and their inverse
   identities. The projection to Spec Gamma(W) agrees with k, giving the scalar
   square. Transposing the final coefficient equation reduces it to D.unit_square
   after restriction to L; c has exactly the orientation in cohomologyOpenRestriction.
   No flatness, quasi-coherence or qcqs assumption is used for these identifications.
   Checked small cases: empty V forces empty W; empty W makes L and T empty;
   zero coefficients give zero maps with the same identities; identity charts give
   the adjunction identity maps. The upper argument works verbatim at p = 0.
   The new claim has no cohomology degree or derived functor and is strictly the
   geometric part, rather than a renamed cohomology claim. Its sourced docstring
   and node provide the remaining argument. A complete formal proof of that geometry
   is not a few-minute repair and remains explicitly open.
   Ran fresh leanfinder, loogle and grep searches with coefficient/cartesian-square
   wording; recorded them on the new node. Read pullbackComp and its conjugate mate,
   toSpecGamma/appLE compatibility and adjoint-uniqueness unit identities in Mathlib.
   Searched lean/ and the upstream AlgebraicGeometry sources. The existing
   ModuleSectionsPullbackIsoTransport concerns global sections, not these coefficient
   inverse and unit equations. No duplicate of the split statement was found.

4. **Route and pruning: pass.** Read from the target down: chart_fmap_congr is
   substitution plus the identity comparison; chart_fmap_identity uses the existing
   identity property; chart_fmap_inverse uses existing composition. The final proof
   constructs inverse cohomology maps, uses source/target naturality for scalars,
   and applies composition and source naturality to hunit before unfolding the
   specified open restriction. No cohomology comparison hole is hidden in a helper.
   Each of the three new imports is proof-only and needed by that argument; both
   original public imports supply symbols in the unchanged signature. The new
   module's two public imports supply its signature. The report lists all six old
   proof dependencies moved to the coefficient node, and correctly claims no global
   module pruning. Read sk-thm-p1.json and its realized statement/steps: the auxiliary
   affine-chart reduction changes no realized unit node or chapter route.

5. **DAG/Lean agreement: pass.** Compared the existing node diff: only proof,
   proof_deps and proof_origin change. The coefficient node carries the required
   source, searches, creation, blueprint ancestry, chapter/unit and verbatim Lean
   signature. Its geometric dependency list equals the union of its steps' uses.
   The original node's new dependency list describes coefficient transport,
   h-map functoriality, basic identity properties and the definition of open
   restriction (it does not invoke the resolution-section theorem unnecessarily).
   The source and target naturalities and the composition statements really give
   the morphism equations used in the proof; inverse equations have the correct
   pushforward-composition orientations.

**Second-reading changes:** added the independent search evidence to the coefficient
node and this detailed review. No Lean proof, signature, definition, import or hole
was changed; the delivered result remains one hole closed and one strictly lower
hole added, with net hole reduction zero.
