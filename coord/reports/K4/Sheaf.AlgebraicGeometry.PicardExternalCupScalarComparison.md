## What changed

Reduced `AlgebraicGeometry.Scheme.picard_external_cup_scalar_comparison`, without changing
its signature, to comparison for cup products with the explicit degree-zero class of 1.
The main proof constructs normalized scalar coordinates, expresses every degree-zero
class as a scalar multiple of 1, moves that scalar between the arguments of the external
cup product, and applies the common unit comparison in each order.

Added three modules, with one statement node each:

- `Sheaf.AlgebraicGeometry.ScalarUnitCohomologyCoordinates`: constructs the class of 1
  using `toRightDerivedZero`, and proves the existence of normalized linear coordinates
  using `rightDerivedZeroIsoSelf`, restricted scalars, and the bijective structure map.
- `Sheaf.AlgebraicGeometry.ExternalCupScalarBalance`: proves scalar balance for arbitrary
  module coefficients and all degrees from the recorded cohomology-to-Ext scalar law,
  linearity of inverse image and tensor functors, and the Ext composition identities.
  All private helpers are proved. Abstract Ext calculations avoid repeated kernel
  reduction of the large concrete sheaf categories; the complete file compiles within
  the single-file limit.
- `Sheaf.AlgebraicGeometry.PicardExternalCupUnitComparison`: states the remaining
  common comparison for the two cup products with the explicit class of 1. It needs
  no bijectivity hypothesis on structure ring maps and asserts no scalar coordinates
  or formulas for arbitrary degree-zero classes.

The unit class is an explicit construction, not a witness chosen from an unproved
existence theorem. The equivalences used in the final proof are obtained locally from
existence theorems; no definition stores an arbitrary witness.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_external_cup_scalar_comparison`
(node `lem-sc-picard-external-cup-scalar-comparison`) by a complete Lean reduction.
This is a decomposition, not a proof without admitted dependencies: one original hole
is closed and one new hole is added (net zero).

Also proved, with no new holes in their modules:

- `AlgebraicGeometry.Scheme.Modules.scalar_unit_cohomology_coordinates`
  (node `lem-sc-scalar-unit-cohomology-coordinates`).
- `AlgebraicGeometry.Scheme.Modules.external_cup_scalar_balance`
  (node `lem-sc-external-cup-scalar-balance`).

The only sorry left in this delivery is
`AlgebraicGeometry.Scheme.picard_external_cup_unit_comparison`
(node `lem-sc-picard-external-cup-unit-comparison`). Its whole proof is `by sorry`;
its docstring and node give the resolution, coefficient-unit, and functoriality argument.
Existing admitted declarations in imported modules are unchanged.

## No longer needed

Second reading removed redundant private imports of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` from the coordinate module and
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` from the balance module.
Both are already available through the public import closure of
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`; their declarations
remain used by the proofs, and no closure pruning is claimed for these removals.

Removed the item's direct proof import of
`Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`. That module and its node
`lem-sc-module-abelian-zariski-cohomology` remain needed by the unit comparison;
this removal does not prune them from the target closure.

The original direct proof dependencies `def-pc-module-pullback`,
`def-sc-field-linear-module-cohomology-operations`,
`def-sc-structure-sheaf-cohomology-pullback`, and
`def-sc-module-cohomology-cup-product` are now used through the new intermediate nodes.
Their modules remain in the needed closure.

The general tensor-pullback comparison
`lem-weil-pbc-module-pullback-tensor` is not used by this comparison route.
The unit-coefficient argument instead uses the already proved, normalized structure-sheaf
comparison `lem-weil-pbc-module-pullback-structure-sheaf`, followed by the tensor unitor.
However `Sheaf.AlgebraicGeometry.ModulePullbackTensor` remains publicly imported by the
unchanged field-linear operations module, so no removal from the whole target import
closure is claimed. No module is claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan's comparison step needs more than coefficient naturality alone.
`zariskiModuleAbelianCohomologyNatural` gives naturality in module morphisms; its
signature does not identify the scheme pullbacks or cup products, or normalize degree
zero. The remaining unit-comparison node makes that missing compatibility explicit.
The degree-zero coordinate step and scalar balance are now actual Lean proofs.

The original plan cited the general tensor-pullback comparison for the unit coefficients.
The more precise existing `tensorPullbackObjUnitToUnit_isIso` gives both the unit
isomorphism and its adjunction-unit characterization, which are the facts needed here.
No target, definition, or existing statement is changed.

The repository's cited Stacks TeX files are not present on this machine. Read the official
pages for [0BED](https://stacks.math.columbia.edu/tag/0BED),
[03FD](https://stacks.math.columbia.edu/tag/03FD), and
[01F7](https://stacks.math.columbia.edu/tag/01F7).
The unit-comparison proof concerns the construction of the external cup maps, not the
Kunneth isomorphism, so it does not import the latter's compactness or diagonal hypotheses.

Searches through the supplied msearch tool found no matching comparison. LeanSearch was
unavailable (HTTP internal server error), recorded as unavailable. LeanFinder, Loogle,
Mathlib grep, local library search, and blueprint searches were run. Blueprint searches
for external cup and zeroth derived found no matching imported blueprint statement.

Edge cases: the coordinate theorem's bijectivity hypothesis excludes an empty scheme
with zero section ring over a field. The unit comparison and balance impose no such
hypothesis: the empty scheme has the zero unit class and zero cohomology, so the formulas
remain valid. The balance proof works for scalar zero, either degree zero, zero modules,
and arbitrary characteristic. Both unit identities use one common product comparison;
there is no cohomological sign when one degree is zero. The unit record
`sk-prop-av-cube` and its route are unchanged.

## New nodes

`lem-sc-scalar-unit-cohomology-coordinates`, in
`dag/nodes/sec-abelian-varieties/lem-sc-scalar-unit-cohomology-coordinates.json`, records
the explicit class of 1 and the proved normalized coordinate theorem. This is the
original plan's degree-zero step, without any assertion about products or comparisons.

`lem-sc-external-cup-scalar-balance`, in
`dag/nodes/sec-abelian-varieties/lem-sc-external-cup-scalar-balance.json`, records the proved
balance law for arbitrary coefficients and degrees. It asserts no additive comparison
or coordinate equivalence.

`lem-sc-picard-external-cup-unit-comparison`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-external-cup-unit-comparison.json`, records
the remaining common comparison only for the fixed classes of 1. It is a strict part
of the original argument; the final theorem needs the two independently proved facts
and explicit Lean rewriting to extend these identities to arbitrary degree-zero classes.

No change records or forced adaptations are needed.

## Second reading by K4

Independent second reader, not the author of these proofs. Verdict: passes as a
net-zero decomposition, with two proved intermediate statements and one remaining
unit-comparison hole; no unconditional proof of the original comparison is claimed.

1. Compared the delivered modules with the repository. The three helper modules are
   new. The original theorem's signature is byte-for-byte identical, including both
   bijectivity assumptions, all five equivalences, both quantified formulas, the
   degrees and projection choices. Its docstring and public imports are unchanged.
   The existing node differs only in `proof`, `proof_deps`, and `proof_origin`.
   No definition or statement used by an existing target changes; no change record
   or forced adaptation is required. Verdict: pass.

2. Read the complete four Lean files and compiled them in import order, again after
   the import repairs below: all compile without warnings or errors, within the
   single-file limit. The only delivered `sorry` is the whole named theorem
   `AlgebraicGeometry.Scheme.picard_external_cup_unit_comparison`. There is no hollow
   definition, forbidden axiom, unsafe declaration, opaque declaration, extern or
   implementation override. Scratch copies with `#print axioms` showed only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the three proved
   theorem bodies and remaining admitted theorem, as expected from their open
   imported dependencies. `scalarUnitCohomologyClass` itself uses only the three
   permitted axioms. It explicitly applies `toRightDerivedZero` to the section 1;
   the local existential equivalences are eliminated inside proofs, never stored
   as arbitrary data in definitions. Verdict: pass, conditional on recorded holes.

3. Read the statements, docstrings and nodes of all three new results against
   the actual definitions of `scalarCohomology`, `scalarCohomologyExtEquiv`,
   `scalarCohomologyPullback`, `scalarExtCup`, `scalarTensorCoefficient`, and
   `structureSheafCohomologyPullback`. Read the official Stacks pages
   [01DZ](https://stacks.math.columbia.edu/tag/01DZ),
   [03FD](https://stacks.math.columbia.edu/tag/03FD),
   [01F7](https://stacks.math.columbia.edu/tag/01F7), and the cup-map construction in
   [0BED](https://stacks.math.columbia.edu/tag/0BED). The latter's hypotheses for the
   Kunneth isomorphism are not used for the unit identities: the identities follow
   from the common resolution comparison and multiplication by the cocycle 1.
   In the coordinate proof, left exactness gives `rightDerivedZeroIsoSelf`, whose
   inverse is exactly `toRightDerivedZero`; the restricted structure map is the
   linear equivalence and its image of 1 is 1. In the balance proof, exact-functor
   transport and Yoneda composition commute with scalars, and linearity of inverse
   image comes from its sectionwise linear right adjoint. No bijectivity assumption
   is needed for balance or unit comparison. The unit-comparison hole asserts only
   the two fixed unit inputs, with one common product equivalence; it omits the
   scalar coordinates and all formulas for arbitrary degree-zero inputs. It is
   strictly part of the argument, not a renamed copy of the item. Its resolution
   proof in words explains the coefficient identification, normalization at 1,
   and compatibility of the two cohomology pullbacks. Checked empty schemes,
   scalar zero, degree zero in either factor, zero coefficients, arbitrary
   characteristic, affine schemes with non-bijective structure maps, and the
   absence of a sign when one degree is zero. No extra finiteness hypothesis is
   required for these identities. Second-reader searches used LeanFinder for
   Yoneda cup with degree-zero identity, Loogle for `rightDerivedZeroIsoSelf`,
   Mathlib grep for scalar composition laws, and `rg` on both the library and
   slopmaster2 for cup-unit and zeroth-derived comparisons. They found the generic
   Ext/resolution and zeroth-derived tools already used, but no theorem closing
   the unit comparison or replacing the normalization/balance combination.
   Verdict: the statements are true and needed; the remaining comparison is not
   closable by a short application of an existing searched theorem.

4. Read the final proof from the top downward. `dY.symm_apply_apply` and its
   normalized inverse formula give `b = dY b` times the unit class; balance moves
   this scalar to `a`, and the first unit identity applies. The second formula
   uses the same argument with balance reversed. No linearity of the merely
   additive `eX`, `eY`, or `eP` is assumed. The coordinate and balance proofs use
   the existing Mathlib/upstream tools rather than duplicate admitted helpers.
   Public imports provide the symbols in each signature. The remaining private
   imports in the unit-comparison module provide its recorded unfinished proof
   route. Removed the two redundant private imports listed under No longer
   needed, and recompiled successfully. All six old direct proof dependencies
   are accounted for there: the general tensor-pullback lemma is bypassed by the
   more precise unit-pullback lemma, while the others remain used through the
   intermediate results. No global module pruning is claimed. Read
   `dag/units/sk-prop-av-cube.json`: its statement, steps and `realized` fields
   remain unchanged; this reduction stays within the scalar-comparison step
   below the cube unit. Verdict: pass.

5. Matched each node's recorded Lean statement with its declaration, source,
   chapter and unit; all new nodes have creation, blueprint, searches, Lean,
   statement-dependency and proof-origin records. The original node's three
   proof dependencies are exactly the three results used by its new proof.
   The coordinate node records the derived-zero isomorphism and linear inverse;
   the balance node records the exact-functor and tensor Ext scalar calculations;
   the unit-comparison node records the remaining resolution and coefficient
   compatibility argument. Each `proof_deps` is the union of the steps' `uses`,
   and the original statement and statement dependencies are unchanged.
   The unit record is not edited. Verdict: pass.

Second reading changed only two redundant private imports and this report (including
its No longer needed list). No proof body, statement, definition or node was changed.
