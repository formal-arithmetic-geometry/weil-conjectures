## What changed

The signature of `integralMatrix_pivot_cover` is unchanged. Its proof now chooses global
free bases, transports the rational cokernel cover across the induced cokernel
isomorphism, and applies the analytic theorem only to a map between standard finite free
modules. From its coefficient chart it obtains integral row quotients and a monic,
rationally invertible pivot,
and constructs the required smaller-rank block decomposition. The global zero-map case
is handled directly on the singleton identity cover. A proof import of
`Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` supplies total disconnectedness
for the nonarchimedean coefficient field. All maps used in the new
definitions are actual sectionwise or categorical constructions.

Added seven modules. `FiniteBiproductPivot` proves the generic finite biproduct assembly.
`ContinuousRegularFunctions` constructs multipliers, proves the formula for their action
on sections, coefficient injectivity and composition, sectionwise monicity, and the
continuous field inverse. `RegularExtensionComparison` constructs the regular-module
scalar-extension isomorphism and proves its naturality from the adjunction.
`IntegralRegularRationalUnit` proves rational invertibility using compatible integral and
field realizations. `IntegralMatrixEntryProperties` constructs integral quotients and
proves all three pivot properties. `IntegralMatrixAnalyticCover` contains the explicit
matrix-function and coefficient-inclusion definitions and the one remaining analytic
covering theorem. `ContinuousCoefficientRealizations` constructs the canonical Type-0
coefficient realization, proves it is a monoid isomorphism for totally disconnected
coefficients, and proves its naturality under continuous ring maps. The analytic
statement now uses this canonical realization and no longer supplies compatibility data.
Its inputs are a matrix map between standard finite free modules and a rational cokernel
cover; the arbitrary-module basis reduction is proved in the original item. The standard
pullback bases are explicitly constructed by `integralFiniteFreePullbackIso`; the
remaining theorem supplies no existential basis or coefficient realization data.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_pivot_cover` (1 of 1).
Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_analytic_cover`, node
`lem-weil-pbc-integral-matrix-analytic-cover`. This is a decomposition: one upper hole
closed and one strictly smaller analytic hole added; the declaration-hole count is
unchanged.
No other delivered declaration contains `sorry`. Explicit `#print axioms` checks of the
canonical comparison, its monoid and isomorphism instances, the actual standard
pullback bases, the finite pivot theorem,
the regular-extension isomorphism and its naturality, the continuous field inverse,
rational invertibility, and matrix entry properties show only `propext`,
`Classical.choice`, and `Quot.sound`; they do not depend on the analytic covering hole.
All eight delivered Lean modules compile cleanly. The original theorem signature is
identical to the repository version, and all eight node signatures and proof-dependency
unions match the delivered sources.

Proved independently of that remaining theorem:
`AlgebraicGeometry.ProEtale.chartComparison_naturality`,
`CategoryTheory.Limits.finiteBiproduct_pivot`,
`CategoryTheory.Mod.regularExtensionIso_naturality`,
`AlgebraicGeometry.ProEtale.CondensedRing.continuousRegular_field_isIso`,
`AlgebraicGeometry.ProEtale.CondensedRing.integralRegular_rationalUnit_of_nowhereZero`, and
`AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_entry_properties`, together with
their actual constructions and supporting lemmas. Their proofs use the definitions in
`IntegralMatrixAnalyticCover`, not its unproved covering theorem.

The remaining theorem is only for standard finite free modules. It needs the geometric
part: transport standard bases and rational cokernel trivializations to a common cover, prove compatibility of the canonical realizations
with normalized pullback, compute constant pointwise rank by exact geometric evaluation,
and restrict to maximal-norm neighborhoods. Its coefficient functions use the explicit
standard pullback bases. It contains no block decomposition, row
quotients, monomorphism, or rational isomorphism conclusion. The empty scheme, zero
source/target rank, and the zero-matrix branch must be retained.

## No longer needed

Removed direct proof imports `Sheaf.Paper.GeometricFieldProEtaleEvaluation` and
`Sheaf.Paper.IntegralScalarContractive` from the item module. The first remains a planned
dependency of the analytic covering theorem. The second is used transitively for its
proved section-linearity helper by `ContinuousRegularFunctions` and its coefficient
comparison theorem by `ContinuousCoefficientRealizations`. Thus no entire existing
DAG node or module is claimed globally pruned. The construction needs no field matrix
normal form, noetherian hypothesis, finite-dimensionality hypothesis, or kernel-closure
induction below this pivot theorem.

## Where the brief, the DAG or earlier work was wrong

The original five-step mathematical plan is retained, with its algebraic steps now proved.
A global nonzero morphism does not give a pivot on every member: on a disconnected scheme
it can vanish on a component. An exploratory nonzero-only split was discarded; no such
module or node is delivered. The remaining chart theorem keeps the zero alternative on
each component of the cover.

For rational invertibility, an arbitrary integral realization alone does not immediately
supply the coefficient-compatibility calculation. The canonical realization API proves
this compatibility
by adjunction naturality. This makes the scalar-extension proof a proved commuting
square argument rather than leaving a comparison hidden in the inverse construction.
The existing geometric evaluation API is for `SheafOfModules`; the analytic obligation
still has to connect it with the present internal module objects and the Type-0
coefficient realization. Existing universe-u field-matrix modules do not directly close
that bridge.

## New nodes

`lem-weil-pbc-continuous-coefficient-realizations`: proved. The comparison is an actual
adjoint of composition with the profinite test projection. Ring-valued construction and
the monoidal adjunction prove the monoid property; the proved Type-0 realization in
`IntegralScalarContractive` supplies its isomorphism. Hom-equivalence naturality proves
that continuous ring maps commute with this comparison. This closes the integral-to-field
compatibility square used in the original item proof.

`lem-weil-pbc-finite-biproduct-pivot`: proved. Selected indices are split off using
`Fin.succAbove`, and finite and binary biproduct extensionality proves the four blocks.

`lem-weil-pbc-continuous-regular-functions`: proved. Multipliers are explicitly defined
sectionwise; the API proves cancellation and reciprocal inversion without geometric rank
assumptions. It reuses the proved private section-linearity theorem in
`IntegralScalarContractive` through a proof-only `import all`.

`lem-weil-pbc-regular-extension-comparison`: proved. Both directions of the regular-module
isomorphism are constructed; their identities and naturality follow from the adjunction
and evaluation on the unit.

`lem-weil-pbc-integral-regular-rational-unit`: proved from the preceding continuous-function
and scalar-extension APIs, using the compatible field realization produced by the canonical comparison API.

`lem-weil-pbc-integral-matrix-entry-properties`: proved. Norm dominance puts the explicitly
constructed continuous quotients inside O_E, and the coefficient realization equivalence
transports their multiplication maps to the original regular modules.

`lem-weil-pbc-integral-matrix-analytic-cover`: the sole remaining `sorry`. The next proof
must supply the constant-rank and covering/refinement work for standard finite free
matrices described above. The original item already proves the passage from arbitrary
free A and B to this case, including transport of their rational cokernel trivialization.
The standard pullback bases are actual finite-biproduct comparison constructions, not
existence witnesses supplied by the remaining hole.
`ContinuousCoefficientRealizations` now supplies actual Type-0 monoid isomorphisms and
proves the compatibility with coefficient inclusion.
`AlgebraicGeometry.ProEtale.geometric_field_proetale_evaluation_exact` supplies
exact evaluation over an algebraically closed field. One must prove compatibility
with normalized pullback.
An alternative route was investigated in scratch work. The proved private
`freeEpiLocalSplitting` and `ccs_exists_cover_regular_lift` in
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` can replace geometric rank
computation. Locally split the free cokernel quotient q:B→C with section s and put
p=id-q≫s. Factor p through image(a). Since B is finite free, lift its finitely many
basis sections locally through A→image(a). This gives b:B→A with b≫a=p and hence
a≫b≫a=a. The corresponding continuous field matrices satisfy ABA=A. Thus e=BA is
idempotent and A=0 iff e=0. A nonzero idempotent in a normed ring has norm at least one,
so its zero locus is the open set where its norm is less than one. This separates zero
and nonzero pieces; maximal-norm neighborhoods handle the latter. Scratch prototypes of
the local lifting/generalized inverse and idempotent zero-locus arguments compiled.
This route still needs the normalized pullback and coefficient transport API, and matrix
composition compatibility. It is an alternative plan, not part of the delivered proof.
No unused scratch module is delivered. Some LeanSearch requests failed (HTTP 500);
the real failed searches,
LeanFinder/Loogle results, and Mathlib source searches are recorded.

Change record: `coord/changes/C3-integral-matrix-pivot-cover.md`.

## Second reading by C3

1. **Comparison with the repository.** I compared the delivered
`Sheaf.Paper.IntegralMatrixPivotCover` with the repository version. The theorem
signature of `integralMatrix_pivot_cover` is byte-for-byte unchanged; the diff is
confined to proof imports, the proof, and its explanatory comment. The seven added
helper modules and their node files are new delivery content, and no existing
consumer is adapted. **Verdict: pass.**

2. **Compilation and axioms.** I compiled all eight delivered modules with
`lcompile.py --all`; every module compiled successfully. The only remaining `sorry`
is the named theorem `integralMatrix_analytic_cover` in its own module, and it is
listed in the report and node as a strict analytic split. There are no `axiom`,
`unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proved helper
results have kernel axioms restricted to `propext`, `Classical.choice`, and
`Quot.sound`; the pivot theorem necessarily still carries `sorryAx` through the
explicit analytic split. **Verdict: pass.**

3. **Statements and split-off node.** I checked each new node's Lean declaration,
statement text, source, proof description, dependencies, and `lean` record against
the delivered modules. The analytic theorem is strictly smaller than the original
pivot theorem: it concludes only the zero-or-dominating-entry cover for a standard
finite-free matrix and supplies no row division, monicity, rational isomorphism,
or block decomposition. Its docstring gives the source and a complete proof plan,
and its edge cases (empty members and zero ranks) are retained. The other new
interfaces are actual constructions or proved helper theorems, with no data selected
from an indeterminate existence proof. **Verdict: pass.**

4. **Route and pruning.** The proof follows the declared route: reduce to standard
finite-free modules, transport the rational cokernel cover, invoke the analytic chart,
use the proved entry-properties and finite-biproduct pivot results, and assemble the
original witnesses. The finite-biproduct and coefficient-comparison steps required by
the route remain present. Proof-only imports are plain `import` (including the
intentional `import all` reuse), while statement dependencies are `public import`;
the removed direct imports are recorded under `No longer needed`. No shorter proved
library or Mathlib route was found in the recorded searches. **Verdict: pass.**

5. **DAG and unit agreement.** The target node's `proof`, `proof_deps`, and
`proof_origin` match the proof, and the seven helper nodes record their declarations,
strictly smaller split where applicable, sources, and dependency unions. The unit
`sk-thm-properbasechange` route remains intact: this item realizes the algebraic
pivot substep used below the unit, without changing the unit's statement or realized
steps. **Verdict: pass.**

I changed only this report by adding the second-reading record. No Lean source,
statement, definition, node, or change record required repair.
