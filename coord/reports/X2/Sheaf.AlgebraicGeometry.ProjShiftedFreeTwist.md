## What changed

The signature and public imports of `Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist`
are unchanged. Its sole theorem now has a complete proof from named component
statements. The proof constructs the two-variable cover, applies the local chart
criterion for scheme isomorphisms, constructs the chart-compatible `C` with
`asIso` and `awayι_linearProjection`, chooses the glued module through the existing
`ProjectiveLine.exists_twistData_unique_iso`, and supplies the two conjuncts.

Three new modules separate the geometric chart calculation, comparison with a
prescribed glued twist, and finite-sum fraction charts. The chart calculation is
proved completely from the source library and Mathlib: after the existing
linear-chart coordinate computation, `homogeneousLocalizationAwayXEquiv`, variable
reindexing and `AffineSpace.SpecIso` identify the map with a spectrum isomorphism.
The finite-sum statement is generalized to any graded commutative ring; it has no
projective-line chart or glued-twist existence conclusion.

Local compilation of all four modules succeeds with no warnings. The chart proof
uses a local heartbeat allowance for dependent coercion elaboration; its single-file
compile stays below the 60-second limit. Final validation is the required
`deliver3.py X2 Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist --no-push` dry run.

## Proved and sorry left

Proved in the assigned module:
`AlgebraicGeometry.Proj.proj_shifted_free_is_twist`
(node `lem-sc-p1-proj-shifted-free-twist`). This removes its sole original `sorry`
by a reduction; it is not asserted to be independent of all remaining sorries.

Also proved:
`AlgebraicGeometry.Proj.isIso_polynomial_linearProjection_restrict`
(node `lem-sc-p1-polynomial-projection-chart-iso`).

The two sorries added by this delivery, each in its own module, are:

- `AlgebraicGeometry.Proj.nonempty_twist_iso_tensorPullback_of_twistData`
  in `Sheaf.AlgebraicGeometry.ProjTwistGluedComparison`, node
  `lem-sc-p1-proj-twist-glued-comparison`.
- `AlgebraicGeometry.Proj.finite_twist_coproduct_fractions`
  in `Sheaf.AlgebraicGeometry.ProjFiniteTwistCoproductFractions`, node
  `lem-sc-proj-finite-twist-coproduct-fractions`.

The existing, imported
`AlgebraicGeometry.ProjectiveLine.exists_twistData_unique_iso`
(node `lem-sc-p1-twist-exists`) remains unproved in its existing module; this delivery
does not modify it. The other inherited obligations in tensor-formula pullback also
remain in the existing library.

The new statements have been checked mathematically at d=0, d=1, d=-1, r=0,
zero homogeneous f, and nilpotent f. The comparison fixes C and an arbitrary supplied
TwistData rather than asserting existence; negative generator powers are only taken
where the variable is invertible. The empty finite coproduct has zero sections and
its fraction image is the zero localization module, represented with denominator 1.

## No longer needed

None of the original imports or proof dependencies is pruned. All five original
public imports are needed by the unchanged statement. The original proof-only import
of `Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists` is used explicitly. The parent
DAG now records the three component nodes used by the proof and the existing
existence node; its former definition dependencies are still used through the new
component statements and their proofs. No unit statement or unit proof step is
bypassed. The second reader removed the redundant public Mathlib IsIso import from the new chart
module and imports it privately in the parent for the local isomorphism criterion.

The parent does not use the invertibility and uniqueness conclusions of
`exists_twistData_unique_iso`; it only uses the module and its generators. This
observation does not prune that module or its node, since its existence conclusion
is still used.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no signature or definition was changed.
The original plan implicitly assumed an inhabitant of `ProjChartIsomorphism`;
its recorded module only defines the structure. The delivery fills that gap by
proving the canonical linear projection is an isomorphism chartwise and then
using the target-local criterion to construct C.

The finite-sum step was marked elementary in the old DAG, but the recorded concrete
`Proj.twist` sheaves still need the basic-open localization comparison and its
restriction compatibility before the elementary componentwise calculation can be
used. This is stated explicitly in the general finite-sum node. The chart and
comparison steps also did not have declarations supplying their conclusions.

The Stacks sources are available online, while the local literature checkout on this
machine contains only the tracked index files. Sources consulted:
[01NG](https://stacks.math.columbia.edu/tag/01NG),
[01M6](https://stacks.math.columbia.edu/tag/01M6),
[01M7](https://stacks.math.columbia.edu/tag/01M7), and
[01MN](https://stacks.math.columbia.edu/tag/01MN).
LeanSearch returned HTTP 500; LeanFinder, Loogle and source grep searches were run
through `msearch.py` and are recorded in `searches.jsonl`. They found no theorem
closing the two outstanding component statements.

## New nodes

`lem-sc-p1-polynomial-projection-chart-iso` records the completely proved canonical
linear projection chart isomorphism. Its source is Stacks 01NG, with the chart map
calculation adapted from the already proved source-library
`isFinite_linearProjection_restrict`. It supplies a local isomorphism, not an
inhabitant of the parent's whole existential conclusion.

`lem-sc-p1-proj-twist-glued-comparison` fixes a chart-compatible C, a module L and
specified generators T, and asserts the resulting twist comparison. Its proof is
local trivialization, equality of transition functions, and gluing inverse maps.
It neither constructs C nor chooses L and has no finite-sum clause.

`lem-sc-proj-finite-twist-coproduct-fractions` gives the basic-open fraction maps for
a finite coproduct of twists of an arbitrary graded commutative ring. Its proof
records common-denominator alignment, the exact shifted-degree range, scalar
compatibility, and the numerator/denominator formula for canonical restrictions.
It does not assert any comparison with a projective line or a glued twist.

No change record is needed: only proofs, proof-only imports and new theorem modules
are changed, and the parent node edits are restricted to proof-route fields.


## Second reading by X2

1. Interface: PASS. Diffed every delivered module against the repository. The only
existing module is ProjShiftedFreeTwist; its theorem signature, original docstring,
and five public imports are byte-for-byte unchanged. Its only original declaration
changes in its proof body. The three component modules are new, and introduce no
changed definition or statement of an existing declaration. No change record is
required.

2. Proof and axioms: PASS. Compiled all four modules in dependency order through
lcompile.py, without errors or warnings. Explicit #print axioms checks in a scratch
copy give exactly propext, Classical.choice and Quot.sound for the chart theorem;
the parent and the two reported open components additionally use sorryAx. Inspected
all bodies: the only two delivered sorries are whole proofs of the named public
component theorems. There are no hollow definitions or prohibited declarations.
The parent constructs the actual chart-compatible C, chooses L,T from the existing
existence theorem, and separately supplies the comparison and finite-sum conjuncts.

3. Split statements: PASS. Read both signatures, docstring arguments, and matching
nodes, checking the conventions against TwistData, degreeZeroFractions, the concrete
Proj.twist construction, and Stacks 01M7, 01MN and 01NG. The supplied TwistData
trivializes on every subopen and has exactly the required transition. At d=0 the
relation is identity; at d=1 it is x₀=t⁻¹x₁, and at d=-1 it is x₀⁻¹=t x₁⁻¹.
The finite fraction lemma has the correct aᵢ+m*b numerator degrees. For r=0 the
section and localization modules are zero; f=0 or nilpotent gives an empty basic
open and zero localization. A common denominator aligns the finitely many numerator
degrees; equality witnesses can also be made common. The restriction formula follows
from g^(e*m)=h^m*f^m and is valid for arbitrary fraction representatives. Each open
component is strictly part of the original conjunction, not a restatement of the
whole target. New independent LeanFinder searches used fraction-section and local
free-generator terminology, with Loogle and grep searches also recorded in
searches.jsonl. Source rg found twistPowSection/isFreeGenerator_twistPowSection
and nonempty_restrict_twist_iso_unit: these supply local triviality, but neither
comparison with tensorPullback nor the finite fraction charts. No duplicate closing
theorem was found, and neither remaining obligation is a few-minute closure.

4. Route and pruning: PASS after import repair. The proved chart calculation uses
the existing homogeneousLocalizationAwayXEquiv and canonical chart formulas;
there is no shorter complete comparison or fraction theorem in the searched library.
Read sk-thm-picard-duality.json: the item is below the unit level, and the realized
unit fields are untouched. All three original proof dependencies remain used as
definitions or the explicit twist existence theorem; none is pruned. The new chart
module's public Mathlib.AlgebraicGeometry.Morphisms.IsIso import was redundant:
a scratch compile succeeds with it removed. Removed it there and added a plain
import to the parent, where the proof uses the local isomorphism criterion.

5. Nodes: PASS. The parent proof steps and proof_deps follow the explicit Lean
reduction. Compared its JSON with the repository: only proof, proof_deps and
proof_origin changed. Each new node has its complete statement, source, proof steps
with dependency union, proof_origin, three search kinds, status, created record,
blueprint ancestry, chapter/unit and verbatim Lean signature. The component modules
and declarations match those records.

Changes by the second reader: removed the redundant public IsIso import from the
new chart module, added the needed proof-only IsIso import directly to the parent,
and recorded this review and the additional searches. No theorem statement or
proof argument changed. Final dry-run and push checks are run by deliver3.py.
