## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.finiteAffineCech_coefficient_baseChange`
with a complete Lean reduction to two independent parts of its argument. Its signature and
existing docstring are unchanged. The proof first constructs normalized module-sheaf maps,
proves each coefficient intersection affine, applies the single-coefficient affine bijectivity
criterion, and uses the existing sheaf-local isomorphism criterion to obtain equivalences on
all opens. It then proves restriction and scalar compatibility from naturality and linearity,
and applies the construction's face equation.

Added `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap`. Its concrete,
fully proved infrastructure consists of `coefficientSupportIso`, its restriction and scalar
compatibilities, `coefficientGenerator`, `coefficientPullbackGenerator`, and
`coefficientIntersection_preimage`. The generator definitions use the actual tilde and standard
module-pullback units. They choose no data from an unproved existence theorem. Its remaining
construction theorem supplies module morphisms, their unit normalization, and face
compatibility; it assumes neither affineness nor quasi-coherence nor a cartesian square.

Added `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonBijective`. Its remaining
theorem concerns one affine intersection and a given morphism with the fixed unit formula.
It asserts bijectivity only on affine opens and has no family or face compatibility assertion.
The original proof supplies the global sheaf-isomorphism argument, using the upstream
`isIso_of_bijective_app_of_isAffineOpen` from
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`.

Updated the original DAG proof and added one node for each remaining theorem. No existing
statement, definition, public import, instance, or target signature was changed. All three
sandbox modules compile together cleanly with lcompile.py. The final dry run supplies the
axiom probes and static delivery checks.

## Proved and sorry left

Closed the one original hole, by reduction:
`AlgebraicGeometry.Scheme.Modules.finiteAffineCech_coefficient_baseChange`
(node `lem-pc-finite-affine-cech-coefficient-base-change`). No sorry remains in the assigned
module. This is a decomposition, not a complete proof independent of the remaining items:
one hole closed and two new holes added, net minus one at this split.

Every new remaining sorry:

- `AlgebraicGeometry.Scheme.Modules.exists_coefficientComparison_maps`, node
  `lem-pc-finite-affine-cech-coefficient-comparison-map`, module
  `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap`.
- `AlgebraicGeometry.Scheme.Modules.coefficientComparison_affine_bijective`, node
  `lem-pc-finite-affine-cech-coefficient-comparison-bijective`, module
  `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonBijective`.

Both are whole proofs of public named theorems, with source references and complete proof
plans in their docstrings and DAG nodes. They separate construction from invertibility:
the first makes no bijectivity claim; the second takes a normalized morphism as input and
performs only the affine calculation. The assembly does not apply a renamed copy of the
original theorem.

## No longer needed

Removed the assigned module's direct proof imports:

- `Sheaf.AlgebraicGeometry.FiniteAffineCechIntersectionBaseChange`, node
  `lem-pc-finite-affine-cech-intersection-base-change`.
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, node
  `lem-weil-pbc-module-pullback-affine-sections`.

Also removed `def-pc-finite-affine-cech-model` from the original node’s `proof_deps`: it
remains a statement dependency and its public import is retained. The proof does not apply
a theorem supplied by that node. This completes the list of old proof dependencies omitted
from the new `proof_deps`.

These declarations are still planned inputs of the new affine bijectivity item; they are
not claimed as mathematically pruned from the entire argument. No globally unnecessary
node or module is claimed. The existing public imports remain because the original
statement uses their declarations. New modules contain only imports required by their
statements and proved helper constructions, without importing unused proposed proof inputs.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The unit record's realized statement and
step lists are empty; this reduction keeps the termwise affine calculation of the existing
node and the cited coherence unit. It uses no flatness or covering assumption.

The original dependency signatures do not directly provide a comparison with all three
section-level compatibilities. `exists_tensorPullback_affine_sections` uses the explicit
tensor pullback and its chosen adjunction unit, whereas the coefficient model and this
statement use the standard module pullback. The library already proves affine pushforward
base change; the missing interface work is to connect the associated coefficient module
and standard units to that calculation while retaining face naturality. The new construction
and single-open criterion isolate those tasks instead of treating them as an application
that the existing signatures do not support.

Searches: LeanSearch for natural maps from associated section modules to pushforward of
pullback returned an internal server error. LeanFinder found the standard pullback/direct-image
adjunction and related section infrastructure. Loogle confirmed `tilde.adjunction` and its
invertible unit. Searches by coefficient names found no existing matching declaration;
related source modules inspected included `AffinePushforwardBaseChange`,
`AffineBaseChangeTensorComparisons`, `ModulePullbackAffineSections`, and
`AffineSectionsComplexCounit`. Exact queries and outcomes are recorded on the new nodes.

Read the source calculation at Stacks Project
[Section 30.5](https://stacks.math.columbia.edu/tag/02KE) and
[Lemma 30.5.1](https://stacks.math.columbia.edu/tag/02KG).
Checked edge cases of the new statements: empty opens give zero coefficient sections;
when r = 0 or there is no increasing tuple, the construction family is empty; intersections
have p+1 factors and hence are nonempty as index families even when the open itself is empty.
The construction allows arbitrary commutative squares; the affine bijectivity criterion
requires the cartesian square and affine source intersection. The latter applies to any
module morphism with the prescribed unit formula, since those generators and their local
scalar multiples span its source on affine opens. Neither statement assumes the desired
inverse or a base-change equivalence.

## New nodes

`lem-pc-finite-affine-cech-coefficient-comparison-map` records the construction of normalized
module morphisms, including face naturality, with no invertibility assertion. Its module
also contains the real generator and support constructions and their proved elementary
compatibilities. No data-valued definition contains a hole.

`lem-pc-finite-affine-cech-coefficient-comparison-bijective` records the local tensor
calculation for a single given normalized map. It has no choice of a family and no gluing
assertion. The proof plan explicitly transports the tensor-pullback presentation through the
unit-compatible isomorphism of adjoints. The original module performs the global descent
and assembles the three required equations. There are no change records because all existing
interfaces are preserved.


## Second reading by A3

1. **Existing interfaces: PASS.** Diffed every delivered module against the read-only
   repository. Only the assigned module existed there. Its theorem signature and original
   docstring are byte for byte unchanged; its public imports are unchanged. The other two
   modules and their declarations are new. The existing node changes only `proof`,
   `proof_deps`, and `proof_origin`. No target, existing definition, or instance changed.
2. **Lean proof and axioms: PASS as a decomposition.** Independently compiled all three
   files with `lcompile.py --all`; no errors or warnings. Compiled scratch copies with
   `#print axioms` for all nine public declarations. The six concrete helpers use only
   `propext`, `Classical.choice`, and `Quot.sound`. The two named remaining theorems and
   the assembled theorem additionally use `sorryAx`, exactly as reported. The only two
   written holes are whole public theorem proofs. No forbidden declarations or data chosen
   from unproved existence occur in the delivered definitions. The comparison family is
   eliminated locally inside a theorem proof, not exported as data from a definition.
3. **Split statements: PASS.** Read both statements and docstring arguments against
   [Stacks 02KG](https://stacks.math.columbia.edu/tag/02KG) and the termwise argument in
   [Stacks 02KE](https://stacks.math.columbia.edu/tag/02KE). Construction uses only a
   commutative square and the tilde/global-sections and pullback/direct-image adjunctions;
   it asserts no invertibility. Bijectivity assumes one normalized morphism and an affine
   coefficient in a cartesian square; the tensor associativity calculation proves exactly
   its conclusion. On an affine B the restricted global generators and their O(B)-scalar
   multiples span the source, so normalization on top determines the map there. Empty Z
   or B gives zero modules; r = 0 or p + 1 > r gives no tuples; p = 0 is a singleton
   intersection. Neither split theorem is a renamed copy of the original statement.
   Repeated LeanFinder and Loogle searches with adjunction/counit terminology and grep
   for `fromTildeΓ|pullbackPushforwardAdjunction|restrictFunctorIsoPullback`.
   Inspected `AffinePushforwardBaseChange`, `ModuleBaseChangeMapOpenRestriction`,
   `ModulePullbackAffineSections`, `AffineBaseChangeTensorComparisons`, and
   `LocallyFreeAffine`. These provide the planned adjunction and affine calculations,
   but no existing theorem supplies this coefficient functor's standard-unit normalization
   and face equation. Neither remaining proof can be closed by a short direct application.
4. **Route and pruning: PASS.** The written proof really proves affine intersections,
   upgrades affine-open bijectivity to a sheaf isomorphism, and proves the restriction
   and scalar equations; the construction supplies the face equation for the same maps.
   Checked that `isIso_of_bijective_app_of_isAffineOpen` is the upstream wrapper around
   Mathlib's basis criterion. Every delivered import is used by a signature or proof;
   proof-only dependencies use plain imports. The two removed direct imports remain
   planned dependencies below the split, so no global pruning is claimed. Completed
   `No longer needed` with the omitted model proof dependency. Read the coherence unit
   and its `realized` record (statement empty, one empty step list): this retains its
   termwise affine Cech calculation and makes no replacement of a unit step.
5. **DAG agreement: PASS.** Checked all three node signatures verbatim against Lean,
   the old/new dependency difference, the union of each proof's uses, source references,
   creation records, chapter/unit, blueprint provenance, and search fields. The original
   node describes the actual assembly. The new nodes describe strictly smaller outstanding
   construction and affine-calculation tasks, with complete natural-language proofs.

Second reading changed only this report (the missing removed-proof-dependency entry and
this independent review) and the two new nodes' search records. No Lean repair was needed.
One original hole is closed by reduction, two are added, net minus one; this delivery is
explicitly a decomposition, and no module is claimed globally pruned.
