## What changed

The unchanged `completed_system_comparison` statement is reduced by a complete categorical
assembly to the pointwise geometric comparison and the normalized tensor-operation
construction. The assembly constructs the etale identity/composition maps by precomposition
with an equivalence, and the raw rational maps by postcomposition with the fully faithful
realization. Six proved private categorical lemmas establish these lifts and the corresponding
reconstruction equations from the counit-mate equation. The four tensor-unit normalizations
are retained explicitly.

`LisseCompletedCoefficientIso` proves the coefficient-ring identification and every residue
projection equation directly from the supplied finite-constant isomorphisms and limiting
coefficient cone. It does not invoke the general completed-constant-sheaf reduction theorem.

All existing mathematical data move, with their names, fields and meanings preserved, into
`LisseCompletedSystemData`, which the original module publicly imports. This permits the
new geometric subresults to import the data without an import cycle. The large data records
remain together. Parent records group the existing integral comparison, integral-operation and ambient-system
fields without adding or dropping a field. Explicit types on inferred tensor units/direct
images and controlled reducibility address repeated endpoint unfolding. Explicit
noncomputable declarations avoid unnecessary executable-code generation; the full data
artifact export and type checking completed in 47.2 seconds.
A mechanical field comparison checks all 18 Comparison, 14 Operation and 20 System
field statements verbatim modulo whitespace after the regrouping. No WeilConjectures
source module changes. Qualified inherited getters now belong to their parent records;
dot access is preserved. The actual consumers use none of those getters or positional record constructors.
The current downstream list has 54 modules, all recorded with their holders and unchanged
meaning in the change record. This interface change is documented for review.

Validation: all five delivery modules export and compile cleanly. The main assembly takes
5.7 seconds. Both unchanged downstream consumers also compile against the sandbox build:
NormalCompletedIntegralModel (23.2 seconds) and SmoothLisseIntegralLattice (21.4 seconds).
The newly landed direct importers AdicHeartIntrinsicFibres (49.5 seconds) and
FiniteEtaleAdicCohomology (40.9 seconds) also compile unchanged. The current 54-module
transitive user list is recorded in the change record.

Change record: `coord/changes/lisse-completed-system-data.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CompletedLisse.completed_system_comparison` by a complete
assembly proof. This is a decomposition, not a full proof of the geometric theorem:
one original hole is closed and two strictly smaller geometric holes are added.

The additional fully proved public theorem is
`AlgebraicGeometry.ProEtale.completed_coefficient_iso_exists`
(`lem-per-lisse-completed-coefficient-iso`). Its private diagram map/isomorphism constructions
contain no holes. The six private lift/descend/mate lemmas also contain no holes.

Every remaining hole introduced by this delivery:

- `AlgebraicGeometry.ProEtale.CompletedLisse.completed_pointwise_comparison`, node
  `lem-per-lisse-completed-pointwise-comparison`: the fixed-base geometric comparison,
  with the supplied coefficient datum and coefficient isomorphism retained exactly.
- `AlgebraicGeometry.ProEtale.CompletedLisse.completed_tensor_operations`, node
  `lem-per-lisse-completed-tensor-operations`: the tensor operation construction and its
  ambient tensor normalizations and counit-mate equation. It contains no etale/raw
  identity or composition coherence assertions.

No hole occurs inside a definition. No definition selects an arbitrary witness of an
unproved existence theorem. The final existence proof chooses witnesses only inside its
proof. The two remaining statements are separate geometric parts of BS 6.8.4, not a renamed
System existence assertion; the categorical proof genuinely supplies the omitted coherence.

Edge cases checked mathematically: the empty scheme and rank-zero charts have zero module
sheaves; ranks may vary on different charts; n=0 is the positive first residue quotient;
ramification index two uses the stated ceiling reindexing; the identity coefficient inclusion
and identity scheme map give ordinary tensor-unit maps. No global-rank, nonempty-scheme,
unramified-extension or global-lattice hypothesis has been added.

## No longer needed

Removed these proof-only imports from the original module:
`Sheaf.Paper.CompletedConstantSheafReduction`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
`Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections`, and
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.

All except the first remain mathematical dependencies of the geometric subresults or
statement prerequisites; the DAG retains them in those places. The original theorem now
imports the three subresult modules and the `choose` tactic used by its proof, and publicly
re-exports
the data module.

Node `lem-weil-pbc-completed-constant-sheaf-reduction` and module
`Sheaf.Paper.CompletedConstantSheafReduction` are unnecessary for this route. The actual
`adicLisseRingSystem` already uses constant quotient sheaves, and the given finite-constant
identifications intertwine them with the continuous finite diagram. Limit uniqueness gives
the required normalized coefficient isomorphism directly. Removed the corresponding old
top-level tool-use entry. This is pruning from this proof, not a claim that all other library
users of that node disappear. No module is withdrawn.

The unit route `sk-p-dl-a1-perverse` and all of its realized nodes remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was weakened or marked disputed. The original step 1 discussed
the general continuous adic datum, although the specific `adicLisseRingSystem` in this
statement is already the diagram of constant quotient sheaves. The extra completed-constant
comparison is therefore avoidable here.

The original single existence hole combined two large geometric constructions with the
categorical coherence argument. The delivery isolates those constructions and proves the
coherence rather than adding a new hole for it. The data extraction is for acyclic imports;
all original large records stay in one module, and no compile limit is raised.

## New nodes

`def-per-lisse-completed-system-data` records the existing comparison data in their new
module, including the parent records that group existing fields. It asserts no inhabitance.

`lem-per-lisse-completed-coefficient-iso` is proved: naturality on constant sections and
uniqueness of limits produce the coefficient isomorphism and all residue projections.

`lem-per-lisse-completed-pointwise-comparison` isolates BS 6.8.4(1),(4) at one fixed base:
finite-system descent, transport of integral reconstruction, and rational Hom localization.
It retains the already supplied coefficient datum/isomorphism and has no operations.

`lem-per-lisse-completed-tensor-operations` isolates pullback and finite coefficient extension:
actual tensor units, their local basis comparisons, localization, ambient identity/composition
normalizations, and the reconstruction counit-mate equation. Etale and raw coherence are
proved separately in the original module.

The existing item node's proof, proof dependencies, proof origin and Lean attachment now
follow the actual assembly. Its mathematical statement and the unit route are unchanged.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
