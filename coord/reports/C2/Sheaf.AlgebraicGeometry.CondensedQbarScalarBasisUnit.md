## What changed

The original theorem
`AlgebraicGeometry.ProEtale.CondensedRing.exists_condensedQbar_scalar_basis_unit`
keeps its declaration signature byte for byte. Its proof combines an ordinary coefficient
construction with a proved descent to the derived category.

New `CondensedQbarScalarBasisSections.lean` states the remaining construction entirely in
ordinary internal modules: common coherent basis sections, finite-limit preservation of scalar
extension, and the ordinary extension-unit/scalar-action copower. Its docstring explains the
finite-support coordinates, continuity, pullback coherence, tensor calculation and flatness.

New `CondensedQbarScalarBasisUnitOfSections.lean` proves
`AlgebraicGeometry.ProEtale.CondensedRing.condensedQbar_scalar_basis_unit_of_sections`.
The proof first evaluates the copower of scalar-unit maps in each degree, then preserves that
copower under localization. Exact-functor factorization and central naturality compare the
localized legs with the chosen left-derived extension adjunction unit. Finally the representative
isomorphism transports the copower to an arbitrary derived object. The last transport argument
from the first worker is retained in a generic helper, avoiding repeated unfolding of concrete
sheaf inverse-image constructions during elaboration. Its unused private helper was removed, and its unnecessary
section-coherence hypothesis was removed from this newly introduced helper theorem. The outer
original theorem retains section coherence unchanged.

All added imports needed only for proofs are plain imports. The existing pushforward module
matches the repository exactly and needs no change. No existing definition, signature, visibility,
or public import was changed. There are no change records or forced adaptations.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_condensedQbar_scalar_basis_unit`
(node `lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit`).

New proved declaration, with no direct hole:
`AlgebraicGeometry.ProEtale.CondensedRing.condensedQbar_scalar_basis_unit_of_sections`
(node `lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit-of-sections`).

New hole added, and the only direct sorry in this delivery:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_condensedQbar_scalar_basis_sections`
in `CondensedQbarScalarBasisSections.lean`
(node `lem-weil-pbc-condensed-qbar-derived-scalar-basis-sections`).

This is a decomposition, not a completed proof of the original coefficient construction:
one original hole closed, one ordinary construction hole added, net zero. The new remaining
statement does not assert any derived unit decomposition. All degreewise and derived descent
steps are proved here. The original theorem still depends on the named construction hole.

## No longer needed

The direct proof import `Sheaf.Paper.ProfinitePointPullback` was removed from the original
unit module and is now a proof import of the remaining ordinary construction module. The old
proof dependencies `lem-weil-pbc-finite-dimensional-linear-homeomorphism` and
`lem-weil-pbc-profinite-point-pullback` are replaced as DIRECT dependencies of the original
node by the two new construction/descent nodes. Both old nodes remain transitive dependencies
of the construction; neither node nor its module is pruned. No public import was removed.
No modules are claimed as pruned, and no tool-use approvals were withdrawn.

The provisional descent import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective` is subsumed
by its proof import of `WeilConjectures.CategoryTheory.DerivedCategory.Coproducts`, which
supplies the actual preservation theorem used. The redundant public import of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients` in the new sections
module was removed: the public scalar-action API already imports it.

## Where the brief, the DAG or earlier work was wrong

The first worker's remaining sections theorem already required the derived unit copower on
every complex. Since localization is essentially surjective, that merely moved almost the
whole original hole to an equivalent representative formulation. The second reading rejected
that split and replaced it with an ordinary-module construction, proving the nontrivial
termwise and localization argument rather than assuming it.

The two new node prose statements also omitted hypotheses/conclusions present in Lean: the
sections node mentioned only coherence, while the descent node omitted its complex-level
isomorphism hypothesis. Both now state the actual final interfaces. The original node's
proof and proof_deps now describe the proof as written.

The unit `sk-thm-properbasechange` realizes its statement and three steps in other nodes.
None of those nodes or their routes is bypassed. This is a reduction within the scalar-basis
node below the unit level.

## New nodes

`lem-weil-pbc-condensed-qbar-derived-scalar-basis-sections`: the ordinary finite-support
coefficient construction, coherent for all schemes, with flat/exact ordinary scalar extension
and the explicitly specified ordinary scalar-unit copower. This is the one unresolved node.
It has the full source and natural-language proof, and real LeanFinder, LeanSearch, Loogle
and grep searches.

`lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit-of-sections`: the proved descent from
ordinary module copowers and exactness to the original derived scalar-unit formula. It does
not assume section coherence, which the descent does not need. It uses the existing localized
central actions and the proved upstream coproduct/localization and exact-derived APIs.

## Second reading by C2

1. Compared every sandbox module with the shared repository using `diff`. The only changed
existing Lean module is the assigned unit module. Its existing theorem signature is byte for
byte identical; only proof imports and its proof change. The pushforward module was identical
and has been omitted. Both other Lean modules and their theorem signatures are new in this
delivery, so repairing their provisional statements needs no existing-interface change record.
No definition used by a target was changed.

2. Read the full proofs and checked the module-system headers, import visibility, forbidden
constructs and direct holes. There is no hole in a definition or private helper and no axiom,
unsafe code, opaque declaration, implementation replacement or external function. There is
exactly one direct sorry, the listed public ordinary construction theorem with its docstring
proof and matching node. Compilation and axiom-check results are recorded below.

3. Rejected the provisional representative-level restatement. The replacement construction
concerns ordinary modules and flatness only. Its coordinate proof uses finite-dimensional
spans of finite extensions, not a false assertion that arbitrary continuous maps into the
algebraic closure have finite support. The specified coefficient model explicitly restricts
to finite-subextension-valued maps. Tested the reasoning for a zero module, the empty scheme,
finite coordinate support, and changing the chosen copower. The formal descent also covers
an empty index family whenever its hypotheses hold; no hidden nonempty or finite-index
assumption is introduced. Repeated actual LeanFinder, LeanSearch, qualified Loogle and grep
searches with different queries. The finite-basis source template is private and cyclic to
import; no complete ordinary infinite-basis construction was found. Its argument is strictly
smaller than the original derived theorem because every degreewise and derived comparison is
now discharged by the separate proof.

4. Checked the proof from the original theorem downward. The top theorem combines the
ordinary construction and the proved descent; the latter uses the proved coproduct/localization
API and exact-derived comparisons. Imports used only by proofs are plain. The report names
every old direct proof dependency displaced by the split, while retaining their use in the
ordinary construction. No module is falsely counted as pruned. Inspected the unit's realized
statement and all three step lists: this node realizes none of those fixed steps, and the
fixed unit route is preserved.

5. Read the original and both new node records against the final Lean. Corrected the two
new prose statements, synchronized their verbatim Lean statements, and updated the original
node's proof, proof_deps and proof_origin. Each new node has source, complete proof plan,
search records, parentage, chapter/unit, creation and Lean records. The proof-dependency lists
are exactly the unions of the proof steps' node uses.

Second-reading changes: replaced the near-restatement by an ordinary-module construction;
proved the actual termwise, localization and left-derived-unit descent; retained the valid
representative/coproduct transport; removed an unused helper and a redundant hypothesis from
the new descent theorem; corrected proof import visibility/redundancy, node descriptions and
dependencies, and the report's hole accounting. The original target statement is unchanged.

Verification: the final compilation and delivery checks are recorded below. Earlier compilation
passed, but a delivery retry hit the 60-second file limit. Profiling identified repeated concrete
sheaf-category elaboration in the representative transport. Moving this categorical transport
to a generic helper reduced the descent module compilation from about 48 seconds to 8.4 seconds;
the now-unnecessary heartbeat overrides on the transport and concrete theorem were removed.
The final scratch import check printed axioms for all three public declarations and the two
generic private descent lemmas. Both generic lemmas use exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. All three concrete public declarations also have `sorryAx`.
Tracing the concrete descent shows no extra holed theorem in its proof body: the dependence
is already in its statement's existing infrastructure, including
`AddCommGrpCat.hasFunctorialFlatResolution` and
`AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`, via `upperStarFromPoint`.
These inherited infrastructure holes are not claimed closed or introduced by this delivery.
The unit theorem additionally uses the explicitly listed ordinary construction hole.
No axiom beyond the permitted three and these open dependencies occurs.

Final verification after elaboration repair: `lcompile.py --all` compiled the three modules
without errors or warnings (0.1 s, 23.0 s, 15.3 s, respectively). The original target signature
and both new nodes' verbatim Lean signatures were checked again and match exactly.
