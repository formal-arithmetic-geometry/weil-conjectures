## What changed

`lean/WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean` closes five original
proof holes: `AlgebraicGeometry.GrpObj.toMixed_bijective`,
`AlgebraicGeometry.GrpObj.commutator_mem_mixedPoints`,
`AlgebraicGeometry.GrpObj.instLieAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopLie`,
`AlgebraicGeometry.GrpObj.infPointsMap_infBracket`, and
`AlgebraicGeometry.GrpObj.infBracket_mem_range_infPointsMap`.

The explicit mixed-point inverse extracts constant and mixed coefficients sectionwise;
the axis restrictions kill the two unmixed coefficients. Its ring-homomorphism laws,
naturality, locality and base compatibility are proved. The commutator restricts trivially
on both axes. Scaling the outer infinitesimal fixes the first projection, rescales the
second and the mixed term, proving scalar compatibility. Functoriality uses preservation
of group commutators; the range argument lifts the commutator and cancels the monomorphism
on both axes. Three proved private helpers implement coefficient injectivity, compression
and explicit scheme factorization.

Repair H8: the four anonymous LieRing field holes are now the public named theorems
`lieBracket_add`, `lieBracket_add_right`, `lieBracket_self`, and `lieBracket_leibniz`, placed
before the LieRing instance. The instance uses exactly the four applications requested
by reviewer X-39192. Each theorem has its own matching node, source, complete coefficient
and invariant-derivation proof in words, and blueprint tag. The statements have exactly
the field conclusions over arbitrary `Lie G`; none assumes the LieRing being constructed.
These obligations remain in the item's module as expressly permitted by the review entry
and coord/brief-stage3.md §3; no new module or import cycle is introduced.

Repair F: every occurrence of the nonexistent scalar instance name in this delivery was
replaced by the actual generated name above. The exact read-only usage query was rerun:
280 downstream modules, zero textual mentions of the actual instance name. Its name,
visibility, statement and inherited data are unchanged. The change record is
`coord/changes/group-scheme-bracket-scalar-proof.md`. No forced adaptation is needed.

Repair F/H11: the independent worker's second reading below replaces the proof author's
previous check, after opening the repaired Lean and all four nodes.

## Proved and sorry left

Five of nine original sorry occurrences have complete Lean proofs, in:
`AlgebraicGeometry.GrpObj.toMixed_bijective`,
`AlgebraicGeometry.GrpObj.commutator_mem_mixedPoints`,
`AlgebraicGeometry.GrpObj.instLieAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopLie`,
`AlgebraicGeometry.GrpObj.infPointsMap_infBracket`, and
`AlgebraicGeometry.GrpObj.infBracket_mem_range_infPointsMap`.

The remaining four occurrences were extracted from `AlgebraicGeometry.GrpObj.instLieRingLie`
as required by H8. Their replacement obligations are:

- `AlgebraicGeometry.GrpObj.lieBracket_add` — node `lem-ag-lie-bracket-add`.
- `AlgebraicGeometry.GrpObj.lieBracket_add_right` — node `lem-ag-lie-bracket-add-right`.
- `AlgebraicGeometry.GrpObj.lieBracket_self` — node `lem-ag-lie-bracket-self`.
- `AlgebraicGeometry.GrpObj.lieBracket_leibniz` — node `lem-ag-lie-bracket-leibniz`.

Each has proof exactly `:= by sorry`. There is no sorry in an instance, private declaration,
or definition. Four field holes are replaced by four named obligations: extraction adds
four named theorem holes and removes four anonymous field occurrences, for zero net change.
This repair is documentation/extraction of the unfinished Lie-ring argument, not four new
proofs. The full delivery's net decrease remains five occurrences. Scalar compatibility
still transitively depends on the four named obligations through the LieRing instance.

The repaired module compiles with lcompile.py. The dry run checks compilation and the
maintainer's axiom probe. Arbitrary commutative rings and base schemes are supported;
no field, smoothness, characteristic, affine, or nonemptiness hypothesis was added.
All definition data is explicitly constructed; no arbitrary witness of an unproved
existence theorem is used.

## No longer needed

No node or module is claimed pruned from target reach. The second reader changed
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf` from a public
import to a proof-only import: its `PresheafOfModules.Derivation.Universal.desc_comp` is
used only in the proof of `homOfDerivation_comp_unitSmul`. All three imports are needed;
none was removed. The matrix-only modules
`Sheaf.AlgebraicGeometry.MixedCommutatorTangent` and
`Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket` do not prove the general-base-scheme
obligations; they were not imported before and are not claimed pruned elsewhere.

## Where the brief, the DAG or earlier work was wrong

The original audit entry has no obligation nodes for the four anonymous LieRing fields.
It did not satisfy the rule that each remaining sorry be a public named theorem with
its own node and complete proof docstring. The previous report's claim that leaving these
fields untouched was sufficient was wrong; H8 is repaired by the four explicit obligations.
The previous scalar-instance name was nonexistent; the real generated name is used above
and in the rerun usage query. The prior second reading was the proof author's own check,
so it was not independent; an independently delegated worker now replaces that section.

No mathematical statement of an existing declaration, target, or DAG node was changed.
The four original audit-associated nodes concern characteristic-zero matrix groups and
have their own lean.module records in other modules; they supply no numbered proof plan
for the general-base-scheme fields here. The new nodes record the actual general statement
of each obligation and distinguish their agent-written coefficient proofs from that
matrix-only source. Unit sk-d-tangent has no fixed proof steps to bypass. No existing node
is changed. Small cases checked: the zero tangent vector, commutative group schemes,
characteristic two (alternation uses D²-D², never division by two), the empty base,
and nonaffine/nonsmooth group schemes (all derivations are sheafwise).

## New nodes

`lem-ag-lie-bracket-add` records `AlgebraicGeometry.GrpObj.lieBracket_add` in the item's module: The mixed-commutator bracket is additive in its first argument. Its proof constructs the invariant derivation sheafwise, identifies the mixed coefficient with the associative commutator, and expands the corresponding identity. The three Mathlib search kinds and whole-DAG source search found no exact arbitrary-base-scheme statement; the unavailable LeanSearch response is recorded honestly.

`lem-ag-lie-bracket-add-right` records `AlgebraicGeometry.GrpObj.lieBracket_add_right` in the item's module: The mixed-commutator bracket is additive in its second argument. Its proof constructs the invariant derivation sheafwise, identifies the mixed coefficient with the associative commutator, and expands the corresponding identity. The three Mathlib search kinds and whole-DAG source search found no exact arbitrary-base-scheme statement; the unavailable LeanSearch response is recorded honestly.

`lem-ag-lie-bracket-self` records `AlgebraicGeometry.GrpObj.lieBracket_self` in the item's module: The mixed-commutator bracket is alternating, in every characteristic. Its proof constructs the invariant derivation sheafwise, identifies the mixed coefficient with the associative commutator, and expands the corresponding identity. The three Mathlib search kinds and whole-DAG source search found no exact arbitrary-base-scheme statement; the unavailable LeanSearch response is recorded honestly.

`lem-ag-lie-bracket-leibniz` records `AlgebraicGeometry.GrpObj.lieBracket_leibniz` in the item's module: The mixed-commutator bracket satisfies the derivation form of the Jacobi identity. Its proof constructs the invariant derivation sheafwise, identifies the mixed coefficient with the associative commutator, and expands the corresponding identity. The three Mathlib search kinds and whole-DAG source search found no exact arbitrary-base-scheme statement; the unavailable LeanSearch response is recorded honestly.

The change record is `coord/changes/group-scheme-bracket-scalar-proof.md`.

## Earlier second reading (a previous round; superseded)

Independent reviewer: Q2 worker `repair_second_reader` (separate agent
`/root/repair_second_reader`), 2026-10-13. I did not write or modify the Lean proofs,
the four obligations, their docstrings, their nodes, or the change record. I compared
repository and repaired Bracket.lean, read all four new nodes and the relevant original
nodes and unit record, and wrote only this second-reading section.

H8: all four remaining sorry occurrences are now public named theorems, before the
LieRing instance. Each has exactly `:= by sorry`, the named source, a complete
natural-language invariant-derivation argument, and its matching blueprint tag and node.
The instance fields are exactly the four applications requested by X-39192. The
compiled, exported statements have parameters `{S : Scheme}`, `(G : Over S)`,
`[GrpObj G]`, and the displayed vectors only; none assumes a LieRing or LieAlgebra
instance for Lie G. Thus the extraction has no circular LieRing hypothesis.

| Public theorem (namespace AlgebraicGeometry.GrpObj) | Exact conclusion | Node |
| --- | --- | --- |
| lieBracket_add (x y z : Lie G) | ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ | lem-ag-lie-bracket-add |
| lieBracket_add_right (x y z : Lie G) | ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ | lem-ag-lie-bracket-add-right |
| lieBracket_self (x : Lie G) | ⁅x, x⁆ = 0 | lem-ag-lie-bracket-self |
| lieBracket_leibniz (x y z : Lie G) | ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ | lem-ag-lie-bracket-leibniz |

I checked each node's statement, verbatim Lean statement, declaration/module record,
source, proof steps and proof_deps against the corresponding docstring. The steps give
the same sheafwise invariant extension, mixed-commutator identification, and final
algebraic expansion. The listed dependencies are the group-object and dual-number
constructions, not a stronger matrix-group bracket result. The source honestly records
the original adopted module's general Lie-ring paragraph and the agent-written argument;
it does not attribute the arbitrary-base conclusion to the characteristic-zero matrix
blueprint. Right multiplication is the correct convention: R_ab = R_b composed with R_a,
so its pullback is R_a^* R_b^*, giving the stated commutator sign. The alternating
argument subtracts D_x squared from itself, so characteristic two is included. The
sheafwise construction needs no affineness or smoothness, and also covers zero vectors,
commutative groups, and an empty base. The four conclusions are exactly the missing
fields, with no extra hypothesis or weakened conclusion.

F: I independently checked the actual exported scalar instance in the original compiled
module and in the freshly compiled repaired module. Both names are
`AlgebraicGeometry.GrpObj.instLieAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopLie`.
The exported LieRing name is also confirmed as
`AlgebraicGeometry.GrpObj.instLieRingLie`. The report and change record now use the
actual scalar name; the original and repaired instance types agree. I reran the exact
read-only downstream query with its unqualified generated name: 280 downstream modules
and zero textual users. The change record states that result correctly. No forced
adaptation is introduced.

F/H11: this is another worker's independent reading, replacing the proof author's prior
self-check. I compiled the repaired module with approved lcompile.py (exit 0), then
compiled it together with an importing probe (exit 0) to inspect the exported names and
all four complete theorem types. The probe files were removed. A source scan found only
the four named theorem sorries and no forbidden constructs or sorry inside a definition,
private declaration, or instance. The five previously completed proofs remain complete
Lean proofs, but the delivery still has four named obligations; extraction itself closes
no further mathematical hole, and the scalar instance still has transitive dependence
on the unfinished LieRing obligations. I make no fully sorry-free or target-completion
claim.

Existing statement signatures and mathematical definition data are preserved. Imports
are unchanged. The explicit mixed-point construction does not choose arbitrary data from
an unproved existence theorem. I checked sk-d-tangent's realized statement and steps:
both are empty, and this repair bypasses no fixed unit step. No pruning or existing-node
change is claimed. The report accurately distinguishes five original holes proved from
four fields merely extracted into four named obligations.

## Second reading by Q2

Independent second reader, dispatched directly on 2026-10-13. I did not write the
submitted proofs. This reading supersedes the earlier round above.

1. **Existing interfaces: PASS.** I read the full repository/sandbox diff and ran the
   project's declaration-signature comparison: `statement_changed` is empty. The original
   definitions, bracket data, existing theorem signatures and visibility are unchanged.
   The LieRing fields now apply the four named obligations; the scalar instance moves
   after the rescaling lemmas and changes only its proof field. Its change record records
   the original and new instance bodies and downstream users. No target is altered.
2. **Lean proofs and axioms: PASS with four recorded holes.** The delivered module compiles
   cleanly through lcompile.py. A scratch copy with explicit `#print axioms` shows only
   `propext`, `Classical.choice`, and `Quot.sound` for `toMixed_bijective`,
   `commutator_mem_mixedPoints`, `infPointsMap_infBracket`, and
   `infBracket_mem_range_infPointsMap`. A separate importing probe verifies the exported
   LieRing and scalar instance names and reports only those three axioms plus `sorryAx`
   for both instances. It also verifies the complete types of the four obligations:
   arbitrary `{S : Scheme}`, `(G : Over S)`, `[GrpObj G]`, and the vectors, without any
   LieRing/LieAlgebra assumption. The only four source sorries are exactly the named
   theorem bodies listed above. No forbidden construct, hollow definition, or arbitrary
   witness chosen from an unproved existence theorem occurs. The explicit compression
   preserves constants and mixed coefficients, and its two axis equations kill the other
   coefficients; its naturality and stalk-locality proofs are genuine Lean proofs.
3. **Extracted statements: PASS as decomposition only.** I read all four docstrings and
   nodes. They are precisely the four separate LieRing laws, each strictly a part of the
   structure obligation, with unchanged hypotheses. For the invariant-extension argument,
   right translation satisfies R_ab = R_b composed with R_a, so pullback reverses this
   order and gives the stated positive commutator D_x D_y - D_y D_x. Left invariance
   follows from associativity; evaluating at the identity proves injectivity. Products
   at a single square-zero parameter give addition; expansion in two parameters gives
   the bracket. The two distributive identities, D_x squared minus itself, and the
   displayed eight-term Jacobi expansion prove the four conclusions respectively.
   No division, smoothness or affineness is used; the construction is sheafwise. I checked
   zero vectors, commutative groups, characteristic two, and the empty base (all sections
   and tangent vectors are then trivial). I searched anew using LeanFinder for
   infinitesimal tangent-bracket alternation, Loogle for commutator/self, and grep for
   mixedPoints, infBracket and invariant derivations, plus direct searches in lean/,
   the upstream module and the DAG. The generic group commutator/self lemma compares a
   point to itself, whereas this bracket uses two different parameter lifts; applying
   generic LieRing laws here would be circular. The manifold results and matrix-only
   MixedCommutatorTangent/MatrixSubgroupLieBracket modules do not cover arbitrary schemes.
   No split-off obligation can be closed by a short existing-lemma application. Four
   anonymous field holes replaced by four named holes give no net proof progress;
   the five other original holes are the delivery's actual decrease.
4. **Top-down route and imports: PASS after repair.** The proof constructs the mixed
   factorization directly and then uses commutator functoriality and monomorphism
   cancellation, without new lower holes for these proofs. I inspected the four original
   audit-associated nodes: their principal declarations are in Ring, Cartier,
   GeneralLinear.ClosedSubgroup.Lie and Monodromy, and their proof_deps describe those
   declarations, not a general-scheme bracket proof plan. None is bypassed by this
   delivery. The sk-d-tangent unit has empty realized.statement and realized.steps;
   its fixed route is preserved. All three imports have uses. I repaired the third
   import's public visibility because Universal.desc_comp is used only in a proof.
   No module is claimed pruned.
5. **DAG agreement: PASS.** Each new node's verbatim Lean signature occurs in the file;
   its declaration, module, file, source, created record, blueprint ancestor/place,
   chapter and unit agree. The proof steps match the docstring, proof_deps equals the
   union of their uses, and proof_origin honestly identifies the agent-written
   general-scheme argument rather than attributing it to the matrix-only blueprint.
   The cited field-group-scheme definition supplies the group-object terminology;
   the actual arbitrary-base construction uses the same general GrpObj diagrams and
   does not import any field-specific conclusion. Existing nodes are not changed.

Changes made in this reading: made the differentials-presheaf import proof-only and
corrected the current import account under No longer needed. No proof, mathematical
statement, definition data, or node was rewritten. Scratch probes are excluded from
this delivery. The dry run and delivery below provide the final preflight verification.
