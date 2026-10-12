## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.exists_lift_reverse_components`
with a complete assembly proof. The proof restricts the chosen bases, uses a finite set of
integer degree pairs, conjugates into standard free sheaves, and transports the lifted maps
back using naturality and inverse cancellation. It constructs the natural comparison on
all complexes and proves both the reverse-degree support and every component equation.

Added the proof-only import `Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteMatrixLift` and
proof-only Mathlib imports for integer finite intervals and their finite subtype/product.
The original public imports and original theorem signature are retained. Removed the unused
proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor`. Added the proved
private categorical helper `transport_lift`. Updated the original DAG proof to this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_lift_reverse_components`
(node `lem-pc-finite-free-reverse-components-lift`). There are no sorries in its module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_finite_free_matrices_of_stalk_local`
(node `lem-pc-finite-free-stalk-finite-matrix-lift`, module
`Sheaf.AlgebraicGeometry.FiniteFreeStalkFiniteMatrixLift`). Its entire proof is `:= by sorry`.
This delivery is a decomposition: one upper hole closed, one lower hole added, net zero.
It does not claim a sorry-free proof of the original theorem's dependency closure.

The lower statement only concerns a finite family of maps between standard free sheaves.
It has no complex, boundedness, arbitrary basis, infinite degree family, reverse-degree
condition, or homotopy equation. Basis transport and assembly are proved in the item.
The only remaining task is lifting finite matrix coefficients and checking their pullback
in the specified canonical comparison; its docstring and DAG node give the full argument.

## No longer needed

Removed the unused proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor`
from the item. Removed the redundant public import
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` from the new finite-matrix
module: replaced it with the direct statement import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`. The attempted removal alone failed
because `SheafOfModules.free` is not exported by Mathlib’s Modules.Sheaf module.
No whole module is claimed globally pruned. The scalar stalk-definition
node `def-weil-pbc-module-stalk` is no longer a direct proof dependency of the original node:
it is used by the new matrix node instead and remains a transitive dependency.

The route does not import `FiniteFreeStalkDegreewiseLift`,
`FiniteFreeStalkChainMapLift`, `FiniteFreeStalkChainMapLiftLocal`,
`FiniteFreeStalkChainMapLiftRestrict`, or `FiniteFreeStalkDegreewiseShrink`.
These existing alternatives were inspected but are not dependencies of this proof.
The chain-map alternatives impose chain equations and include a shrinking step that this
statement does not need. They are not claimed globally unreachable or globally pruned.
The original unit's realized arrays are empty; its statement and route were not changed.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed signature was found. The original DAG correctly describes
the matrix argument but its listed dependencies are definitions and the open-pullback
comparison; they do not state the actual coefficient-lifting conclusion. The new matrix
node isolates that missing part. Existing degreewise lifting has a related interface over
the global stalk map, but does not immediately give the required comparison on all complexes
on the prescribed open V. No unsupported import or circular dependence was introduced.

The edge cases checked mathematically are empty finite index types, source or target rank
zero, d=0, and terms outside the support bounds. The Lean assembly handles d=0 and all
outside-bound cases without changing assumptions; it uses uniqueness of maps involving
zero objects. An empty coefficient list in the new lemma can take U=V.

Only launcher single-file/sandbox compilation was used. LeanSearch returned an internal
server error; it is recorded as unavailable. LeanFinder, Loogle, Mathlib grep and the full
blueprint search were performed; no exact finite-matrix lifting statement was found.

## New nodes

`lem-pc-stalk-from-spec-subopen` states the compatibility of canonical ambient-stalk
maps with nested open inclusions. Its new module StalkFromSpecSubopen contains the
fully proved three-line equality theorem used by the comparison definition.
It adds no hole and no change record is required.

`def-pc-stalk-restriction-within-iso` defines the nested-open comparison used by the proof.

`lem-pc-finite-free-stalk-finite-matrix-lift` states simultaneous lifting of maps between
standard finite free sheaves for an arbitrary finite index type. Its source is the finite
matrix extension in `lem-pc-perfect-locus`, expanded by steps 2--3 of the original node.
It records the searches actually run and the complete natural-language coefficient and
comparison proof. No existing statement, definition, unit, or target was changed, and no
change record or forced adaptation is required.

## Earlier second reading (a previous round; superseded)

The item theorem signature is unchanged. The assembly proof was compiled with the new matrix and nested-open comparison modules; the remaining matrix theorem is a strict coefficient-lifting subproblem. The new definition is a direct pullback composition comparison.


## Second reading by W2

1. **Unchanged interface: PASS.** Compared all three delivered modules with the
   repository. Only the item exists there; its complete existing theorem signature,
   from `theorem exists_lift_reverse_components` to `:= by`, is byte-identical.
   The new private `transport_lift` is proved. The original public imports remain;
   removing the presheaf-stalk import changes only proof visibility. There is no
   existing definition or statement change and no forced adaptation.
2. **Proof and axioms: PASS as a decomposition.** All original three modules compiled locally
   through `lcompile.py --all`. Read every branch of the assembly proof: naturality
   transports both bases; finite interval pairs carry the lifts; `hzero` handles the
   non-reverse relation; strict lower/upper bounds and preserved zero objects handle
   the other pairs. `mapHomologicalComplexCompIso` supplies a comparison on all
   complexes, with the module comparison as each term component. A separate scratch
   probe printed the axioms of the item, the matrix theorem and the comparison:
   the first two use only propext, Classical.choice, Quot.sound and sorryAx;
   the comparison uses only the three permitted axioms. Exactly one sorry remains,
   the named matrix theorem. No forbidden declaration, hollow data, or witness
   chosen from an unproved existence theorem occurs in a definition. The chosen
   bases inside the theorem come from its explicit hfree hypothesis, not a sorry.
3. **Split statements: PASS.** Read the finite-matrix signature and its complete
   docstring argument against its node: arbitrary scheme and point, prescribed
   V, finite index type (in an independent universe), varying finite ranks, and
   the specific comparison all agree. Each entry lifts by
   `TopCat.Presheaf.exists_le_germ_eq` (Mathlib Stalks.lean:447); a finite
   intersection suffices. Read the source-library freeMatrix, free_hom_ext,
   sum_freeπ_ιFree and freeMatrix_pullback (Modules/Sheaf.lean:254--339), and
   Mathlib Opens.fromSpecStalkOfMem_ι and fromSpecStalkOfMem_toSpecΓ
   (Stalk.lean:176,193), which justify comparison and coefficient compatibility.
   Empty index types and zero ranks give zero maps on V; rank one is scalar germ
   lifting. This is strictly smaller than the item: no arbitrary bases, complex,
   bounded support or reverse-degree assembly. The comparison definition is an
   explicit composition of existing natural isomorphisms, not an existential
   choice. Independent LeanFinder query about trivial vector bundles, Loogle
   query `"germ", "exists"`, and grep on Mathlib, lean/Sheaf and
   lean/WeilConjectures found ingredients but no exact available replacement.
   Existing DegreewiseLocal still has sorry, concerns the global stalk map and
   separate neighbourhoods, and would require further comparison transport;
   the chain-map alternatives impose equations absent here. The original blueprint
   file is not installed on this machine; attempts to fetch its pinned public
   GitHub path returned HTTP 404. Source verification therefore used the repository
   node statements and proof plans, the unit text, and the concrete source-library
   and Mathlib ingredients just listed; no claim of rereading the absent original
   blueprint paragraphs is made.
4. **Route and pruning: PASS after repair.** Read the original node and the
   sk-thm-picard-perfect unit, whose realized arrays are empty. The route still
   lifts coefficients, transports bases and assembles bounded reverse maps;
   no unit statement or step was bypassed. The added proof imports of the item
   are ordinary imports. Corrected No longer needed to name the actually removed
   PresheafModuleStalkFunctor import and its old direct dependency. That node remains
   transitive through the matrix lemma; no globally pruned module is claimed.
   Replaced the new matrix module's broad public source-library import by the
   direct public Mathlib free-sheaf import required by its signature.
5. **Nodes versus Lean: PASS after repair.** The three assembly steps correspond
   to hPVfree/t, transport_lift/e, and k with its case analysis. proof_deps is their
   cited union. The matrix node has its source, full proof steps, created record,
   blueprint ancestry, searches, chapter/unit and verbatim Lean signature.
   Added its missing statement reference to the comparison-definition node.
   Corrected that definition node's status from unsplit to split, and replaced
   paraphrased search queries/results by the actual logged searches (including
   unavailable LeanSearch). Its proof is empty because it records a construction;
   its Lean body is fully explicit and compiled. No original node statement,
   unit realized field, or target was modified.

Second reading changed the new matrix module's statement import, the comparison
node's status and search records, the matrix node's comparison dependency, and the
report's pruning accounting. The correct assembly proof was retained. Holes closed:
exists_lift_reverse_components (one). Holes added:
exists_finite_free_matrices_of_stalk_local (one). Net zero; decomposition only.


Final contract repair: extracted the map-equality proof from the comparison definition
into the fully proved `AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_homOfLE`,
module `Sheaf.AlgebraicGeometry.StalkFromSpecSubopen`, node
`lem-pc-stalk-from-spec-subopen`. The definition now refers to that named theorem
through a public import required by the exposed definition body. A private import
was tried and Lean rejected it as an inaccessible constant in a public definition. Its signature and construction are unchanged; proof
irrelevance identifies the equality proof. The new statement has exactly the same
Y, y, U, V and membership assumptions as the former inline proof. Its three-line
proof uses the two canonical-map identities and cancellation of V.ι; no hole was
added. The logged LeanFinder, Loogle and grep searches found the Mathlib ingredient but no existing
nested-open declaration. The DAG search found only the comparisons already
reviewed above. This is a named proof needed by a definition, as AGENTS.md §5
requires, not a new mathematical obstruction. The node includes its docstring
proof, source location and blueprint ancestry.

## Additional new proved node

`lem-pc-stalk-from-spec-subopen` names the equality proof needed by
`stalkRestrictionWithinIso`; its theorem is proved, with no sorry. Second reading
also changed that definition's body to reference this theorem. The total remains
one original hole closed and one strictly smaller hole added, net zero.

The named equality is also a clause of SpecStalkLimitAffineNeighbourhoods for
*affine* neighbourhoods, and a local `have` in ChainMapLiftRestrict. Neither is
an existing separately named theorem for arbitrary nested opens, so the extracted
three-line proof avoids importing the larger affine-limit or chain-map results.
LeanSearch for the equality returned Internal Server Error and is recorded as
unavailable. No sorry was introduced by this extraction.
