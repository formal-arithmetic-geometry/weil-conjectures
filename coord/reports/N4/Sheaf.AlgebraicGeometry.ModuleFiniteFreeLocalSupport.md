## What changed

`Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalSupport` now reduces the finite-rank
statement to the local finite support of one section. For each source basis map,
the proof obtains a local lift, constructs the finite intersection of its
neighbourhoods and the finite union of its supports, restricts the lifts further,
and composes them with the support inclusions. The private proved helper `exists_finite_support_of_unit_support` implements
this argument for an arbitrary sheaf of rings. The private categorical
helper `factor_restricted_coproduct` assembles the maps and proves the required
morphism equality by coproduct extensionality. All original public signatures
and public imports are preserved.

The new module `Sheaf.AlgebraicGeometry.ModuleUnitLocalSupport` states the
one-section step. `Sheaf.AlgebraicGeometry.ModuleSupportRestrictionEnlargement`
states the separate algebraic identity for restricting an already given lift
and enlarging its support. The parent and both new nodes record this route.
A private `direct_restrict_map` wrapper constructs the usual restriction map
with its direct target explicitly typed; its direct target is used for the restricted map. This prevents repeated unfolding when assembling the map. The finite-family
proof needs 350000 elaboration heartbeats, locally scoped and explained, while
retaining the fixed 60-second compiler limit. The second reader removed two redundant
restriction-equality helper theorems and simplified their uses, avoiding repeated
elaboration of the same functor comparisons. No other existing module is adapted. This is a decomposition, not an
unconditional proof of the local finite-support theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_finite_free_local_support`
(node `lem-weil-pbc-module-finite-free-local-support`), by a complete finite-family
argument from the named one-section theorem.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_unit_local_support`
(node `lem-weil-pbc-module-unit-local-support`). This has only a unit source and
one section; its remaining argument is finite-subcoproduct stalk representation
and one shrinking, with no finite-family intersection, union or coproduct
assembly. Its source and complete proof in words are in its docstring and node.

The new theorem
`AlgebraicGeometry.Scheme.Modules.enlarge_restricted_unit_support`
(node `lem-weil-pbc-module-support-restriction-enlargement`) was initially left
open by the first worker and closed in second reading. Its proof is coproduct
extensionality, functoriality, and restriction of the existing equality; it has
no `sorry` and uses only `propext`, `Classical.choice`, and `Quot.sound`.

No sorry remains in the original module. The private finite-family and
categorical assembly helpers are proved. One original hole closed and one new
lower hole added: decomposition, net zero holes before closure accounting.
The parent still depends on `sorryAx` through the one-section theorem.

The empty family n = 0 gives W = U, empty support and vacuous coproduct
extensionality. Empty I and zero sections are admitted by the one-section
statement; there is no nonempty-index, finite-type or surjectivity assumption.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit` from the original module.
Its node `lem-weil-pbc-module-stalk-filtered-colimit` is no longer a direct
proof dependency of the parent, but remains needed through the one-section
lemma and is imported there. The candidate proof import `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`
was also removed: coproduct assembly uses the cofan equivalence already available
from the retained imports. Thus no module is claimed pruned from the targets'
import closure. The restriction-colimit dependency is retained and is realized
by Mathlib's left-adjoint instance for `overMap`. No unit statement or realized
unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The DAG's step described as elementary
contains the one-section germ representation and shrinking argument. The direct/iterated overMap identities needed for
support enlargement also required substantial elaboration work. The two separate
substeps are now exposed, and the algebraic restriction/enlargement substep is proved while finite intersection, union and coproduct assembly
are implemented in Lean. This does not move the full statement into either node.

The local `literature/blueprint` and `literature/stacks-project` material named
in the repository documents is absent on this machine. The cited Stacks Tags
01BB and 01AH were read directly at their official pages. LeanSearch returned
Internal Server Error; LeanFinder, Loogle, source grep and the blueprint-node
search found the relevant construction and assembly tools, but no complete
one-section local-support theorem. Neither source was changed.

## New nodes

`lem-weil-pbc-module-unit-local-support`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-module-unit-local-support.json`,
records the local finite support of one morphism out of the unit, from the first
paragraph of the proof of Stacks 01BB and the stalk-colimit assertion 01AH (2).
It belongs to the parent's chapter and unit and preserves the parent's blueprint
ancestor. Its Lean module is
`lean/Sheaf/AlgebraicGeometry/ModuleUnitLocalSupport.lean`. Three kinds of Mathlib
search are recorded, including the failed LeanSearch request. A second node, `lem-weil-pbc-module-support-restriction-enlargement`, is stated
in `lean/Sheaf/AlgebraicGeometry/ModuleSupportRestrictionEnlargement.lean`. It
records only the explicit restriction/enlargement equality for an existing
factorization, with no choice of a lift, neighbourhood or support. It has the
same chapter, unit and ancestor. LeanSearch failed; Loogle and source searches
found the basis identities and unit restriction isomorphism but no combined
statement. No change record is needed: no existing statement, definition or
public interface changes.

## Second reading by N4

1. **Statements and definitions.** Read the three delivered modules and compared
   the parent against the repository with `diff`. The signature of
   `exists_finite_free_local_support` is byte-for-byte identical, from `theorem`
   through the conclusion before `:=`. All three original public imports stay
   public. The new imports are plain proof imports. No existing public statement,
   definition, or visibility changed, and no change record is required. The private
   `direct_restrict_map` is a real construction by `overMap.map`, with no choice
   from an unproved existence theorem. Verdict: pass.

2. **Compilation and trust.** Compiled the whole three-module set using
   `lcompile.py --all`: restriction/enlargement 50.4 s, one-section support 13.3 s,
   parent 41.0 s, all without warnings or errors. The first dry run exposed a
   parent timeout; this was repaired by removing redundant equality/composition
   helpers and using `F.map_comp` and the explicitly typed restricted map directly.
   Scratch `#print axioms` checks show only `propext`, `Classical.choice`,
   `Quot.sound` for `enlarge_restricted_unit_support`; the parent and
   `exists_unit_local_support` also have `sorryAx`, as expected from the remaining
   named hole. Scanned every delivered file: no hollow definition, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern`. Verdict: pass with one
   explicitly reported split hole.

3. **Split statements, sources, and small cases.** Read official Stacks
   [01BB](https://stacks.math.columbia.edu/tag/01BB), first proof paragraph, and
   [01AH](https://stacks.math.columbia.edu/tag/01AH), clause (2). The one-section
   theorem isolates the lifting of one germ into a finite subcoproduct and
   shrinking for equality; it assumes a scheme, opens U contained in V, a basis
   type I, one unit map, and a point of U. It adds no finite-type, epimorphism,
   nonempty-support, or quasi-compactness assumption. Those hypotheses of the
   full 01BB lemma belong to later generation/compactness steps and are not
   needed for this local germ argument. Its complete docstring argument explains
   the finite-subcoproduct colimit, stalk representation, shrinking, and conversion
   through `unitHomEquiv`. Empty I gives the zero target; a zero section uses empty
   support; empty U has no x. The enlargement statement has only an existing
   supported lift, Z contained in W and U, and S contained in T; no new lift is
   chosen. Its proof was closed here, including the cases S empty and S=T.
   Independent LeanFinder search for a germ in an infinite coproduct represented
   locally by finitely many summands returned generators and germ-zero tools,
   but no local finite-support theorem. Loogle found `ιFree_freeMap`; source grep
   in Mathlib's module sheaf files and Stalks, the upstream module files and
   `lean/Sheaf` found only the relevant pieces and the existing parent theorem.
   Verdict: the remaining hole is strictly smaller than the item, true, needed,
   sourced, and not a renamed copy of it.

4. **Route, imports, and pruning.** Read the original proof dependencies,
   `module_stalk_filtered_colimit`, the restriction-colimit Mathlib leaf, and
   `dag/units/sk-thm-p1.json` including `realized`. The parent constructs the
   finite intersection and finite support union in Lean; it restricts each
   chosen one-section lift and includes its support using the now proved
   enlargement theorem. `factor_restricted_coproduct` uses the mapped free cofan,
   its colimit property and extensionality to assemble the map. For n=0 the
   intersection is U, the union empty and extensionality vacuous. Mathlib's
   `overMapPushforwardAdj` and left-adjoint instance supply restriction preserving
   the coproduct. The original direct stalk dependency is listed under No longer
   needed and retained through the one-section module; the other original proof
   dependencies remain. No realized unit statement or step was replaced or
   bypassed. No module is claimed pruned from the targets' closure. Verdict: pass.

5. **DAG agreement.** Checked all three node files against the actual Lean
   declarations, signatures and proof route. New nodes have matching declarations,
   complete sources and proof plans, searches, status, created/Lean records, parent
   chapter `sec-proper-base-change`, unit `sk-thm-p1` and blueprint ancestry.
   The parent uses the one-section and enlargement declarations; the latter is
   now proved. Corrected the parent proof step's inaccurate Mathlib colimit
   construction name to `Cofan.isColimitMapCoconeEquiv` and
   `isColimitOfPreserves`, and updated its proof-origin note to distinguish the
   remaining split hole from the proved algebraic substep. Verdict: pass.

Changes made: proved `enlarge_restricted_unit_support` without altering its
signature; removed redundant private `direct_restrict_map_eq` and
`direct_restrict_map_comp` and simplified their uses to repair the parent compile
time; corrected the parent node's proof text; updated hole counts and this report.
