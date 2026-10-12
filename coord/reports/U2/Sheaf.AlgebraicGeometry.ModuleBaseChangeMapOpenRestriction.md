## What changed

Completed `AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap_open_restriction`
without changing its signature, definition of the base change map, visibility, or
existing public imports. Added two ordinary proof imports:
`Sheaf.AlgebraicGeometry.ModuleBaseChangeOpenSquareIso` and
`Sheaf.AlgebraicGeometry.ModuleBaseChangeSquareRestrictionCommutes`.

The first new module proves the single-square open exchange map is an isomorphism.
It compares the chosen tensor adjunctions with the Mathlib restriction adjunctions,
identifies the two inverse-image opens, proves the restriction mate sectionwise
invertible, and transports it through uniqueness of left adjoints.

The second new module proves the commutation equality for arbitrary restriction
squares, without openness assumptions. It applies Mathlib mate/pasting identities, discharges the sectionwise
right-adjoint equality directly using `Functor.map_comp` and uniqueness of morphisms
between opens, then compares the two outer squares by equality transport. The
duplicate private `pushforwardSquare_pasting` declaration has been removed. Its public signature spells out the original
base change formula as a local let, so it does not import the item or introduce a
second public definition. The main theorem applies these results, infers that the
comparison composites are isomorphisms, and proves the final equivalence by
isomorphism cancellation.

Updated the item's proof plan and supplied a node for each new module. Sources were
read in the obtained Stacks checkout at `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`:
Sheaves Lemma 00A0 and Cohomology Remarks 0ATL/0ATM. The source paths in the nodes
refer to the project's standard literature layout. The unit route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap_open_restriction`
(node `lem-weil-pbc-module-base-change-map-open-restriction`).

Also proved, with complete Lean proofs:
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap_open_square_isIso`
(node `lem-weil-pbc-module-open-square-isiso`) and
`AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap_square_restriction_commutes`
(node `lem-weil-pbc-module-square-restriction-commutes`).

No holes added; no sorry remains in any delivered module. This is a proof,
not a decomposition into new unproved statements. The existing naturality proof
and the base change definition are retained verbatim.

## No longer needed

No existing import was removed: the item's two original public imports support
its statements and definition.

The planned direct dependency `lem-weil-pbc-module-base-change-map-pasting`
(`Sheaf.AlgebraicGeometry.ModuleBaseChangeMapPasting`) is no longer needed by this
proof and has been removed from the item's proof_deps. The coherence helper relies directly on Mathlib mate calculus and
`Functor.map_comp`; it declares no duplicate `pushforwardSquare_pasting` theorem. The original restriction nodes are still needed
transitively by the single-square proof, and therefore are not pruned:
`lem-weil-pbc-module-restriction-open-immersion-colimits` and
`lem-weil-pbc-open-immersion-module-pullback-restriction`.

The other old direct dependencies are now reached through the proved helpers:
`def-pc-scheme`, `def-weil-open-immersion`,
`def-weil-sheaf-of-modules-category`, and `def-pc-module-pullback`.
They are omitted from the item's direct proof_deps because the new proof uses the
helper declarations; none is claimed pruned from the import closure. No claim is made that the pasting module
leaves the entire targets' closure: other importers may still need it.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had an unfinished declaration, redundant specialized
naturality, unregistered holes, an incomplete report, and no valid delivery.
It was replaced from the repository's current module; the redundant helper and
unfinished files were removed from the sandbox delivery.

The planned pasting module imports this item. Importing it here would create an
import cycle, despite its pasting proof being complete. The independent coherence
helper avoids the cycle without changing any other existing module.

Repair of return point 1: removed the duplicate private
`pushforwardSquare_pasting` theorem from the coherence module. The corresponding
step now uses Mathlib `Functor.map_comp` directly after evaluating on a module and
an open; equality of the paths follows from thinness. The existing scheme-specific
theorem in `ModuleBaseChangeMapPasting` is private, and importing that module here
would create a cycle through this item. No declaration was renamed to hide the
duplicate, no existing signature was changed, and no import-check tool was changed.
Updated the coherence node to describe this direct use of the general theorem.
The second-reading section below records the returned version; a fresh second
reading is needed for this repair.

LeanSearch returned Internal Server Error for both component searches. The
search records mark it unavailable without inventing a mathematical verdict;
LeanFinder, Loogle and local source searches were available.

## New nodes

`lem-weil-pbc-module-open-square-isiso`:
`lean/Sheaf/AlgebraicGeometry/ModuleBaseChangeOpenSquareIso.lean`.
The full-inverse-image open-square isomorphism step alone, proved sectionwise.
The edge cases include empty opens and isomorphisms, and the proof requires no
quasi-coherence hypothesis.

`lem-weil-pbc-module-square-restriction-commutes`:
`lean/Sheaf/AlgebraicGeometry/ModuleBaseChangeSquareRestrictionCommutes.lean`.
The pasting/transport equation alone, proved for arbitrary commuting squares;
there are no IsIso conclusions or openness assumptions in this component.

No interface change or forced adaptation; no change record is needed.


## Earlier second reading (a previous round; superseded)

1. **Existing interfaces: pass.** Compared the delivered item against the current
repository file with `diff -u`. The only differences are two ordinary proof imports
and replacement of the final `sorry`. The full signatures of `moduleBaseChangeMap`,
`moduleBaseChangeMap_naturality`, and `moduleBaseChangeMap_open_restriction`, the
base-change definition, the naturality proof, and public imports remain verbatim.
The other two modules are new, with no adaptation of any existing module.

2. **Proof and construction: pass.** All three modules compile locally without
warnings through `lcompile.py`. Read every proof, including the private core and
mate/pasting lemmas. There is no sorry or prohibited declaration in the delivered
sources. Scratch-copy `#print axioms` checks cover the base-change definition,
existing naturality, final theorem and both public helpers; results are recorded
below. The chosen adjunction comes from the existing theorem with its specified
unit; no arbitrary object is extracted from mere existence. leftAdjointUniq
transports between adjunctions of the same right adjoint, preserving the unit;
this correctly handles the choice in the definition.

3. **New components: pass.** Neither new theorem is left open. The single-square
helper requires exactly the two open immersions, commutation and full image
condition needed for invertibility; it has no affine or quasi-coherence condition.
Checked its image equality argument: hX gives a preimage y and injectivity of jU
forces fU(y)=w. Empty opens and the empty source still give equal opens; identity
immersions give the identity restriction comparison. The coherence helper needs
only the six commuting equalities and no openness. Its two pasting identities
have the correct order of composition comparisons; equality elimination proves
transport compatibility, then epi/mono cancellation gives the equation. Identity
squares reduce to adjunction and composition coherence, including for the zero
module. These are separate strict components of the target, with complete source
proof docstrings and individual nodes, rather than a renamed target.

Read Sheaves Lemma 00A0 (lemma-j-pullback), including the explicit module variant,
and Cohomology Remarks 0ATL/0ATM (remark-compose-base-change and its horizontal
version) in the obtained Stacks sources. The underived calculations implement the
restriction and mate arguments these sources describe. Independently searched
LeanFinder for exchange transformations restricted to inverse-image opens,
Loogle for CategoryTheory.mateEquiv_hcomp, and `rg` in lean/ and pinned Mathlib's
Modules/Sheaf and Adjunction/Mates. Searches find restriction composition and
mate calculus, used here, but no independently importable theorem for either
complete component. The existing ModuleBaseChangeMapPasting imports this item,
so reusing its private argument avoids an actual import cycle.

4. **Route, imports and pruning: pass.** The proof uses Mathlib sectionwise
restriction formulas and mate calculus directly, then the two fully proved
components. Each public import is required by a public signature or definition:
tensor pullback/adjunction for both helpers and conjugateIsoEquiv for coherence.
The item's two new imports are ordinary proof imports. No removable delivered
import was found. Checked sk-thm-p1.json realized: none of the removed direct
edges is a unit's realized statement or step, and no chapter/unit route changes.
The report now explicitly accounts for every old direct proof dependency:
restriction results and definitions remain used through the helpers; only the
pasting-node dependency is replaced by its independent Mathlib mate calculation.
No whole-library module pruning is claimed.

5. **DAG agreement: pass.** Compared the item's node with the repository node:
only proof, proof_deps and proof_origin differ. Step 1 uses the open-square helper;
step 2 uses both helpers; step 3 is elementary isomorphism cancellation. The new
nodes record the actual restriction/unit comparison and mate/pasting/transport
arguments, their union of dependencies, source, searches, provenance, unit,
chapter and Lean declarations. The restriction nodes' recorded Mathlib matches
are precisely restrictAdjunction and unit_leftAdjointUniq_hom_app used in the
open-square proof. The mate nodes' Mathlib matches include mateEquiv_hcomp and
both conjugate-whiskering lemmas used in coherence. No unsupported Lean/DAG edge
or missing new node was found.

Second reading changed only documentation: added the missing blueprint tags to
both new module docstrings, expanded the old-dependency accounting above, and
wrote this independent review. No mathematical or proof repair was necessary.

Axiom results: all five checked declarations depend exactly on `propext`,
`Classical.choice`, and `Quot.sound`; none uses `sorryAx` or another axiom.
Scratch copies were removed before delivery.


## Second reading by U2

Independent reading of the repaired delivery, 2026-10-13; the earlier reading above
is not relied upon.

1. **Interfaces: pass.** Read the complete diff against the repository item. Only
   two ordinary proof imports and the final proof body differ. All existing
   declaration signatures, visibility, public imports, the base-change definition,
   and the existing naturality proof are byte-for-byte unchanged. Both other
   delivered modules are new; there is no forced adaptation or interface change.
2. **Proof: pass.** Read every delivered proof and compiled all three modules in
   dependency order using lcompile.py: clean, without warnings. Independent
   scratch-copy #print axioms checks for moduleBaseChangeMap, its naturality and
   open-restriction theorems, and both public helper theorems report exactly
   propext, Classical.choice and Quot.sound. No sorryAx occurs; no holes or forbidden
   declarations occur in the sources. Scratch copies were removed. The only chosen
   adjunction is the existing canonical tensor adjunction with its specified unit;
   the argument compares adjunctions through leftAdjointUniq and its unit equation.
   It introduces no arbitrary witness from an unproved existence statement.
3. **Components and reuse: pass.** No statement is split off with sorry. The two new
   proved statements separately establish single-square invertibility and general
   restriction coherence, strictly parts of the original argument. Checked empty
   opens, empty source, identity immersions and the zero module: the equal-open
   argument and functorial mate identities still apply without extra hypotheses.
   Read Stacks Sheaves lemma-j-pullback and both Cohomology composition remarks.
   Fresh LeanFinder search for Beck-Chevalley on inverse-image open subsets finds
   restriction adjunctions and composition, already used, but no complete helper.
   Fresh Loogle search for mateEquiv with TwoSquare.hComp finds mateEquiv_hcomp,
   mateEquiv_vcomp and mateEquiv_square. Local searches in Sheaf, WeilConjectures
   and pinned Mathlib likewise find no independent complete replacement. The
   existing moduleBaseChangeMap_pasting imports this item, so importing it here
   creates a cycle. Specifically rechecked the return: the duplicate declaration
   pushforwardSquare_pasting is absent; the right-adjoint equality now follows
   directly from Functor.map_comp and thinness within the mate argument.
4. **Route and pruning: pass.** The main proof applies the two components and
   cancels isomorphisms. Public imports supply signature/definition constants;
   the two added item imports are proof-only. No unused delivered import found.
   Every removed old direct proof dependency is accounted for in No longer needed:
   definitions and restriction results remain available through the helpers;
   the planned module-pasting edge is replaced by direct Mathlib mate calculus.
   Checked sk-thm-p1 realized: none of those edges realizes a unit statement or
   step. The chapter and unit route stay intact. No module is claimed removed from
   the whole targets import closure.
5. **DAG: pass.** The existing node differs only in proof, proof_deps and
   proof_origin. Its proof follows the actual three-step proof. Both new nodes
   give their complete public Lean statements, sources, searches, provenance,
   chapter, unit, and dependency unions; the restriction and mate Mathlib leaves
   match the constants actually used. Checked the repaired coherence node against
   its sectionwise Functor.map_comp calculation and equality-transport proof.

Second reading changed only this report and added independent search records.
No Lean or DAG repair was necessary after the first worker's return repair.
Closed original holes: moduleBaseChangeMap_open_restriction (one of one remaining
in the item). Added holes: none. Two additional helper theorems are fully proved.
