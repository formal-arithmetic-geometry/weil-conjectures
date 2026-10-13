## What changed

Rebased onto the concurrent S1 landing, which had introduced
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core` without the
cover hypotheses. Corrected that false helper by restoring the two original cover
equalities, and replaced its hole by a reduction to two separate parts of its original argument. The main module
forms the bidegree component from the total summand inclusion and `c`, maps the
specified total cycle with `cyclesMap`, and proves its inclusion and homology-class
formulas by naturality. It extracts the three canonical module-comparison witnesses,
uses the ordinary external pairing comparison, and then identifies its ordinary
module cup with the scalar Ext external cup. Degree equality is eliminated by
substitution. A proved private `moduleCup_congr` helper handles equality of the
ordinary bilinear pairing inputs. Local irreducibility keeps derived cohomology
and pullback constructions folded during equality glue; explicit coefficient
modules fix the ordinary cup instances without unfolding those constructions. The original `picardScalarCech_externalCup` signature and all public imports are
unchanged. Only the newly landed core helper signature is corrected; the original
theorem now passes its existing cover equalities to the proved core.

Added `Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing` and
`Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison`, each with one named
public intermediate theorem. Their statements have different scopes: the first
uses ordinary module cohomology and a single bidegree pairing, with no scalar Ext
external cup or total map; the second involves no Cech complex or comparison at all.
The node copies describe this same route. Compilation of all three modules
passes without warnings using `lcompile.py --all` (12-15 seconds per main/ordinary
comparison module and about 5 seconds for the scalar comparison statement). The only choices made in the main proof
are comparison witnesses and the existing uniquely characterized module cup.

## Proved and sorry left

The existing main theorem `AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`
is proved from the corrected core, with its original signature unchanged.

Closed the hole in the corrected
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`
(node `lem-sc-picard-scalar-cech-external-cup-core`). This does not assert a proof
of the old false uncovered core statement. No sorry remains in the item.

Added exactly two holes:

- `AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing`
  (`lem-sc-picard-module-cech-external-pairing`).
- `AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison`
  (`lem-sc-scalar-external-cup-module-comparison`).

This is a decomposition of one upper hole into two strictly separate arguments,
not a claim of a fully axiom-free proof or positive net hole progress. Each new
hole is exactly `:= by sorry`, with its source and proof in words in its docstring.
Neither defines any data. Edge cases: zero coefficients and empty covers of an
empty scheme give zero classes; natural degree zero is the pulled-back section
tensor formula. Arbitrary covers need no comparison isomorphism or affine assumption.

## No longer needed

Removed the direct proof import `Sheaf.Paper.CechCupPullbackCompat` from the item.
It is still needed through `PicardModuleCechExternalPairing` for the ordinary
comparison argument, so this removal prunes no module from the target closure.
The original dependencies `def-sc-cech-refinement-cochain-map`,
`def-sc-cech-cup-product`, and `lem-sc-picard-cech-cup-pullback-compat` now belong to
the first intermediate node rather than the corrected core proof. The old core dependency `def-sc-field-linear-module-cohomology-operations` now
belongs to `lem-sc-scalar-external-cup-module-comparison`. Removed the redundant
direct public import `Sheaf.AlgebraicGeometry.ModuleCechComparison` from the new
ordinary comparison module: `Sheaf.Paper.ModuleCohomologyCupProduct` already
publicly imports it. No original mathematical
step or unit route is pruned; no whole module is claimed unnecessary.

## Where the brief, the DAG or earlier work was wrong

The existing ordinary Cech/module compatibility theorem does not directly identify
the scalar Ext operations with their ordinary module counterparts. This is already
step 3 of the parent's proof plan, but lacked a separate usable Lean interface.
The first new statement packages only the product-cover specialization of steps
1-2. The second packages only step 3. The concurrent core landing was wrong:
STATEMENT-DISPUTED (old version): without cover equalities the comparison witnesses
are unconstrained outside the chosen opens. Let X=Y be the disjoint union of two
copies of Spec k; choose U,V to be the first component and F=O_X,G=O_Y, in degree
zero. Extend factor sections by zero on the second component. Extend the product
section on (1,1) also to (2,2). All comparison conditions still hold after restriction
to the selected opens, for every resolution, but the product comparison of 1 tensor 1
has value 1 on (2,2) and externalCup of the factor extensions has value zero there.
Tags 01FD and 0FKV use open covers. Restoring the original cover hypotheses corrects
this error and leaves the enclosing theorem unchanged. The corrected core is true
and reduced by the actual proof; the old false claim is neither assumed nor proved.
There are no DAG citers of the old core on the fetched base. The only Lean user is
the item itself; its call is adapted. All 174 import descendants keep their existing
statements and definitions; no other module needs adaptation.

The correction is recorded in
`coord/changes/picardScalarCech_externalCup_core.md`. No Challenge signature or
definition changes, so target meaning is unchanged.

Local literature text is absent on this machine. Read the cited Stacks pages
01FD, 0FKV, 01F7 and 0BED online. The new proofs in words are marked agent-written
specializations of these diagrams. Searches found no matching Mathlib statement;
LeanSearch was unavailable, with that failure recorded by msearch.py.

## New nodes

`lem-sc-picard-module-cech-external-pairing` records the ordinary canonical module
comparison on a product-cover cycle with prescribed external front/back bidegree
coordinates. It is stated in `PicardModuleCechExternalPairing.lean`.

`lem-sc-scalar-external-cup-module-comparison` records agreement of scalar Ext
external cup and ordinary module cup of projection pullbacks. It is stated in
`ScalarExternalCupModuleComparison.lean`. Both nodes inherit the parent's chapter
and unit. Their proofs follow its route without changing the unit statement or steps.
The change record is `coord/changes/picardScalarCech_externalCup_core.md`.
The corrected existing core node records its statement correction and preserves
all non-owned fields. The parent node now uses that proved core; the core node
records the two-part comparison argument. New node statements are unchanged.

## Earlier second reading (a previous round; superseded)

The corrected core and unchanged target signature were checked against the
counterexample and compiled together with both strictly smaller intermediate
statements. The two remaining `sorry`s are exactly the named intermediate
arguments listed above; no `sorry` remains in the item theorem or corrected
core proof. The DAG copies, proof dependencies, and statement correction record
match the imports and declarations in the sandbox.


## Second reading by A4

1. **Interface check: pass with the declared correction.** Read the diffs against
   the repository's landed S1 version. The entire existing
   `picardScalarCech_externalCup` signature is byte-for-byte identical; both
   existing public imports stay unchanged. The only changed existing signature
   is `picardScalarCech_externalCup_core`, adding exactly the two cover equalities
   declared in `coord/changes/picardScalarCech_externalCup_core.md`. No definition
   or Challenge statement changes. Checked declaration uses by `rg`: only the
   enclosing theorem calls the core. Read the noncover counterexample against
   `IsModuleCechComparison`: its resolution equation restricts to the chosen
   opens and cannot determine extension on the other components. Restoring covers
   is a statement correction, not a proof of the old false uncovered assertion.

2. **Proof and trust check: pass as a decomposition.** Independently compiled
   all three delivered modules with `lcompile.py --all`, and compiled the main
   module again. Read the cycle-map inclusion calculation, homology naturality,
   extraction of canonical comparison witnesses, equality substitution in the
   bilinear cup, and degree transport. There is no hole in the main module; the
   two holes are exactly the named public lower statements listed above. There
   is no data definition added and no forbidden declaration or attribute.
   A scratch copy with `#print axioms` for all four public theorems compiled:
   each reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The chosen cup is uniquely specified by `exists_unique_moduleCupProduct`;
   comparison witnesses are supplied by hypotheses, not arbitrary unproved
   existence. The old main theorem was already proved on the S1 base; only the
   corrected core body is newly filled. This adds two lower holes for one upper
   hole and is not positive net hole progress.

3. **Lower statements: pass.** Read both full statements and their docstring
   proofs, their nodes, and the definitions of the scalar operations, module cup
   characterization, module Cech comparison and bidegree coordinates. The
   ordinary comparison is steps 1-2 alone and the scalar/module equality is
   step 3 alone: neither restates the total-cycle scalar assertion. Checked
   degree zero against the normalized tensor section formulas; for zero
   coefficients and empty schemes the classes vanish. An empty factor index
   family together with its cover equality forces that factor scheme to be
   empty. The statements assume no comparison isomorphism or affine cover.
   Read Stacks [01FD](https://stacks.math.columbia.edu/tag/01FD),
   [0FKV](https://stacks.math.columbia.edu/tag/0FKV),
   [01F7](https://stacks.math.columbia.edu/tag/01F7), and
   [0BED](https://stacks.math.columbia.edu/tag/0BED): these supply the ordinary
   naturality/cup argument; the scalar identification is the explicitly marked
   agent-written resolution specialization. Fresh LeanFinder searches for
   derived tensor compatibility under scalar restriction and for product-cover
   Cech cocycles gave only general sheaf/tensor or scheme-gluing declarations.
   Loogle found `HomologicalComplex.homologyMap_comp`; a fresh grep search
   `Cech.*tensor|tensor.*Cech` returned no Mathlib match. Searched project sources
   with `scalarCohomologyPullback`, `scalarCohomologyCup`, and
   `scalarCohomologyExtEquiv`: coefficient naturality and degree-zero formulas
   exist, but no arbitrary-degree module comparison closes either new hole in
   a few minutes. No further split is introduced.

4. **Route and pruning: pass after import cleanup.** The core uses the two
   genuine parts of the parent's argument, joined by proved homological algebra
   and witness equations. Proof-only imports in the main module are plain
   `import`. Removed the ordinary comparison module's redundant direct public
   `ModuleCechComparison` import, already available publicly via
   `ModuleCohomologyCupProduct`. Retained its plain `CechCupPullbackCompat`
   import for its stated proof plan. Completed `No longer needed` for the old
   core's scalar-operations dependency as well as the old parent's refinement,
   cup and comparison dependencies. These move below the new intermediate
   nodes; no module leaves the target closure. Read
   `dag/units/sk-prop-av-cube.json`: this auxiliary node is not a realized unit
   statement or step, and its decomposition changes no unit route or realization.

5. **DAG check: pass after citation repair.** Compared all four Lean signatures
   to their `lean.statement` records, byte-for-byte: all match. Each
   `proof_deps` is exactly the union of its proof steps' `uses`. The parent uses
   the corrected core; that core uses the ordinary comparison and scalar
   comparison, bidegree/component and scalar-comparison interfaces, and the
   unique module cup. The two new nodes have their required source, searches,
   chapter/unit, creation, blueprint and Lean fields. Read the correction
   record and `statement_change` against the original core. Corrected the
   scalar comparison node's copied Cech source tags to 01F7/0FKV/0BED, matching
   its docstring and cover-free argument.

Second reading changed: one redundant public import removed, the scalar node's
source citation corrected, the dependency-movement accounting completed, and this
independent five-point review added. No proof or statement required further repair.
