## What changed

Implemented scalarExternalCup_moduleComparison by unfolding externalCup, applying
scalarCup_moduleCup_compatibility on the product, and applying
scalar_moduleCohomologyPullback_comparison to both projection pullbacks.
The assigned module and both prerequisite modules are absent from this checkout;
their signatures were reconstructed verbatim in meaning from the existing DAG records.
All three modules compile together using lcompile.py.

## Proved and sorry left

Completed scalarExternalCup_moduleComparison (one of one planned item holes).
The current base omits the module, so this restores an existing decomposition rather
than claiming a newly achieved positive net ledger reduction.
Restored two named holes in the two existing planned prerequisite nodes:
- scalar_moduleCohomologyPullback_comparison
  (lem-sc-scalar-module-cohomology-pullback-comparison).
- scalarCup_moduleCup_compatibility
  (lem-sc-scalar-cup-module-cup-compatibility).
This is a decomposition through the two existing comparison nodes, not an independent
proof of the resolution comparisons. No further nodes were introduced.

## No longer needed

Both planned comparison lemmas are used; no module import is removed.
The cup-comparison node no longer needs the proof dependency
`def-weil-pbc-module-cohomology-fmap`: its statement and resolution argument
involve no pullback. That dependency edge was already removed by the first worker
but omitted from this report. The main external comparison still uses that node
through moduleCohomologyPullback, so no module leaves the target import closure.

## Where the brief, the DAG or earlier work was wrong

The assigned module and both prerequisite modules are absent from the supplied checkout,
although their DAG nodes contain full Lean signatures. Their interfaces are realized
in this sandbox without changing their meaning. The target combines the two independent
comparisons and does not duplicate either one.

The dedicated handoff in coord/returns/G3.md records an earlier duplicate-instance
collision between ModuleCupNaiveDerivedCompatibility and
GlobalTensorPullbackMonoidalNormalization. The repair restores all three withdrawn
modules together, preserving the original recorded signatures and docstrings.
Both failed modules now compile against the canonical ModuleCohomologyCupProduct
import in the current build; the delivery tool also runs its axiom/sorry probe.
The dependent external theorem is included together with both comparison modules,
addressing each importer failure listed in the handoff. No forced adaptation of
an existing module is needed: these three sources are absent on the delivery base.

Change record: coord/changes/scalar-external-cup-module-comparison.md.
Searches: LeanFinder returned only unrelated group-cohomology results; Loogle did
not know IsModuleCupProduct; Mathlib grep found no scalar/module cup comparison.
The unit record sk-prop-av-cube has no realized nodes to bypass, and the planned
scalar pullback/cup route is retained. Empty schemes, zero coefficients, and
natural degree zero require no exceptions in either comparison statement.


## Second reading by G3

1. Interfaces: all three repository source paths are absent, as recorded in the
   dedicated repair handoff. Compared every restored theorem signature with its
   repository DAG lean.statement: the external theorem agrees byte for byte;
   the two prerequisites agree after whitespace normalization only. All field,
   scheme, morphism, coefficient, natural-degree, cup, characterization, and class
   parameters are retained. No existing definition or target was changed.
2. Proof: compiled all three modules together in import order using lcompile.py;
   all pass without warnings. The main proof unfolds externalCup, applies cup
   compatibility, and substitutes scalar/ordinary pullback comparisons for both
   projections. The second projection uses pullback.condition.symm in the correct
   direction. There are precisely the two reported named theorem sorries, no
   definitions or forbidden declarations in these files. A scratch #print axioms
   check passed for all three declarations: only propext, Classical.choice,
   Quot.sound, and sorryAx (the open prerequisite/imported statements).
   Delivery also checks every declaration with its axiom/sorry probe.
3. Prerequisites: these are existing recorded split nodes restored after withdrawal,
   not newly invented statements. Pullback comparison concerns a single morphism;
   cup comparison concerns a single scheme without pullback. Each is a strict part
   of the external-product argument, and each docstring specifies the resolution,
   evaluation-at-1, and transport argument. Degree zero gives the ordinary section
   pullback and tensor pairing; zero coefficients and empty schemes give zero
   classes. No flatness or quasi-coherence is assumed or needed: the scalar inverse
   image is exact over a field and coefficients map to tensor pullback. Additional
   searches for derived-functor/Ext naturality and resolution cups found generic
   Ext composition/map lemmas, not either comparison theorem. Inspected the scalar
   operation definitions, ModuleCohomologyFMap, IsModuleCupProduct, and the related
   PicardExternalCupCochain linearity lemmas; none supplies either remaining proof.
4. Route and pruning: the main proof directly composes the two planned comparisons.
   Its public imports provide names in the signature; its two comparison imports
   are correctly proof-only. The prerequisite imports supply their signatures.
   The unit sk-prop-av-cube has empty realized statement/step arrays, and no unit
   route is bypassed. Corrected No longer needed to record the already removed
   cup-node pullback dependency; no module is pruned from the import closure.
5. DAG: opened and compared all three nodes. The main proof_deps is exactly the
   union of the two application steps, including the operation definitions. The
   prerequisite nodes retain the existing resolution-comparison plans and matching
   Lean records. Updated the main proof and proof_origin to describe the actual
   reduction rather than presenting the still-open resolution arguments as done.

Second-reading changes: report pruning correction, this independent review, and
main-node proof/proof_origin synchronization. Lean statements and proof bodies
needed no repair. One assigned theorem body is closed conditionally on two
restored prerequisite holes; this is a restoration/decomposition, not a claim of
positive net ledger progress.
