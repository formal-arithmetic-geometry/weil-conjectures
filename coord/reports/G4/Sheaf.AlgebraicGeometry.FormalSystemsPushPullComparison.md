## What changed

Proved `AlgebraicGeometry.exists_formalSystemsPushPull_comparison` from an existing
ideal-power pullback-image theorem and one new, strictly partial lifting theorem.
The item's signature and existing public imports are unchanged.

The proof constructs kappa componentwise using `cokernel.desc`. It proves that the pushed
quotient projection kills J^(n+1) by the pullback-image identity, multiplication naturality
for the adjunction counit, and the adjunction hom-set equivalence. It proves every
transition equation by cancellation of the quotient projection. It constructs gamma
from the unit and beta and proves its naturality. Finally it obtains alpha from the
formal-functions lifting theorem and evaluates its equality at every level.

Added proof-only imports of `ModulePullbackIdealPowerProductImage`,
`CoherentFiniteTypeLocallyNoetherian`, and the new `FormalCompletionPushforwardLift`.
Updated the comparison node's proof, proof_deps and proof_origin to match this route.
The second reading added the lifting node's planned dependencies as proof-only imports
of its new module, as required by the stage-3 dependency-import convention.

Both modules compile with the project's local compiler. The source was read at Stacks
Tag 088B; the local literature copy is absent on this machine. LeanFinder returned only
adic projection identities, Loogle confirmed the cokernel API, LeanSearch was unavailable
(Internal Server Error), and Mathlib/source grep found no direct lifting result.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_formalSystemsPushPull_comparison`
(node `lem-weil-pbc-formal-systems-push-pull-comparison`). No sorry remains in the item.

Added one hole: `AlgebraicGeometry.formalCompletion_pushforward_lift`, in
`Sheaf.AlgebraicGeometry.FormalCompletionPushforwardLift`, node
`lem-weil-pbc-formal-completion-pushforward-lift`. This is a decomposition, not a
sorry-free proof: one upper hole closed and one lower hole added, net zero for these
holes. The existing imported `AlgebraicGeometry.modulePullbackIdealPowerProductImage`
now has a proof in the repository snapshot; its existing node is not changed or
duplicated by this delivery. This does not claim that its transitive axioms are closed.

The new lemma takes kappa with its already-proved quotient identities and arbitrary
gamma as input. It supplies only the formal-functions lift alpha. It removes the
adjunction and beta from this step. This is strictly the limit-and-gluing part of the
argument; the quotient construction and adjunction-map compatibility are actual Lean
proofs in the item, not hypotheses repackaged as a restatement.

## No longer needed

No existing import was removed. None of the unit's realized steps was bypassed.
The original direct reference to `ModulePullbackIdealQuotient` is replaced by the more
precise `ModulePullbackIdealPowerProductImage`; the former remains a dependency of the
latter and is therefore not claimed as globally pruned. Formal functions, the affine
coherent-formal-module equivalence, affine tilde/sections, affine ideal-products, and
formal restriction remain needed by the new lifting node. No module is claimed pruned.
An exploratory `Mathlib.CategoryTheory.Adjunction.Limits` import was removed after
compilation showed that the remaining imports suffice.

For completeness, these six old direct `proof_deps` are absent from the comparison
node's new direct list:

- `lem-weil-pbc-module-pullback-ideal-quotient`: replaced by the ideal-power image
  calculation; retained below its existing dependency chain.
- `lem-weil-pbc-theorem-formal-functions`: moved to the new lifting node.
- `lem-weil-pbc-coherent-formal-modules-affine`: moved to the new lifting node.
- `lem-weil-pbc-affine-tilde-gamma-adjunction`: moved to the new lifting node.
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`: moved to the new lifting node.
- `lem-weil-pbc-formal-systems-pullback`: moved to the new lifting node.

These are direct dependency replacements, not globally pruned modules.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan cited the quotient theorem at level one,
whereas the recursive ideal-power image theorem exactly matches the positive powers
used by `formalModuleQuotient`; it supplies the annihilation calculation without new
statements. The lifting interface needed by the second and third steps did not exist.

Edge cases for the new statement: J=0 gives constant systems and ordinary maps; J=1
gives zero systems; zero modules, zero gamma, empty affine opens, and f=id satisfy the
limit construction. It asserts no termwise invertibility of kappa. On nonseparated Y,
intersections of affine opens are covered by smaller affine opens, not assumed affine.
The completed-ring linearity and uniqueness arguments are written explicitly in its
node and docstring. The new statement needs no beta isomorphism: the source's limit
construction uses only the compatibility and linearity of gamma.

## New nodes

`lem-weil-pbc-formal-completion-pushforward-lift`: the formal-functions lift through a
supplied quotient comparison. Its module is
`lean/Sheaf/AlgebraicGeometry/FormalCompletionPushforwardLift.lean`. Its source is
Tag 088B, the construction from lim gamma. Its proof records affine formal functions,
completed scalar linearity, quotient descent, uniqueness, and gluing. It inherits the
comparison node's chapter/unit and blueprint ancestry. Searches of the full blueprint
by "088B" and "formal pushforward comparison" found no existing blueprint statement.
Change record: `coord/changes/formalCompletionPushforwardLift.md`.

## Second reading by G4

1. Compared the entire item with the repository using diff and the declaration parser:
   its only existing declaration has an identical signature and visibility; no
   definition or target changed. The added imports are proof-only. The added theorem
   and its new-module change record agree; there are no forced adaptations. Verdict: pass.
2. Compiled both files in dependency order using lcompile.py. Reviewed the cokernel
   construction, ideal-image annihilation calculation, adjunction conversion, both
   naturality proofs, and the componentwise final equality. No forbidden declaration,
   hollow definition, or arbitrary witness used as data was added. The only direct
   sorry is the named lifting theorem. Explicit scratch #print axioms checks and the
   delivery probe are recorded below. Verdict: pass with the reported lower hole.
3. Read the lifting statement, its complete docstring, and node against Stacks Tag
   088B's first-half construction. An arbitrary compatible gamma gives a completed
   scalar-linear limit map, hence quotient maps and a unique locally gluable lift;
   neither invertibility of beta nor an exceptional ideal is used in this portion.
   Checked zero/unit ideals, zero modules, identity f, and empty affine opens. Searched
   afresh with LeanFinder (adic coherent system/direct image/inverse limit), Loogle
   (cokernel.desc), launcher grep (formalCompletion_pushforward/pushforward_lift/lim
   kappa), and repository rg with alternate terms. The matches supply completion or
   cokernel APIs, not this sheaf-level lifting statement. This is strictly the lifting
   portion of the argument; constructing kappa and gamma is actually proved. Closing
   the affine-equivalence, affine restriction, and gluing bridge is not a short proof
   repair, so the one lower hole is retained. Verdict: pass, genuine decomposition.
4. Read the old and new proof_deps and dag/units/sk-thm-p1.json realized fields. No
   unit-level statement or realized step is bypassed; the local formal-functions and
   affine reconstruction route stays in the lower lifting node. Completed the explicit
   old-dependency inventory above. Added the planned proof-dependency imports to the
   new lifting module; existing public imports remain unchanged. Verdict: pass.
5. Compared both node records with their Lean declarations and proof routes. The old
   node's changes are confined to proof, proof_deps and proof_origin; its Lean record
   and statement are unchanged. The new node has its source, searches, ancestry,
   chapter/unit, complete statement and verbatim Lean signature. Its dependencies are
   exactly the union of its proof steps. Verdict: pass.

Second-reading changes: added proof-only imports for the lifting node's stated route;
completed the six-node old direct dependency inventory; corrected the stale assertion
that the existing ideal-power image theorem still had a direct sorry. No proof body,
statement, definition, node, or change record required repair. One original hole closed,
one lower hole added: decomposition with net zero, no global module pruning claimed.

Validation: both final modules compiled without diagnostics (2.0 s and 3.9 s).
Explicit #print axioms on scratch copies of both declarations returned exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the latter is expected
from the retained named lifting hole and open imported dependencies. Scratch copies
were removed before delivery.
