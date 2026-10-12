## What changed

Repaired the returned duplication finding without changing any existing public signature
or adapting another module. The item now has two fully proved private helpers with genuinely
more general statements: `constantModule_constructible` applies to every finitely generated
Lambda-module, and `finite_open_constantModule_stalk` applies to every module finite as a set.
Neither statement mentions a quotient or a natural number. The main proof specializes them
to `Lambda/(ell)`. The third duplicate, `open_constantModSheaf_constructible`, is removed:
the proof uses the existing `Scheme.IsConstructibleSheaf.openImmersionLowerShriek` directly.

The main theorem still combines source constructibility and finite geometric stalks with
`Scheme.isConstructibleSheaf_lowerStar_of_finite_stalks`. Its statement and public imports
are unchanged. Proof-only imports supply the closed complement, constant and open stalk
formulas, Noetherianity, and the finite-stalk module direct-image step.
The incomplete shared-helper extraction found in the sandbox is removed, including its
adapted `NormalizationMonoProperties`, three helper modules/nodes and change record.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.finite_pushforward_open_constantModSheaf_constructible`
(node `lem-weil-pbc-finite-pushforward-open-quotient-constant`). The generalized private
helpers `AlgebraicGeometry.constantModule_constructible` and
`AlgebraicGeometry.finite_open_constantModule_stalk` have complete proofs.
No sorry remains in the item module.

One lower hole is added:
`AlgebraicGeometry.Scheme.isConstructibleSheaf_lowerStar_of_finite_stalks`, node
`lem-weil-pbc-finite-pushforward-finite-stalk-module`, in
`Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule`.
This is a decomposition: one original hole closed, one strictly lower hole added.
The lower statement concerns direct image of an already constructible module sheaf with
finite stalks; it contains neither an open immersion nor a quotient constant.

The generalized helpers include zero modules and empty schemes/opens. The constructibility
helper assumes finite generation, while the stalk helper needs only finiteness as a set;
these are separate hypotheses and both hold for the quotient used here.
The direct-image statement was checked in the earlier delivery on the empty source/target,
zero sheaf and coefficient ring, identity and closed immersion cases. It is unchanged.

## No longer needed

Removed the three quotient-specialized private declarations duplicated from
`NormalizationMonoProperties`. Its module is not imported: it imports this item, so that
would create a cycle. Its existing private helpers and all public declarations remain
unchanged in the library. No mathematical node or module is claimed globally pruned.

Removed the item's direct proof-only import of
`Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian`; that dependency is
still imported by the new finite-stalk module lemma. Thus
`lem-weil-pbc-finite-pushforward-constructible-noetherian` remains needed transitively,
as do `lem-fin-extension-by-zero` and `lem-weil-pbc-extension-by-zero-stalks`.
The provisional shared-helper modules and nodes are not part of this delivery.
All other proof-only imports in the item are used; its public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied three existing private statements word for word. The repair
uses the permitted generalization route for two of them and directly uses the existing
open-extension theorem for the third. Importing the private declarations' owner cannot
solve the problem because they are private and its module depends on this item.
No forced adaptation or existing interface change is needed.

The original DAG's abelian finite-direct-image dependency cannot directly establish
module constructibility. The finite-stalk module interface records the missing module
refinement step. The parent node's proof now follows the actual generalized helpers and
their quotient specializations; the unit route `sk-thm-p1` is preserved.

The local literature blueprint files are not present. The existing DAG carries the
normalization argument and its source reference. Stacks Tag 095R was read online:
it assumes finite presentation and Noetherian coefficients in its module clause;
the new lemma obtains these by the Noetherian base and a finite quotient of Lambda.
The agent-formulated finite-stalk generalization and refinement proof are explicitly
marked as such in the new node. The unit route `sk-thm-p1` is preserved. The new module imports both stated mathematical
proof dependencies (`ConstructibleModuleUnderlyingSets` and
`FinitePushforwardConstructibleNoetherian`) as proof-only imports.

Searches: LeanFinder returned scheme constructible-image and finite-type module-sheaf
results, not this theorem. Loogle did not know `IsConstructibleSheaf`; Mathlib grep found
no direct-image constructibility match. LeanSearch returned Internal Server Error,
recorded as unavailable. Project searches found the abelian finite-pushforward theorem,
closed-immersion pushforward, and finite-etale locally constant module pushforward.
None states the required finite non-etale arbitrary-ring module implication.
The imported blueprint `lem-fin-finite-morphism` assumes a finite-type field base and
also asserts higher direct-image vanishing; it has no usable Lean declaration.

## New nodes

`lem-weil-pbc-finite-pushforward-finite-stalk-module` is the single new node retained from
the returned delivery. Its new module has one public theorem with exactly `:= by sorry`,
its source and a complete proof in words. No new holes are added by this repair.
There are no statement/definition changes, forced adaptations or change records.

## Second reading by T2

1. Compared both delivered modules with the repository. The item retains its existing
   public theorem signature, variables, universes, public imports and docstring byte for
   byte; changes are its proof, proof-only imports and two new private proved helpers.
   The other module is new. There are no definition changes, change records or adaptations.
   Verdict: no existing mathematical interface changed.

2. Compiled the two-module set in import order with lcompile.py: both compile without
   warnings or errors. The sole remaining sorry is the named public theorem
   `Scheme.isConstructibleSheaf_lowerStar_of_finite_stalks`, with its matching node and
   source/proof docstring. No definitions or forbidden declarations occur in the delivery.
   Scratch-copy #print axioms checks show only propext, Classical.choice and Quot.sound
   for each private helper, and those plus sorryAx for the item and the new theorem.
   Verdict: genuine checked reduction, not a completed sorry-free result.

3. Read Stacks Tag 095R (https://stacks.math.columbia.edu/tag/095R) and the actual
   constructibility definitions and dependency modules. The new theorem is its finite-stalk
   arbitrary-coefficient generalization: finite source trivializations give a finite list
   of finite modules, whose annihilator intersection has finite quotient ring. Every
   geometric point lifts to a cover member; empty members can be discarded. Conservativity
   then shows the ideal kills the sheaf. Forgetting and finite abelian direct image give
   finite-set strata; refining for the finite quotient ring's finitely many operations
   recovers module strata. Finite over a Noetherian target supplies the required source
   Noetherianity and finite presentation. No arbitrary data is chosen in Lean from an
   unproved existence statement. Checked empty source/target, zero sheaf/ring, identity,
   finite closed immersion, and a non-etale finite map: no extra hypothesis is required.
   The remaining theorem does not restate the item: source constructibility and finite
   stalks are its inputs, both established separately by complete Lean proofs here.
   Its docstring supplies the full mathematical reduction. Searched project/upstream
   constructibility files and Mathlib with lowerStar/constructibility and finite-stalk
   terms, and independently ran LeanFinder with a finite-stalk module preservation query.
   Results concern constructible scheme images, abelian pushforward, finite-etale locally
   constant pushforward, closed immersions, or embeddings into finite pushforwards;
   none states this theorem. No split-off hole can be closed by these existing interfaces
   in a few minutes. Verdict: true, needed lower statement; one-for-one decomposition.

4. Read the item from the top: identity-cover constancy and the constant geometric-stalk
   isomorphism prove the finitely generated constant-module helper; the open stalk formula
   identifies inside stalks with M and outside stalks with zero. The existing open-extension
   theorem directly gives source constructibility. This is a real reduction before the
   finite-direct-image hole. The generalized helpers avoid the quotient-specific private
   duplicates in NormalizationMonoProperties. Monoidal.isConstructibleSheaf only saves the
   trivial-stratification final line while adding a much larger import; the present direct
   argument is appropriate. Each added item import supplies declarations explicitly used
   by those proofs; the new theorem imports its planned module-underlying-set and abelian
   direct-image dependencies privately. The old direct dependency
   `lem-weil-pbc-finite-pushforward-constructible-noetherian` is no longer directly used
   by the item, but remains needed through the new theorem, so no module is globally
   pruned. Read dag/units/sk-thm-p1.json realized: none of its required step nodes is
   bypassed or removed; normalization and the curve route remain intact.
   Verdict: imports and pruning report match the reduction, unit route retained.

5. Compared the parent node's three proof steps with the Lean: constant source plus
   open extension, the two open-stalk cases, then application of the finite-stalk theorem.
   Its proof_deps and proof_origin describe those steps. The new node's Lean signature
   matches its module; its finite-ring reduction explains why the imported underlying-set
   theorem's finite-ring assumption is available, and its remaining refinement recovers
   the exact Scheme.IsConstructibleSheaf conclusion. Source, searches, creation, blueprint,
   chapter/unit and Lean records are present. Existing node edits are confined to the
   permitted proof fields. Verdict: DAG agrees with the delivered proof and open hole.

Changes in this second reading: replaced stale scratch axiom imports left by the previous
shared-helper attempt, added an axiom scratch copy checking both private helpers, and
added this review. No delivered Lean or DAG repair was needed. The result remains one
original hole closed and one lower hole added, net zero; no module is claimed pruned.
