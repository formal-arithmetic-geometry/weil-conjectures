## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink`
with a complete Lean proof from two strictly smaller statements. Added proof-only
imports of `PerfectOpenStalkRetractHomEquality`, `OpenModuleStalkRestrictionComparison`,
`Mathlib.Data.Int.Interval`, and `Mathlib.AlgebraicGeometry.AffineScheme`.
No existing signatures, public imports, or definitions changed.

The proof shrinks each adjacent equation, inductively intersects the finitely many
neighbourhoods indexed by the source support, chooses an affine subopen, transports
the components via restriction transitivity, and proves the stalk coordinate formula
by naturality and cancellation. Outside the support, the source is zero; the final
support degree is included. No boundedness or perfectness of Q is used.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_degreewise_shrink`
(node `lem-sc-perfect-open-stalk-degreewise-shrink`). There are no sorries in the
item's module.

Added holes:

- `AlgebraicGeometry.Scheme.exists_open_stalk_retract_hom_eq`
  (`lem-sc-perfect-open-stalk-retract-hom-equality`): equality for a single pair of
  maps from a finite-free retract, with arbitrary target.
- `AlgebraicGeometry.Scheme.nonempty_openModuleStalkRestrictionComparison`
  (`lem-sc-open-module-stalk-restriction-comparison`): a natural isomorphism of
  module-stalk functors, with no complexes or chain equations.

This is a decomposition: one upper hole closed and two lower holes added, not a
sorry-free proof. Each new module has only its named public theorem with `by sorry`.
No data definition depends on either unproved theorem. The local choice of c occurs
inside an existential theorem proof, not in a public object definition.

## No longer needed

No original imports removed: both public imports occur in the statement.
The proof no longer directly needs node
`lem-weil-pbc-stalk-internal-hom-finite-presentation` or module
`Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation`; the finite-generation
zero-germ argument suffices. Its proof dependency was removed from the item's node.
The new hom-equality node instead uses the smaller existing generic tool
`lem-weil-pbc-finite-free-local-hom-zero` (`FiniteFreeLocalHomZero`).
These are dependency-edge pruning claims, not claims that other target branches
cease to use the modules.

The alternative `FiniteFreeStalkDegreewiseShrink`, `FiniteFreeStalkFiniteEquations`,
and `StalkRestrictionSubopenCompatibility` are not imported: their pullback-to-stalk-
scheme interface, finite-free hypotheses, and target boundedness do not fit this item.
`PerfectOpenStalkRetractMapEquality` is not used: it treats endomorphisms only.
No other nodes or modules from the planned argument are bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG called the comparison of the open module stalk functors a non-elementary
step but cited only their definition. It now has a smaller natural-comparison node.
Its other stated dependency, the internal-Hom finite-presentation theorem, does not
by itself expose shrinking of maps from slice-site retracts to arbitrary targets.
The new single-pair hom-equality statement isolates exactly that interface.

The new comparison cites Stacks Tag 00A0(3), including its module clause, rather
than the broader pullback-stalk formula 0098. Sources were read online; literature
payloads are absent from this clone. Tag 01CP's finite-type injectivity paragraph
supports shrinking without any finiteness hypothesis on the target.

The generic tools in the new nodes' plans, `new-module-restriction-stalk-components`
and `lem-weil-pbc-finite-free-local-hom-zero`, lie in other units. They provide
module-stalk/generator calculations, not replacements of any cube-unit step.
The original unit `sk-prop-av-cube` and its route are unchanged.

Edge cases checked in the statements and argument: empty support interval, zero
rank retract, unbounded arbitrary Q, the final source degree, V=W, and arbitrary
supplied e. The zero-rank case has no generators; empty opens cannot contain x.

## New nodes

`lem-sc-perfect-open-stalk-retract-hom-equality`, in
`lean/Sheaf/AlgebraicGeometry/PerfectOpenStalkRetractHomEquality.lean`, isolates
single-pair equality shrinking with a finite retract source. Its full proof in words
is in the declaration docstring and node. LeanFinder found only generic germ facts;
LeanSearch was unavailable; the sheaf-module grep found no matching statement.

`lem-sc-open-module-stalk-restriction-comparison`, in
`lean/Sheaf/AlgebraicGeometry/OpenModuleStalkRestrictionComparison.lean`, isolates
the natural functor isomorphism needed for restriction. The existing objectwise
`ModuleRestrictionStalkIso` does not supply naturality. LeanFinder and grep found
`Scheme.Modules.restrictStalkNatIso` for underlying abelian stalks, not this
slice-site module-stalk comparison. LeanSearch was unavailable. Blueprint searches
for stalk equality, stalk restriction, 01CP, and 00A0 had no matching blueprint nodes.

No change records or forced adaptations are needed.

## Second reading by D4

1. **Interface unchanged — pass.** Compared the delivered item with the repository
   using `diff` and an exact signature comparison. The existing theorem signature
   is byte-for-byte identical; both original public imports remain. The only new
   declarations in the item are private, explicit restriction/composition helpers.
   The two additional public theorems live in their own new modules. No definition,
   target statement, or other existing module was changed; no change record is needed.
2. **Proof and trust — pass, conditional on the two listed holes.** Compiled all three
   modules through `lcompile.py --all`: comparison 5.0 s, hom equality 5.3 s, item
   56.3 s, all without errors or warnings. Inspected every proof from the finite-set
   induction through the final naturality calculation. Only the two named public
   theorems listed above contain `sorry`; there are no forbidden declarations or
   hollow definitions. The restriction-composition isomorphism is explicitly
   constructed. The local choice of a stalk comparison occurs solely within a
   proposition proof, and defines no exported data. Explicit `#print axioms` in a
   scratch module showed exactly `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` for each of the three public declarations. The complete delivery axiom
   probe reported no disallowed axioms; `deliver3.py --no-push` printed OK and
   passed the preflight (CODEX because of the new modules and nodes). This closes one upper hole and adds two
   lower holes, a decomposition with net -1 holes closed, not a complete proof.
3. **Split statements — pass.** Read both complete docstring proofs and node plans
   against the actual stalk definition. Independently checked [Tag 01CP]
   (https://stacks.math.columbia.edu/tag/01CP), whose finite-type injectivity proof
   imposes no finiteness on the target, and [Tag 00A0(3)]
   (https://stacks.math.columbia.edu/tag/00A0), including its module clause. Checked
   rank zero, zero target, W=U, V=W, and the impossibility of an empty open containing
   x. A single-pair equality lemma and a natural module-stalk comparison are strictly
   smaller than the complex/finite-support target, not renamed restatements. Repeated
   searches with `leanfinder` for finite-generated sheaf maps equal near a point,
   `loogle` for stalk/restriction, and `grep` for local generators/restricted stalks,
   plus `rg` in both library roots. Found local-generator machinery and additive
   restriction-stalk isomorphisms, but no theorem with either complete slice-site
   module-stalk interface. Read `FiniteFreeLocalHomZero`, `ModuleRestrictionStalkIso`,
   `ModuleRestrictionStalkLinear`, `ModuleRestrictionStalkNaturality`, and the proved
   component construction. These do not directly close either new statement in a
   short pass: transport of slice-site restrictions and scalar actions remains.
4. **Route and pruning — pass.** The proof intersects precisely the finite source
   support interval, including its last degree; outside it both composites have
   zero source, even for arbitrary unbounded Q. Affine refinement and conjugation
   preserve the family and arbitrary supplied e. Every import is needed for a
   signature or proof; proof-only imports are plain imports. The old dependency
   removed is exactly `lem-weil-pbc-stalk-internal-hom-finite-presentation`, and is
   listed under No longer needed. No original import is removed. Read
   `dag/units/sk-prop-av-cube.json`: the unchanged unit route is not bypassed by
   these lower-level stalk calculations; no realized unit node is removed.
5. **DAG agreement — pass.** Checked all three node records against their Lean
   signatures byte-for-byte and checked that each `proof_deps` is exactly the union
   of its proof-step uses. The item's proof and origin describe the implemented
   reduction. Both new nodes have source, complete proof steps, searches, split
   status, creation record, blueprint provenance, chapter/unit, and Lean records.
   Only permitted proof fields of the existing node differ from the repository.

Second reading changed only this report: added the independent checks, source
verification, search results, and explicit decomposition/net-hole accounting.
No Lean or node repair was necessary.
