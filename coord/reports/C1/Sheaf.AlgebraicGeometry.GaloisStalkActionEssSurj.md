## What changed

Replaced the `sorry` in
`AlgebraicGeometry.Scheme.galoisStalkActionFunctor_essSurj` by a complete Lean proof
from finite-action realization. The theorem's signature and existing docstring are
unchanged. All additional imports in this module are proof-only.

The new module `Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct` proves
`CategoryTheory.discreteContAction_finite_orbit_coproduct` for any compact topological
group and arbitrary universe of actions. It constructs the actual orbit subtypes,
their restricted continuous actions, equivariant inclusions, and both colimit proofs.
Open stabilizers, the finite coset quotient, and the orbit-stabilizer equivalence
prove each orbit finite. There are no holes in this module.

The new module `Sheaf.AlgebraicGeometry.GaloisStalkFiniteActionRealization` states the
remaining finite-action realization step. The target chooses essential-image
witnesses only inside its theorem proof; no exported definition chooses an arbitrary
object from an unproved existence statement.

For an arbitrary action M, the target takes its finite orbit family, realizes each
orbit, forms the coproduct of the chosen sheaves, and defines an equivariant map
M → T(coproduct) by the orbit universal property. The natural isomorphism j transfers
stalk preservation of this coproduct to T followed by the underlying-set functor.
The underlying orbit coproduct and the transported stalk coproduct have isomorphic
points. Their factorization laws identify that isomorphism with the underlying map
of the constructed equivariant map. The action and full-subcategory APIs then lift
invertibility, giving the essential-image witness.

The original DAG node and both new nodes now describe this route. All three modules
compile together without warnings through lcompile.py (approximately 10 seconds in
all). The universe is unchanged: the orbit index lives in Type (max (u + 1) v),
so no larger-universe coproduct scheme is used.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.galoisStalkActionFunctor_essSurj`
(node `lem-exc-galois-stalk-action-essentially-surjective`). No `sorry` remains in
the assigned module.

Also proved the new theorem
`CategoryTheory.discreteContAction_finite_orbit_coproduct`
(node `lem-exc-discrete-continuous-action-finite-orbit-coproduct`), with no holes.

Added one hole, the finite geometric realization step:
`AlgebraicGeometry.Scheme.galoisStalkActionFunctor_finite_mem_essImage`
(node `lem-exc-galois-stalk-finite-action-realization`). Its proof is exactly
`:= by sorry`; its docstring supplies the source and proof in words.

This is a decomposition: one original hole closed and one strictly narrower hole
added, net zero holes. The remaining theorem concerns only finite actions; the
infinite-action orbit and coproduct arguments are fully proved. The assertions also
cover empty actions (empty orbit family and empty coproduct), trivial actions, and
a separably closed base field. No axioms or hollow definitions were added. `#print axioms` for the proved orbit
theorem reports only `propext`, `Classical.choice`, and `Quot.sound`; for the target
it additionally reports `sorryAx`, exactly because finite realization is still open.

## No longer needed

Second reading also removed redundant direct proof imports
`Mathlib.CategoryTheory.Sites.Limits` and
`Mathlib.CategoryTheory.Limits.Types.Colimits`: both are already publicly supplied
by the retained `Mathlib.CategoryTheory.Sites.LeftExact` import. The assigned
module compiles without either direct import.

The old direct `proof_deps` no longer named by the upper proof are
`lem-exc-etale-field-gsets`,
`lem-exc-etale-open-subgroup-quotient-finite-discrete`,
`lem-galois-stalk-representable`,
`lem-weil-pbc-etale-fibre-discrete-separable-points`, and
`lem-weil-pbc-small-etale-representable-presheaf-sheaf`. They now belong to the
finite-realization or orbit-decomposition steps, rather than the upper node.
None is globally pruned.

Removed direct proof imports from the assigned module:
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints` and
`Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`.
These modules remain needed by finite-action realization and are imported there;
they are not pruned from the targets' transitive import closure.

Removed `Mathlib.CategoryTheory.Sites.Point.Skyscraper` from the new finite-realization
module: that step does not use coproduct preservation. Kept it in the assigned module,
where its left-adjoint instance is used. No original mathematical dependency node or
library module is claimed as globally pruned: finite field classification, the
representable-stalk identification, the etale fibre result, and representable
sheafness all remain in the finite-realization node's proof dependencies. The
finite-open-subgroup quotient result is used in the proved orbit-decomposition node.
The geometric-stalk dependency stays in the original node's coproduct step.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect mathematical route was found. The DAG's second step
requires geometric glue not supplied by the signatures of the existing declarations:
identifying Ks-points and Omega-points and transporting the canonical germ action.
This finite realization is now an explicit, strictly narrower remaining item.

The generic orbit coproduct API needed by the first and third steps was absent.
It has now been constructed and proved, rather than left as a second hole.

Lean instance search for sheaf colimits does not terminate efficiently when invoked
only at the implicit HasColimit goal. Explicitly supplying HasSheafify and the
underlying type-colimit instance, then using Sheaf.instHasColimitsOfShape, resolves
this in seconds without changing definitions or raising resource limits.

No unit route is bypassed. The unit's realized statement/step lists do not name this
node, and the reduction follows all three steps of its original proof.

## New nodes

`lem-exc-galois-stalk-finite-action-realization`:
`dag/nodes/sec-curve-estimates/lem-exc-galois-stalk-finite-action-realization.json`.
Its module is `Sheaf.AlgebraicGeometry.GaloisStalkFiniteActionRealization`; it is the
one remaining hole. It realizes finite actions only, including the empty action.

`lem-exc-discrete-continuous-action-finite-orbit-coproduct`:
`dag/nodes/sec-curve-estimates/lem-exc-discrete-continuous-action-finite-orbit-coproduct.json`.
Its module is `Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct`; its
statement is fully proved and includes both categorical and underlying-set colimits.
No change record is needed: no existing public signature, definition, or public import
changed, and the original module's interface comparison is empty.

## Second reading by C1

1. Compared the assigned module with its repository version using `diff`. The
   existing declaration signature and docstring are byte for byte unchanged;
   only its proof, local options, and proof-only imports changed. Both other
   modules are new. No definition, public import, or existing statement changed.
   Verdict: pass; no change record is required.
2. Read all three modules and compiled them in import order through lcompile.py.
   There is precisely one local `sorry`, the named finite-realization theorem
   reported above. No forbidden declaration or hollow definition occurs. Scratch
   `#print axioms` confirms that orbit decomposition uses only propext,
   Classical.choice, and Quot.sound; the upper theorem additionally uses sorryAx
   from the finite-realization hole. Witnesses chosen from this hole occur only
   inside a theorem proof, never in exported data definitions. Verdict: pass as
   a decomposition, not a completed axiom-free essential-surjectivity proof.
3. Read the finite-realization signature against its geometric construction and
   the supplied germ formula. Its only restriction beyond the upper statement
   is finiteness of the given action. Finite sets can be resized to Fin n; the
   existing etaleFieldGsets result realizes them. A geometric point of an etale
   scheme over K has finite separable residue field, so its Omega-embedding has
   image in Ks and the factorization is unique. Extending each g to Omega and
   applying the germ formula yields the required action compatibility. Checked
   empty actions, singleton trivial actions, and separably closed K: all fit
   the statement and construction. Searched with different leanfinder, loogle,
   and grep queries (recorded in the new nodes and searches.jsonl), and searched
   lean/Sheaf and the upstream algebraic geometry sources. Found generic Galois
   category realization, requiring additional category/fiber-functor structure,
   but no replacement for this geometric comparison. The lower hole is strictly
   narrower; the nonfinite orbit and coproduct work is proved. Verdict: pass.
4. Read the upper proof from its colimit construction downward and inspected the
   retained imports and the source proof of Stacks 03QT in the local Stacks copy.
   The action coproduct and underlying-set coproduct give the comparison map;
   its component equations identify it with an isomorphism, and the forgetful
   functors reflect invertibility. The index stays in the existing value
   universe; the empty family uses the empty sheaf coproduct. The unit
   sk-prop-h2 has empty realized lists and this node realizes none of its fixed
   statement/steps. The original three-step route is retained. The report now
   explicitly lists every old direct dependency relocated below the upper node.
   Verdict: pass; no globally pruned module.
5. Checked both new nodes' required fields, statements, proof steps, sources,
   dependencies, and Lean declarations. The upper node uses exactly the two new
   results and stalk colimit preservation; the orbit node uses the Mathlib open
   subgroup quotient result; the finite node retains the original geometric
   dependencies. Corrected the new nodes' lean.statement fields to contain the
   actual multiline signatures verbatim and added independent search results.
   Verdict: pass.

Changes from this reading: removed the two redundant direct Mathlib imports,
corrected new-node signature records, added independent search records, and
completed the dependency-pruning report. No Lean proof or mathematical statement
needed repair. The finite geometric realization is too substantial to close in
a few minutes; it remains the single explicitly sourced lower hole.
