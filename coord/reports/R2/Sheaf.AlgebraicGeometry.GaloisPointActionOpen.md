## What changed

Proved `AlgebraicGeometry.Scheme.galoisPointAction_open_stabilizers` without changing
its signature, visibility, or hypotheses. The proof factors a lift through the separable
closure using the closed source-library geometric-lift theorem, obtains an open
stabilizer from `etaleFieldGeometricAction_continuous`, and proves containment in the
stabilizer of the supplied action. `Subgroup.isOpen_mono` finishes the argument.

Two private helpers are fully proved: `exists_algEquiv_extension` extends a field
automorphism through an arbitrary algebraically closed extension by coefficient action
on a transcendence-basis polynomial algebra and `IsAlgClosure.equivOfEquiv`;
`separablePoint_stabilizer_open` applies the existing continuity theorem. In particular,
the extension is not assumed algebraic, and no arbitrary object is defined from an
unproved existence theorem.

Added proof-only imports of `Sheaf.AlgebraicGeometry.EtaleFieldGeometricAction`,
`WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts`, and
`Mathlib.FieldTheory.IsAlgClosed.Classification`. Updated the item's node to the actual
proof route. The unit record has no realized statement or steps attached to this item;
its Kummer argument is unaffected.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.galoisPointAction_open_stabilizers`
(node `lem-exc-galois-point-action-open`). No `sorry` remains in the item; no holes,
axioms, new definitions, or new public statements were added. This is a proof, not a
decomposition. Both private helpers compile without `sorry`.

Single-file compilation succeeded with no warnings. The delivery dry run printed OK:
compilation and the declaration-axiom probe passed; the static preflight passed except
for the second reading reserved for the next worker. Only the permitted standard axioms
are used. Nothing was pushed.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
and the item's direct dependency on `lem-weil-pbc-etale-fibre-discrete-separable-points`.
The explicit finite residue-field/open singleton decomposition of the original plan
is unnecessary: the closed geometric-lift factorization theorem and the already proved
separable-closure action supply the needed facts. This is a local dependency removal;
other users may still need that module. No other original imports were removed.
An exploratory explicit `Mathlib.Algebra.MvPolynomial.Equiv` import was removed after
compilation showed the Classification import already supplies it.

## Where the brief, the DAG or earlier work was wrong

The earlier node only said that extending automorphisms and finite separable residue
fields ensure openness. Its dependency did not itself state either the automorphism
extension or the transfer of actions. The actual proof makes these steps explicit.
A lift into an arbitrary algebraically closed Omega cannot be treated as a lift into
the separable closure without factorization. The source library already proves that
factorization, and the field-extension helper handles transcendental Omega as well.
The identity automorphism and an empty etale scheme present no extra cases: the former
extends by the same construction, and the latter has no lifts to quantify over.


## Second reading by R2

1. **Interface — pass.** Compared the sole delivered module with the repository using
   `diff`; the existing public theorem signature is byte for byte identical, including
   every hypothesis, conclusion, universe and visibility. No definition or public
   statement was added or changed. No change record or forced adaptation is needed.
2. **Proof — pass.** Independently compiled the module through `lcompile.py`, without
   errors or warnings. Searched the delivered Lean for `sorry`, axioms and forbidden
   implementation escapes: none occur. A scratch copy with explicit `#print axioms`
   for the target and both private helpers compiled; all three use exactly `propext`,
   `Classical.choice`, and `Quot.sound`, without `sorryAx`. The lift is obtained from
   a proved theorem, and the automorphism is constructed using proved Mathlib results;
   no data is chosen from a postponed existence theorem.
3. **Split statements — pass (none).** There are no split-off statements or new holes.
   Read both private helpers. The coefficient automorphism extends over the polynomial
   algebra on a transcendence basis and then its algebraic closure, and its restriction
   fixes K. This works for an empty basis (algebraic Omega/Ks), a nonempty basis
   (transcendental Omega/Ks), and the identity automorphism. Empty X has no lifts.
   Independently searched the library by automorphism-extension and stabilizer terms,
   and queried LeanFinder for extending subfield automorphisms to possibly transcendental
   algebraically closed overfields; no direct replacement was found. Read the actual
   pinned Mathlib Classification and Basic declarations used by the helper.
4. **Route and pruning — pass.** Read the geometric-lift factorization theorem and
   the concrete separable-closure action and its proved continuity theorem. The proof
   first uses these closed results, transfers stabilizer containment using hρ, and
   finishes by `Subgroup.isOpen_mono`. Every added import is proof-only and used;
   both public imports support the statement. `## No longer needed` lists the sole
   old proof dependency and its removed import. The unit `sk-prop-h2` has empty realized
   statement/step lists, and this local route preserves its Kummer argument.
5. **DAG — pass.** The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`; its statement and Lean signature record are unchanged. The union
   of step uses is exactly `proof_deps`, namely the continuity node. Closed source and
   Mathlib declarations are named explicitly in the proof steps. No new nodes exist.

Second-reading change: restored the existing public theorem docstring verbatim, avoiding
an unnecessary API documentation rewrite. The proved argument, signatures, imports and
node route needed no repair. Closed holes: `AlgebraicGeometry.Scheme.galoisPointAction_open_stabilizers`
(1 of 1 original holes). Added holes: none. Split off: none.
