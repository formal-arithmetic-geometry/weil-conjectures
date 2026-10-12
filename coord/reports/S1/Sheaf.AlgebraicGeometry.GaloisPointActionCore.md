## What changed

Proved `AlgebraicGeometry.Scheme.exists_galoisPointAction_core` with its exact original
signature. No public statement, definition, visibility, universe, or target changed.
The fully proved private definitions `fiberPrecomp` and `sepClosureAction` provide natural
precomposition and the Galois action over Ks.

Each Omega-valued etale lift descends to Ks by the already proved
`Scheme.Hom.exists_SpecMap_comp_eq_of_isSepClosed`; the already proved
`Scheme.SpecMap_comp_injective` gives uniqueness. These componentwise bijections naturally
identify the fibre functors. Transport the Ks action across this isomorphism. The given
extension identity directly proves the formula. The inverse used in the transport is the
inverse of a proved bijection, so its data is uniquely determined. No unproved existence
result or choice of extending automorphisms is used.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts`. Both original public
imports stay: they supply the public geometric-fibre and Galois interfaces. The two private
helpers and the target have only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
The source route is Stacks 03QW, the residue-field paragraph before Theorem 59.56.3, implemented
by the proved source-library descent theorem. The core node's proof, proof dependencies and
proof origin describe the implemented route.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.exists_galoisPointAction_core`
(`lem-exc-galois-point-action-core`). No holes remain in the module; no holes were added.
Both private helpers are fully proved. This is one proof, not a decomposition.

Local single-file compilation passes without warnings. A scratch copy with `#print axioms`
checks the target, both private helpers, the upstream descent theorem and upstream injectivity
lemma: all use only `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
The delivery dry run additionally probes every declaration and checks the unchanged interface.

## No longer needed

Removed the original proof-only import `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
and its node `lem-weil-pbc-etale-fibre-discrete-separable-points`, the sole old proof dependency.
The complete discreteness and singleton-open fibre decomposition is unnecessary for the core
formula. Other users may still need that module; this report does not claim it leaves the
entire targets' closure.

Removed the original direct proof-only import `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
its required instances are available through the new upstream geometric-lift import. The first
worker's added `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` and
`Mathlib.AlgebraicGeometry.Morphisms.Flat` imports are also unnecessary after the second reading.
No automorphism-extension-through-an-algebraic-closure or transcendence-basis lemma is needed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The old DAG mentioned openness although this core theorem asserts
none, and omitted the descent and transport glue. Its proof now describes those steps.
The original declaration's proof-plan docstring describes extension of automorphisms; it is
preserved as API documentation. The inline proof comment and updated node describe the actual
shorter descent route. A future documentation update could replace the old plan by: descend
lifts uniquely to Ks, assemble a natural fibre isomorphism, act over Ks, and transport the action.

The first worker missed the exact proved upstream geometric-lift theorem and upstream
injectivity lemma. The second reading replaces the duplicate `etaleLift` proof and the flat-epi
argument by these results, and updates imports and node metadata accordingly.

## New nodes

`lem-exc-etale-lift-sepclosed-base` records the already proved source declaration
`AlgebraicGeometry.Scheme.Hom.exists_SpecMap_comp_eq_of_isSepClosed` in
`WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts`, with its exact
signature and a complete proof in words. It adds no Lean statement, module or hole.
The first worker's proposed `lem-exc-separable-embedding-factorization` node is not delivered:
the directly used geometric-lift result now records the complete reduction. No change record
is required because no existing interface changed.

## Second reading by S1

1. PASS. Compared the delivered module with the repository version. The only existing
   declaration is `exists_galoisPointAction_core`; its signature is byte-for-byte unchanged,
   verified by direct text comparison. Public imports and the existing docstring are unchanged.
   Added definitions are private and occur only in the theorem's proof, not in its signature.
2. PASS. Compiled the original delivery, then the repaired module, without errors or warnings.
   The module contains no sorry, axiom, unsafe, opaque, implemented_by, extern or hollow data.
   `#print axioms` on all three delivered declarations and the two upstream results gives only
   the three permitted axioms. The bijective-precomposition inverse determines the chosen data.
3. PASS. No statements are split off. Read the existing upstream descent proof in full and
   compared its exact signature with the new node. Tested its assumptions conceptually: an
   empty X has no g and gives no false existence; the identity field embedding returns the same
   lift; Omega need not be algebraically closed; every finite separable residue-field image
   lands in L because the polynomial splits there. Injectivity of beta makes the descent unique.
   Repeated searches with different phrasing via leanfinder, loogle and grep; searched lean/
   and the DAG. The exact upstream result is reused, not restated in Lean.
4. PASS AFTER SIMPLIFICATION. Removed the duplicate etaleLift helper and unnecessary flatness
   route by using the already proved geometric-lift and field-precomposition lemmas. Kept the
   correct action, transport and formula proofs. All surviving proof imports are used; all old
   proof dependencies removed are listed above. Read dag/units/sk-prop-h2.json: this core node
   realizes neither its statement nor any of its steps; its realized lists are empty, and this
   shortening stays below the unit level without changing the unit's route.
5. PASS AFTER UPDATE. Read both delivered node files and their dependency records. The core
   proof and proof_deps match the descent, injectivity, action and transport written in Lean.
   The new node attaches an existing proved declaration, has a verbatim signature, source,
   full proof, dependency union, searches, creation and blueprint records, chapter and unit.
   No existing statement or statement dependencies changed.

Changed in the second reading: replaced the duplicate descent helper and flat-epi cancellation
by proved upstream results; reduced proof imports; replaced the proposed field-factorization
node by the directly used geometric-lift node; updated the core proof metadata and this report.
