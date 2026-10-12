## What changed

Replaced the whole proof of
`Rep.nonempty_equiv_invariantResolution_inhomogeneous` in
`Sheaf.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology`.
Its statement, universes, public imports and original docstring are unchanged.
The proof now combines the locally constant cochain delta-functor with the existing
universality theorems, computes right derived invariants using the supplied resolution,
and transports homology along an explicitly proved complex isomorphism.
The private helper `Rep.universalDeltaFunctor_iso_all` generalizes the degree-specific comparison to a theorem valid for every degree at once. Specializing it gives the required comparison without restating the existing theorem; the proof is the same uniqueness argument. 

Added two proof imports and their new modules:

- `Sheaf.RepresentationTheory.DiscreteIntegerInvariantsInfrastructure` proves
  `Rep.discreteInteger_invariants_infrastructure` from the existing arbitrary-ring
  injective-embedding theorem and Mathlib's invariants adjunction restricted along
  the full discrete subcategory. This supplies enough injectives after any categorical
  equivalence and finite-limit preservation of invariants, even without compactness
  or an abelian-category assumption on the source category.
- `Sheaf.RepresentationTheory.LocallyConstantCochainsEffaceable` states the unresolved
  construction, exactness, degree-zero identification and coinduced effacement together.
  Its complex is specified by additive term coordinates, its coefficient maps and its
  differential, hence is determined up to the coordinate complex isomorphism.
  No public definition chooses an arbitrary witness from an unproved existence theorem.

Updated the original node's proof, proof dependencies and proof origin to match this
reduction. Added the two matching nodes. No existing definition, public signature or
visibility changed; there are no forced adaptations or change records.

All three modules compile together through `lcompile.py --all`, without errors or warnings.
Edge cases checked mathematically: degree zero has no incoming boundary and the displayed
formula is g*m-m; zero coefficients give zero terms; the trivial group gives the usual
alternating complex with only degree-zero cohomology; finite discrete groups are the
ordinary group-cochain special case. The infrastructure is valid for any topological
group because trivial-action stabilizers are the whole group and the existing embedding
theorem has no compactness or scalar finiteness hypothesis.

## Proved and sorry left

Closed the original hole:
`Rep.nonempty_equiv_invariantResolution_inhomogeneous`
(lem-sc-discrete-resolution-inhomogeneous-cohomology).
Its complete Lean proof uses the separately stated cochain theorem below and existing
library declarations. There are no sorries left in the item's module.

Also proved the new theorem `Rep.discreteInteger_invariants_infrastructure`
(lem-sc-discrete-integer-invariants-infrastructure), from the existing theorem
`Rep.discreteContinuousRep_functorialInjectiveEmbeddings_of_topologicalGroup`
and Mathlib. This is a proof from a pre-existing unresolved dependency, not a claim that
all of injective theory is now sorry-free.

Added exactly one hole:
`Rep.exists_locallyConstantCochains_effaceable`
(lem-sc-locally-constant-cochains-effaceable), in
`Sheaf.RepresentationTheory.LocallyConstantCochainsEffaceable`.
Its whole proof is `:= by sorry`, with its source and complete construction/effacement
argument in its docstring and node. It involves neither the supplied resolution I,
the supplied complex K and its coordinates t, nor any derived-functor comparison.
It is the strictly separate construction/effacement part of original steps 2 and 3.

This is a decomposition: one original hole closed, one new hole added, net zero among
the delivery's declarations. The universality comparison, injective infrastructure,
coordinate commutation and homology transport are implemented in Lean. Existing
unresolved dependencies are reused rather than restated.

## No longer needed

Removed the redundant direct proof import `Sheaf.CategoryTheory.DeltaFunctor` from the
item: its declarations remain available via the public imports of the cochain theorem
and the right-derived delta-functor theorem, and its node remains a genuine proof
dependency of the universal comparison. This removal does not prune that module out
of the target closure.

No mathematical node or module in the original route has become unnecessary.
In particular the injective-resolution, left-exact-functor, delta-functor,
effacement-universality and right-derived-universality nodes are retained.
The original direct proof dependency on def-exc-discrete-modules-category is now
mediated through the two new nodes; it remains a statement dependency of the item.
No claim of whole-module pruning is made.

The tempting finite-scalar-ring chain (`ContinuousCochainsDerivedInvariants`,
`ContinuousCochainsDeltaFunctor`, `ContinuousCochainsInvariantsZero`,
`CoinducedContinuousAcyclic`, `CoinducedDiscreteEmbedding`, and
`DiscreteModulesAbelian`) is not imported: its Finite hypothesis cannot be instantiated
for Z. It was never needed by the integer-coefficient route in this delivery.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies provide abstract delta-functor tools, but do not supply
an integer-coefficient cochain construction/effacement statement. The similar library
lemmas all impose a finite scalar ring. This is an interface gap, not a false original
statement; it is isolated in the new cochain theorem.

The node's enough-injectives step can already use the arbitrary-ring theorem
`Rep.discreteContinuousRep_functorialInjectiveEmbeddings_of_topologicalGroup`.
Its left-exactness step has a direct Mathlib proof by restricting the
trivial-action/invariants adjunction; no separate module kernel/cokernel construction
is required for that step.

The local literature directory contains only indexes on this machine. Checked the
published Stacks pages for Tags 04JF and 0DVG directly. Tag 0DVG states the profinite
comparison without proving it; the contraction and compactness argument is explicitly
agent-supplied in the remaining theorem's proof origin. The unit sk-thm-br and its route
are unchanged; this reduction stays below the unit level.

## New nodes

`lem-sc-discrete-integer-invariants-infrastructure`, at
`dag/nodes/sec-curve-estimates/lem-sc-discrete-integer-invariants-infrastructure.json`,
records the proved enough-injectives/finite-limit infrastructure and its existing
arbitrary-ring embedding dependency. Its module is
`lean/Sheaf/RepresentationTheory/DiscreteIntegerInvariantsInfrastructure.lean`.

`lem-sc-locally-constant-cochains-effaceable`, at
`dag/nodes/sec-curve-estimates/lem-sc-locally-constant-cochains-effaceable.json`,
records the one remaining construction and effacement theorem. Its module is
`lean/Sheaf/RepresentationTheory/LocallyConstantCochainsEffaceable.lean`.
It preserves arbitrary integer coefficients and explicitly specifies the complex's
coefficient maps and differential. The new nodes inherit the original chapter, unit
and blueprint ancestry; three search kinds and the failed LeanSearch service are recorded.
There are no change-record paths because no existing interface was changed.


## Forced adaptations

None. The returned duplicate theorem was removed by generalizing the local comparison helper to all degrees; no module held by another group was adapted.

## Second reading by P3

1. **Statements and interfaces.** I compared the delivered item module with the repository
version and verified that the target declaration, its hypotheses, conclusion, universes,
public imports, and docstring are unchanged. The two added modules introduce only the
declarations recorded by their matching DAG nodes.

2. **Proof and axioms.** I compiled all three delivered modules with `lcompile.py --all`.
The target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`; the sole remaining `sorry` is the named split theorem
`Rep.exists_locallyConstantCochains_effaceable`, exactly as documented. The target proof
uses the universal delta-functor comparison, the supplied resolution isomorphism, and an
explicit coordinate complex isomorphism.

3. **New statements.** I checked both new statements against their declarations and
docstrings. `Rep.discreteInteger_invariants_infrastructure` is proved from the existing
arbitrary-ring injective-embedding result and a restricted invariants adjunction. The
cochain theorem is a strictly lower-level construction/effacement statement, with its
complex and differential specified rather than chosen from an existential witness; its
remaining proof is a named, sourced split. Neither duplicates the item statement or an
existing library declaration.

4. **Pruning and dependencies.** The removed direct `DeltaFunctor` proof import is
transitively supplied by the new cochain and universal-comparison imports. The item node's
proof, proof dependencies, and proof origin match the code, and the new node records match
their declarations. No unit-level route was bypassed; `sk-thm-br` remains the unit.

5. **Edge cases and route.** Degree zero, zero coefficients, and the trivial-group case
agree with the displayed inhomogeneous differential. The infrastructure theorem has no
compactness or finite-scalar assumption, while the cochain theorem carries the compact,
Hausdorff, totally disconnected hypotheses needed for local constancy and effacement. The
shortest available route was used after checking the imported library declarations.

I changed only this report section during second reading; no Lean declarations or DAG
statements required repair.
