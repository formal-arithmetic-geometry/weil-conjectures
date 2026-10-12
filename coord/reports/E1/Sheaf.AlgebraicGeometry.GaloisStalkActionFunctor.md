## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.exists_galoisStalkActionFunctor` with a complete
Lean construction from a natural Galois action on the geometric point fibre. The existing
statement, universes, definitions and docstring are unchanged. Mathlib's site-point morphism
API descends the action to stalks. The proof establishes the action laws, the germ formula,
equivariance of all stalk maps, and continuity: a germ stabilizer contains its lift's open
stabilizer. It then constructs the functor through both full subcategories, and uses the
identity natural isomorphism on underlying stalks.

Added `Sheaf.AlgebraicGeometry.GaloisPointAction`, containing one smaller intermediate theorem
on geometric lifts, with a sourced proof in words. It has no sheaves, stalk colimits or
existential stalk functor. Added proof-only imports of this module,
`Mathlib.CategoryTheory.Sites.Point.Category` and `Mathlib.Topology.Algebra.OpenSubgroup`.
Updated the parent DAG proof and dependencies to follow the actual Lean construction.
The unused-variable linter is disabled locally for the original theorem, because the
quantified proof-binder names `hτ` and `hx` are not used in its result type; their hypotheses
are both used in the proof. This preserves the original signature verbatim.

Both delivered modules compile cleanly with the prescribed local compiler. Edge cases of the
intermediate statement were checked: empty fibres impose no condition; a separably closed
base gives the trivial action; the argument permits transcendental Omega/K and imperfect K.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.exists_galoisStalkActionFunctor`
(node `lem-exc-galois-stalk-action-functor`). No sorry remains in the original module.

Added exactly one hole:
`AlgebraicGeometry.Scheme.exists_galoisPointAction`
(node `lem-exc-galois-point-action`, module `Sheaf.AlgebraicGeometry.GaloisPointAction`).
Its proof is exactly `by sorry`. This is a decomposition: one upper hole closed, one
strictly smaller hole added, net zero holes removed. The stalk-colimit construction,
functor assembly and continuity implication are proved, rather than moved to that hole.
There are no other added holes, axioms, hollow definitions or arbitrary witness definitions.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints` from the original module.
Its node `lem-weil-pbc-etale-fibre-discrete-separable-points` remains needed by the new
point-action theorem and is imported there; it has not been pruned from the overall closure.

The proof does not use `AlgebraicGeometry.etaleFieldGsets` or its equivalence, full
faithfulness, essential surjectivity or cover characterization. The public import
`Sheaf.AlgebraicGeometry.EtaleFieldGsets` must remain, however, because its shared
`HasForget₂ (Type u) TopCat` instance is needed to elaborate the original statement's
continuous action category. Thus no whole module or node is claimed pruned. All newly
added proof imports are used, and the parent has no direct proof dependency on the
etale/Galois classification theorem. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original dependencies supply the finite separable residue fields but do not state the
natural absolute Galois action on the Type-valued geometric point fibre, its independence
of extensions, or its open stabilizers. That field/geometric step is now a distinct,
strictly smaller item. Mathlib already handles the descent to stalk colimits through
`Point.Hom.sheafFiber`, so no new descent theorem or sheaf-action existence theorem is needed.

The cited Stacks source is absent from the local literature directory; its Tag 03QW page
was read directly at `https://stacks.math.columbia.edu/tag/03QW`. The argument used is the
construction before Theorem 59.56.3, not that theorem's stronger equivalence assertion.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and source grep
were performed and are recorded in the new node. Blueprint searches found no duplicate
of the precise point-action statement.

## New nodes

`lem-exc-galois-point-action` states the natural action on geometric lifts and openness of
its stabilizers, with the exact formula for any automorphism of Omega extending g.
Its module is `lean/Sheaf/AlgebraicGeometry/GaloisPointAction.lean`. Its proof records the
extension, finite separable residue-field independence, naturality, action laws and Krull
openness argument from Stacks 03QW. The parent theorem proves all remaining categorical
steps from this statement using Mathlib. No change record is required: existing statements,
definitions and public imports are preserved.

## Second reading by E1

1. **Unchanged interface: PASS.** Compared both delivered modules with the repository.
   The parent has one existing theorem; its signature and docstring are byte-for-byte
   unchanged, as are its public imports. The changes are its proof, proof-only imports,
   and a local linter option. The point-action module is new. No definition or existing
   statement changed and no change record is required.
2. **Proof and axioms: PASS as a decomposition.** Both modules compile cleanly through
   `lcompile.py --all`. Scratch copies with `#print axioms` for both declarations show
   only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
   There is exactly one sorry, in the named new theorem; no forbidden declaration,
   holed definition, or arbitrary-witness definition occurs. Read the action composition
   order, point-morphism descent, germ compatibility, naturality, stabilizer inclusion,
   full-subcategory lifts, and identity underlying isomorphism: all match the claim.
3. **Split statement: PASS.** Independently checked the source at Stacks 03QW before
   Theorem 59.56.3 and the finite separable residue-field input. Extension automorphisms
   exist even for transcendental Omega; the embedded separable closure contains every
   finite separable residue-field image. Consequently the displayed formula determines
   every component of rho uniquely, so the existential theorem is not arbitrary data.
   Empty fibres are vacuous; a separably closed base yields the identity action; imperfect
   fields cause no inseparable residue-field ambiguity. Infinite disjoint unions of etale
   components still give finite residue fields at each lift. The theorem omits sheaves,
   colimits and stalk actions and is strictly a part of the parent argument, not a
   restatement. Independent LeanFinder, Loogle and grep searches found generic Galois
   category tools and field extension tools, but no duplicate with this formula and
   openness. Closing the remaining field/geometric theorem would require substantial
   formalization, rather than a short application of a found lemma.
4. **Route and pruning: PASS.** Mathlib already supplies the colimit descent and is used
   directly. No shorter ready-made field-specific action was found. The new proof-only
   imports are used; the retained public EtaleFieldGsets import supplies the Type-to-TopCat
   instance needed by the unchanged signature. The old direct proof dependency
   `lem-weil-pbc-etale-fibre-discrete-separable-points` moves below the new node; the other
   old dependency, `def-weil-pbc-geometric-stalks`, remains. No module is pruned from the
   import closure. Read `dag/units/sk-prop-h2.json`: its statement and sole Kummer step
   and its `realized` record are untouched, and this reduction bypasses no unit step.
5. **DAG agreement: PASS after repair.** Parent proof steps and dependency union match
   the Lean construction. The new node has its source, complete proof plan, dependencies,
   searches, origin, creation, blueprint, chapter/unit, and Lean record. Corrected its
   `lean.statement` to the verbatim multiline Lean signature and recorded the second
   reader's independent search results. No other node fields or Lean proofs were changed.

Second reading changed only the new node's signature transcription and search evidence,
and appended this review. One original hole closed, one strictly smaller hole added;
this is a decomposition with net zero holes removed, not a fully axiom-free proof.
