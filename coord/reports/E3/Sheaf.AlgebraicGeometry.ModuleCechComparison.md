## What changed

Proved the alpha chain-map identity in `Sheaf.AlgebraicGeometry.ModuleCechComparison`, without
changing any existing signature or definition. Two proved private helpers express
naturality of the global-section restriction and its zero Cech differential.

Reduced `moduleCechAlpha_isIso` to augmented Cech acyclicity of a single injective
module and the existing `HomologicalComplex₂.quasiIso_of_column_augmentation`.
The proof constructs the augmentation of the flipped double complex, proves its
component equality with alpha composed with the inverse total-flip isomorphism,
applies the column criterion, and cancels the isomorphism. The natural-number
flip signs and their compatibility equations are proved locally.

Added proof-only imports of `Sheaf.AlgebraicGeometry.InjectiveModuleCechAugmentation`,
`Sheaf.Algebra.Homology.FirstQuadrantAugmentation`, and
`Mathlib.Algebra.Homology.TotalComplexSymmetry`. Added the single-injective-module
augmentation theorem in its own module and a matching node. Updated the original
node's proof, proof_deps and proof_origin to describe the actual Lean argument.

Both modules compile together with lcompile.py. No other module was adapted.

## Proved and sorry left

Current baseline holes closed (all names below are in
`AlgebraicGeometry.Scheme.Modules`):

- `moduleCechAlpha_comm`: proved by restriction naturality, cancellation of the
  first two Cech cofaces, and the total differential formula.
- `moduleCechAlpha_isIso`: reduced with a complete compiling proof from the
  single-row lemma below and the existing first-quadrant augmentation theorem.
  This is a decomposition rather than a completed acyclicity proof.

Additivity, whole-space restriction, and `moduleCechBeta_comm` were already
proved by B2 in the current repository baseline. Their proofs are preserved;
they are not progress of this delivery.

The item's module has no remaining sorry. Exactly one hole is added:
`AlgebraicGeometry.Scheme.Modules.injectiveModuleCechAugmentation_quasiIso`, in
`Sheaf.AlgebraicGeometry.InjectiveModuleCechAugmentation`, node
`lem-sc-injective-module-cech-augmentation`. Its entire proof is `by sorry`.
The docstring contains the source and full argument: sheaf gluing in degree zero,
injective Cech vanishing in positive degrees, and reflection through forgetting
scalars. This theorem concerns one injective module and no resolution or total
complex, so it is strictly a part of the total-resolution comparison argument.

One current baseline hole is proved directly; one is reduced; two holes are
closed and one is added. The two private helpers are fully proved and add no holes.
The reduction also uses existing declarations with their own proof obligations,
as authorized for stage 3.

## No longer needed

None. No imports were removed, and no previously stated proof-dependency node
was pruned: the original node's proof_deps was empty. All four original public
imports are needed by the statements or definitions. All three added proof-only
imports are used. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's node is a definition node with an empty proof and empty proof_deps,
although its module originally contained five theorem holes (two remain in
the current baseline). There was no numbered node plan
to instantiate. The theorem docstrings and the source proof of Stacks 01EQ supply
the missing route, now recorded in the node copy.

Mathlib's total-flip isomorphism has no available symmetry instance for up Nat;
the proof supplies and proves the usual (-1)^(i*j) signs locally. No global
instance or interface is changed. The new augmented-row statement was checked
for an empty covering (forcing an empty scheme), degree zero, positive degrees,
and covers with repeated opens. Its zero-component hypothesis specifies the
canonical map and does not assert existence or choose data.

The source cohomology.tex, lines 1408–1481, was read at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/cohomology.tex`;
the canonical literature path is absent in this read-only clone. No repository
files were written or fetched to repair that local literature mirror.

## New nodes

`lem-sc-injective-module-cech-augmentation` is the augmented Cech acyclicity
statement for a single injective module. It adds the canonical degree-zero
gluing identification to the existing positive-degree vanishing theorem, in the
Mathlib module-valued Cech interface needed by the first-quadrant criterion.
It is sourced to Stacks 01EP and its use in 01EQ. Three Mathlib search kinds
were attempted (LeanSearch unavailable), and the imported blueprint and project
were searched for duplicates. Its proof records the existing positive-degree
vanishing and standard Cech-complex comparison as dependencies. No change
records are required: every existing signature and definition is unchanged.

The resumed attempt initially failed parsing two helper docstrings followed by
`set_option`. Removing the unnecessary local options repaired compilation;
the final proofs need no transparency option. Stale generated probe files were
removed before the delivery dry check.

## Second reading by E3

1. Compared the delivered module with the repository using `diff -u` and the
   raw signature slices of the project declaration parser. All twelve existing
   signatures are byte for byte unchanged. Only the two reported theorem bodies
   change; every definition, existing docstring, instance attribute and public
   import is preserved. No adaptation or change record is needed. Verdict: pass.

2. Independently compiled both modules together with `lcompile.py --all`:
   no errors or warnings, 11.2 s and 47.3 s respectively. Scanned both sources:
   exactly the reported named public augmented-row theorem has `by sorry`,
   with no forbidden declarations or hollow definitions. A fresh scratch module
   imported the compiled delivery and ran `#print axioms` on all twelve existing
   declarations and the new theorem. The chain-map identity and all definitions
   use only `propext`, `Classical.choice`, and `Quot.sound`. The alpha isomorphism
   theorem and the new augmentation theorem additionally use `sorryAx`, as
   reported. The isomorphism reduction remains conditional on open dependencies.
   Verdict: pass with precisely the reported remaining obligation.

3. Read the split theorem, its full docstring proof, its node, and the source's
   injective-trivial-Cech and Cech-cohomology proofs in `cohomology.tex`. Gluing
   gives the canonical degree-zero isomorphism; injective-module Cech acyclicity
   gives positive-degree vanishing. The component hypothesis specifies the
   restriction map, and all higher source components are zero. Checked empty
   covers (forcing X empty), a singleton cover by X, repeated opens, zero
   coefficients, and degree zero versus positive degrees. There is no arbitrary
   witness choice. Repeated LeanFinder, Loogle (`CochainComplex.single₀, QuasiIso`)
   and grep searches using different wording, and searched both project source
   roots with `rg`. Existing positive-degree acyclicity and complex-comparison
   theorems do not already state this canonical augmented ModuleCat result.
   The split concerns one injective module, with no resolution or total complex,
   and is strictly a part of the argument. Closing it requires gluing and
   transport between Cech interfaces, not a short application of an available
   theorem. Verdict: true and needed; the split remains open.

4. Read the alpha proof downward: naturality and cancellation of the two cofaces
   give the direct chain-map proof; the explicitly verified (-1)^(i*j) symmetry
   turns rows into columns; the existing first-quadrant augmentation criterion
   gives the total comparison. Checked the +1 sign on the zero axis and
   cancellation of the total-flip isomorphism. No shorter applicable theorem
   was found. All three added imports are proof-only; the four original public
   imports support statements or definitions. The original node had no proof
   dependencies, so `## No longer needed` omits none. Read the unit record
   `dag/units/sk-thm-picard-duality.json`: its statement, steps and `realized`
   remain unchanged, and no unit-level route is bypassed. Verdict: pass.

5. Compared both node records with the declarations and argument. The existing
   node records the direct commutation proofs and the two dependency declarations
   used by the isomorphism reduction. The new node's Lean statement matches its
   theorem; the source, searches, creation, blueprint, chapter, unit and Lean
   records are present. Its proof plan records degree-zero gluing, transport of
   positive-degree vanishing, and the single-term source; proof_deps is the union
   of its steps' uses. Verdict: pass.

Second reading changes: appended this independent review and recorded fresh
search and axiom-check evidence. No Lean proof, statement, definition, import
or node needed repair. Progress remains two baseline holes closed and one new
hole added: one direct proof plus one decomposition, net one hole removed.
