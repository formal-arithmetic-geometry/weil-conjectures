## What changed

Replaced the single sorry in `AlgebraicGeometry.perfect_iff_affine_bounded_projective`
with a complete proof using the existing ring criterion and two strictly smaller
intermediate steps in new modules. The original declaration and docstring are unchanged.
The forward proof obtains a pseudo-coherent finite-Tor preimage, applies
`DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude`, maps the resulting
isomorphism through the affine equivalence and inclusion, and composes the tilde comparison.
The converse constructs the definition's pointwise witnesses by mapping the given
isomorphism through derived restriction and composing it with a local strict-model comparison.

All three files compile together with lcompile.py. The original node's proof and
proof_deps now describe these actual Lean steps. No definitions or existing signatures change.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.perfect_iff_affine_bounded_projective`
(lem-pc-perfect-affine-bounded-projective).
Added two holes:

- `AlgebraicGeometry.perfect_affine_module_preimage`
  (lem-pc-perfect-affine-module-preimage), in PerfectAffineModulePreimage.lean.
- `AlgebraicGeometry.affine_projective_local_strict_model`
  (lem-pc-affine-projective-local-strict-model), in AffineProjectiveLocalStrictModel.lean.

This is a decomposition: one original hole closed, two strictly smaller holes added.
The preimage step stops before constructing a bounded projective replacement. The
strict-model step concerns only termwise tilde and restriction of an explicitly given
complex, with no arbitrary E. The ring criterion remains an existing sorry dependency.
No sorry remains inside the main theorem's proof.

## No longer needed

Removed the main module's direct proof imports of AffinePseudoCoherentCriterion,
AffineQCohDerivedEquivalence, AffineTorAmplitudeCriterion,
PerfectPseudoCoherentLocallyFiniteTor, and PseudoCoherentComplex. The first four
modules' obligations are now located under PerfectAffineModulePreimage; they remain
needed in the transitive proof plan. PseudoCoherentComplex is already exposed through
the affine pseudo-coherence criterion, so its separate import is redundant.

No original proof node is globally pruned: the affine equivalence, pseudo-coherence
criterion, Tor criterion, and perfect-to-pseudo-coherent theorem remain needed by the
new preimage step. The ring criterion is used directly. The two new statements do not
bypass any blueprint unit; they realize the original affine-case argument.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox held the original sorry, with no completed delivery. A preliminary
directional split was discarded: the final delivery uses smaller genuine proof steps and
contains no directional restatement nodes. The original plan's quasi-compactness and
restriction glue is not furnished by the signatures of its existing inputs; it is now
explicitly assigned to the preimage step. The converse's finite-free retract and exact
restriction comparisons are similarly explicit in the strict-model step.

Checked the new statements on the empty spectrum/zero ring and on the zero complex.
Bounds are allowed to enlarge; the empty-spectrum preimage can use [0,0], and the
local-model conclusion is vacuous when there are no points. No data is chosen into a
definition from an unproved existence theorem; existential witnesses are used only
inside the proof of a proposition.

## New nodes

`lem-pc-perfect-affine-module-preimage` records pseudo-coherence and finite Tor amplitude
of a preimage under an affine equivalence, with its natural comparison with termwise tilde.
It uses the four existing affine/perfect criteria; it does not assert a bounded
projective replacement. Source: Stacks 08EB and its cited 08E7, 08E9, 08CQ arguments.

`lem-pc-affine-projective-local-strict-model` records strictly perfect models for derived
restriction of the associated-sheaf complex of a bounded finite-projective module complex.
Its proof is termwise splitting, restriction, and exactness; it does not assert perfectness
of an arbitrary derived object. Source: the reverse direction of Stacks 08EB and the
strict-perfect definition. Searches found no existing matching declaration; LeanSearch
returned an Internal Server Error and is recorded as unavailable.

## Second reading by P3

1. Compared the delivered item module with the repository version. The theorem signature and
all existing declarations are byte-for-byte unchanged; only imports and the proof body changed.
Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`. They compile without errors.
The only remaining `sorry`s are the two named split-off theorems, each with a public declaration,
docstring source and matching DAG node; there are no hollow definitions, axioms, unsafe or opaque
declarations. Verdict: pass.

3. Checked both split-off statements against the imported library and repository search results.
The module-preimage statement stops before bounded-projective replacement, and the strict-model
statement concerns only an explicit bounded finite-projective complex, so neither restates the
item. Edge cases (empty spectrum and zero complex) are vacuous or satisfy the stated bounds.
Verdict: pass.

4. The main proof applies the affine preimage step, the ring pseudo-coherent finite-Tor criterion,
and the local strict-model step exactly along the unit route. Imports removed from the original
module are now confined to the preimage module; the report records all removed imports and no
additional proof dependency is bypassed. Verdict: pass.

5. DAG node proof steps, proof dependencies, declarations and module paths match the Lean code;
the two added nodes carry source, proof, search and blueprint metadata. Verdict: pass.

Changed only the report by adding this second-reading record; no Lean statements or definitions
were changed during review.
