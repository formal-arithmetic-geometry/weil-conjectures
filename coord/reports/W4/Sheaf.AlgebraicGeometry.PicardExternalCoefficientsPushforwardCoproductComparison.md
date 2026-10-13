## What changed

The original theorem now composes two actual presheaf isomorphisms through the
concretely constructed `picardConstantSectionsTensor`: restrict the basis expansion
using `pushforward₀.mapIso`, then compose with the affine external-section comparison.
The original signature and its public imports are unchanged. One proof-only import
provides the two new intermediate statements through its
public construction import. The geometric helper imports its two planned component
comparison modules privately; ScalarGlobalSectionsComparison is public-transitive
through those component modules.

`PicardConstantSectionsTensor` constructs a constant vector-space presheaf, its
structure-ring map, presheaf extension of scalars, and pointwise tensor with G.
All data and functoriality proofs are real constructions, with no `sorry` in definitions.
The construction is independent of a basis and of the external direct image.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.Modules.exists_external_coproduct_comparison`.
This is a decomposition, not a net reduction of holes. Added two strictly separate
obligations, each in its own module:

- `AlgebraicGeometry.Scheme.Modules.exists_picard_constant_sections_tensor_basis`
  (`lem-sc-picard-constant-sections-tensor-basis`): purely algebraic basis expansion;
  no first scheme, quasi-compactness, affine diagonal or quasi-coherence.
- `AlgebraicGeometry.Scheme.Modules.exists_external_constant_sections_tensor_comparison`
  (`lem-sc-picard-external-coefficients-pushforward-tensor-comparison`): geometric
  affine external-section comparison; no basis, index type or coproduct.

No other holes were added. All three modules compile with lcompile.py --all.

## No longer needed

No original imports were removed. The redundant added direct proof import of
PicardConstantSectionsTensor was removed; the geometric comparison already publicly
imports it. No library module is thereby pruned. The original sheafification dependency
`def-weil-presheaf-modules-sheafification` is not used by the new composition:
this is entirely an isomorphism of presheaves, before sheafification. The original
open-immersion and external-section dependencies remain within the geometric
intermediate's plan, via `ExternalSectionsOpenComparison` and
`ExternalGlobalSectionsTensorAffineRight`; they are not pruned from the overall route.
Specifically, every old proof dependency
is accounted for: def-sc-scalar-global-sections-comparison and
lem-sc-external-global-sections-tensor-affine-right move to the geometric helper;
lem-weil-pbc-open-immersion-module-pullback-restriction is used through the helper
plan of lem-sc-external-sections-open-comparison. Only
def-weil-presheaf-modules-sheafification is absent from the new proof plan, although
the presheaf categories themselves remain statement dependencies.

The invalid prior sandbox helper module
`PicardExternalCoefficientsPushforwardCoproductComparisonNatIso` is removed from this
attempt; it was never a repository module and is not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong

The prior attempt merely renamed the entire target as a new helper. That did not
reduce it. This attempt separates the two isomorphisms displayed in Stacks Tag 0BED
using an explicit middle object. Presheaves of modules have dependent coefficient
rings, so their components assemble with `PresheafOfModules.isoMk`, rather than
ordinary `NatIso.ofComponents`.

## New nodes

`lem-sc-picard-constant-sections-tensor-basis` records the constant coefficient
construction and algebraic basis-expansion obligation. The construction's pullback
is a standard left adjoint determined up to natural isomorphism by its adjunction;
no arbitrary witness of a mere unproved existence theorem is chosen.

`lem-sc-picard-external-coefficients-pushforward-tensor-comparison` records the affine,
basis-independent tensor calculation and restriction naturality. It depends on the
constant-tensor construction, not on the basis theorem's conclusion. Empty bases,
empty opens, empty X and zero coefficients satisfy the same tensor formulas.

## Second reading by W4

1. Compared every delivered module with the read-only repository. The sole existing
   declaration, exists_external_coproduct_comparison, retains its signature and
   docstring byte for byte. Its public imports remain unchanged. The two sibling
   modules and their declarations are new; there is no forced adaptation or
   statement/definition change to an existing interface. Verdict: pass.
2. Compiled all three modules in import order using lcompile.py. Exactly the two
   named split theorems retain whole-proof sorry; there is no forbidden command or
   holed definition. A scratch copy with #print axioms checked the original theorem,
   both split theorems, and all three new definitions. The definitions use only
   propext, Classical.choice, Quot.sound; the theorems additionally use sorryAx
   from the two declared obligations. The Mathlib pullback is a genuine left
   adjoint with a proved adjunction, not arbitrary data from an unproved existence
   statement. Verdict: pass as a decomposition, not a completed proof.
3. Read both split statements, their proof docstrings and nodes. The algebraic
   obligation applies to arbitrary M, G and Y without X or quasi-coherence; the
   geometric obligation has neither basis nor coproduct. Neither restates the
   original item. Read the affine-open calculation and displayed tensor/basis
   factorization in [Stacks Tag 0BED](https://stacks.math.columbia.edu/tag/0BED).
   Its degree-zero equalizer calculation needs no higher-cohomology vanishing.
   Basis expansion, extension of scalars and tensor balance prove
   the asserted formulas, including I empty, M zero, G zero, empty Y and empty
   affine opens. An empty X gives zero global sections and zero external image.
   Independently searched Mathlib via leanfinder, loogle and grep with different
   queries, and searched Sheaf and the upstream algebraic-geometry sources. Found
   pointwise tensor, free presheaves, pullback adjunction and isoMk ingredients,
   but no complete existing comparison. LeanSearch returned an internal server
   error and is recorded as unavailable, not as a no-match result.
   Closing either obligation requires
   constructing presheaf component maps and their naturality, beyond a short
   application of an existing theorem. Verdict: true, needed, strictly separate
   parts of the displayed source calculation; both remain open.
4. Read from the parent composition downward and inspected the existing affine
   external-section and open-comparison declarations. No shorter complete proof
   was found. Removed the redundant direct proof import of the construction;
   imported the geometric helper's planned component comparisons privately.
   The pruning section now accounts explicitly for all four old proof_deps.
   No library module is asserted pruned. sk-prop-av-cube.json has empty realized
   statement/step lists; this change stays below that unit and preserves its
   cube-theorem route. Verdict: pass.
5. Checked all three nodes against the Lean signatures and proof routes; each
   proof_deps list is exactly the union of its proof steps' uses. The existing
   node changes only proof, proof_deps and proof_origin as decoded JSON. New nodes
   have the required source, proof, search, created, blueprint, chapter, unit and
   Lean fields. Corrected the geometric node's copied algebraic searches and
   made both new statements self-contained with explicit definition citations.
   Verdict: pass.

Second reading changed the redundant proof import, added the geometric helper's
planned proof imports, corrected new-node statements and search metadata, and
completed the old-dependency accounting. No theorem signature or proof was altered.
The original hole was closed by adding two lower holes: 1 closed, 2 added, net -1
before any import-closure changes; the maintainer's pinned sorry ledger determines
the actual closure totals. No change record is needed for existing interfaces.
