## What changed

Replaced the body of `CochainComplex.residue_bottom_differential` without changing its
signature, visibility, or existing docstring. Its proof now derives fibre injectivity
using Mathlib exactness, applies the existing finite-projective residue-localization
lemma, descends along the resulting principal cover, and transfers projectivity to
opcycles via Mathlib's quotient isomorphism.

Added `Sheaf.RingTheory.PrincipalCokernelProjectiveDescent`, with the single remaining
statement `Module.injective_projective_cokernel_of_principal_cover`. All newly added
imports of the existing module are ordinary proof imports. The new module imports
only Away.Basic and FinitePresentation; the latter already supplies the tensor
and projectivity APIs, so their separate imports were removed.

## Proved and sorry left

Closed the original hole in `CochainComplex.residue_bottom_differential` by a genuine
reduction to the planned localization lemma plus a strictly smaller cover-descent
statement. Added one named hole:
`Module.injective_projective_cokernel_of_principal_cover`
(node `lem-sc-principal-cokernel-projective-descent`). This is a decomposition, not
an unconditional proof or positive net hole progress: one original hole closed,
one lower hole added, net zero before any import-closure pruning measurement.

The first reader's two categorical holes are now closed directly in the main proof:
the work formerly assigned to `CochainComplex.residue_fibre_injective` and
`CochainComplex.opcycles_projective_of_cokernel`. Their unpublished auxiliary module
and node were removed from the delivery. The existing dependency
`Module.finiteProjectiveCokernel_residue_localization` remains open upstream.

## No longer needed

The unpublished `Sheaf.Algebra.Homology.ResidueBottomAuxiliary` and its node
`lem-sc-residue-bottom-auxiliary` are no longer needed, since both categorical steps
are proved directly from Mathlib. The first worker's unused proof import
`Mathlib.CategoryTheory.Adjunction.Additive` was removed.

Of the original proof_deps:
- `lem-pc-finite-projective-cokernel-localization` remains directly used.
- `lem-weil-pbc-finite-projective-finitely-presented` remains directly used through
  its Mathlib match, `Module.finitePresentation_of_projective`.
- `lem-weil-pbc-finitely-presented-flat-module-projective` is no longer a direct
  dependency of the main reduction. It is explicitly retained in the descent node's
  proof plan. Its Mathlib module remains needed there; no library module is claimed
  pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's descent statement was false: take R = Z, M = 0, N = Z/2Z and
f = 0. N is finitely presented and every residue-field map from M is injective,
but its cokernel N is not projective over Z. The unpublished residue-only theorem
was removed and replaced with the principal-cover hypothesis actually furnished
by the existing finite-projective localization lemma. No existing statement was
changed and no change record is required for this replacement of unpublished work.

The first report omitted the third hole in
`CochainComplex.opcycles_projective_of_cokernel`, and both new nodes lacked proofs,
search records, blueprint ancestry and verbatim Lean signatures. These defects are
repaired. The initial compilation also found a long-line warning, a letI warning,
and an unused projectivity hypothesis; the final files compile without warnings.

## New nodes

`lem-sc-principal-cokernel-projective-descent` isolates descent of an injective map
and its projective cokernel from principal neighborhoods covering every prime.
Its source is Stacks Algebra, [Section 10.23](https://stacks.math.columbia.edu/tag/00EN),
[00HT](https://stacks.math.columbia.edu/tag/00HT) and
[00NX](https://stacks.math.columbia.edu/tag/00NX). Its docstring and node give the
annihilator argument, finite relation presentation, explicit tensor-quotient
comparison, flatness descent, and final finite-presentation criterion.
LeanSearch was unavailable (HTTP internal error); LeanFinder, Loogle and grep ran
and are recorded in searches.jsonl. Searches located local injectivity and
projectivity APIs, but no exact tensor-cokernel principal-cover theorem. No change
records or forced adaptations are included.

## Second reading by N4

1. Compared every delivered module with the repository. The existing module has
   exactly the same declaration signature and public imports; only its proof,
   declaration-local elaboration option and three ordinary proof imports change.
   The second module is new. No definitions or target statements changed. PASS.
2. Compiled the initial files and the repaired files through lcompile.py, in import
   order. The repaired files compile without errors or warnings. No forbidden
   declarations, hollow definitions or arbitrary witness constructions occur.
   The only explicit sorry is the named descent theorem documented above.
   Appended #print axioms for both delivered declarations to a scratch copy:
   both report only propext, Classical.choice, Quot.sound and the expected sorryAx.
   PASS subject to the declared open dependencies.
3. Rejected the original descent statement by the zero-source torsion-module
   counterexample above. The replacement requires injectivity and projectivity
   on an actual cover. Checked zero ring, zero source, zero target, identity map,
   field and disconnected-ring cases: all agree with the complete docstring proof.
   In particular the false Z/2Z example no longer satisfies its hypotheses.
   Searched Mathlib through all required search categories and searched lean/ and
   dag/nodes by localization, cokernel, residue and projectivity concepts. The
   surviving statement is strictly the descent part, with no complex or homology
   assertions. PASS after replacement.
4. Proved both categorical parts directly using
   ShortComplex.exact_iff_isZero_homology, exact_iff_mono, homologyIsoSc',
   ModuleCat.mono_iff_injective, opcyclesIsoSc', moduleCatOpcyclesIso and
   Module.Projective.of_equiv'. The main proof now actually applies the planned
   finiteProjectiveCokernel_residue_localization. All old proof_deps are accounted
   for above. Read dag/units/sk-prop-av-cube.json: its realized statement and step
   lists are empty, and this work refines only the single-differential algebra
   below that unit; its statement and route are preserved. PASS.
5. Updated the main node's proof, proof_deps and proof_origin to the reduction
   actually compiled. Completed the new node with self-contained statement,
   source, detailed proof steps, their dependency union, recorded searches,
   blueprint ancestry, creation fields and the verbatim Lean declaration.
   Removed the now unnecessary unpublished auxiliary node. PASS.

Changes made by this second reading: eliminated both categorical holes; replaced
false residue-only descent with principal-cover descent; removed the auxiliary
module and unused proof import; fixed compiler warnings; completed DAG metadata;
removed redundant tensor/projectivity imports from the new module; and corrected
the report to describe one remaining hole and net-zero decomposition.
