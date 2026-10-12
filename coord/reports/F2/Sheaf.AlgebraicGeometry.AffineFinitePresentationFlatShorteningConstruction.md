## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.affine_finitePresentation_flat_shortening_construction`
by a complete Lean induction on the natural upper support bound. The original signature
and all public imports are unchanged. The base and already-short cases use the input
complex and the identity homotopy equivalence. In the remaining successor case the proof
uses zero top residue homology and the zero next term to prove that every residue
pullback of the incoming differential is epic. An affine splitting criterion and a
single-step cancellation theorem provide the shorter complex. Mapping the cancellation
homotopy equivalence through each residue pullback and applying `toHomologyIso` transfers
all the residue vanishing hypotheses. The induction hypothesis gives the final model;
`HomotopyEquiv.trans` supplies its equivalence to the original complex.

Added two supporting modules, each containing one public theorem and its complete proof
in words: `Sheaf.AlgebraicGeometry.AffineResidueEpiSplitting` and
`Sheaf.AlgebraicGeometry.SplitTopDifferentialCancellation`. These isolate the affine
Nakayama/projectivity step from the cancellation of one already-split differential.
Updated the original node's proof, proof_deps and proof_origin to the actual induction.
No definition, existing statement, target, or other existing module was changed.

The assigned proof compiled locally, including the derivation of fibre epimorphy from
exactness, support monotonicity, transfer through homology isomorphisms and composition
of homotopy equivalences. Both supporting modules compiled in import order with it.
Edge cases checked mathematically: b=0, b≤d, d=0, m=0, zero top term and the empty affine
scheme. The splitting statement does not require finite presentation of its source.
The cancellation statement requires neither affineness nor any residue vanishing.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.affine_finitePresentation_flat_shortening_construction`
(node `lem-pc-affine-finite-presentation-flat-shortening-construction`).
There are no sorries left in the assigned module.

Added two holes:

- `AlgebraicGeometry.Scheme.Modules.affine_isSplitEpi_of_residue_epi`, node
  `lem-pc-affine-residue-epi-splitting`, in `AffineResidueEpiSplitting.lean`.
- `AlgebraicGeometry.Scheme.Modules.exists_split_top_differential_cancellation`, node
  `lem-pc-split-top-differential-cancellation`, in `SplitTopDifferentialCancellation.lean`.

This is a decomposition: one upper hole closed, two strictly smaller holes added;
it is not an axiom-free proof of the underlying cancellation theorem. The first new
statement concerns a single module morphism, with no complex or support bounds. The
second removes just one split top differential and has no residue hypothesis or final
bound d. The induction and all the glue in the original module are proved in Lean.
Neither supporting statement rephrases the original arbitrary-bound shortening result.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.RingTheory.Nakayama`
- `Mathlib.RingTheory.LocalProperties.Basic`
- `Mathlib.RingTheory.Finiteness.Projective`
- `Mathlib.RingTheory.Flat.EquationalCriterion`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`

The original node no longer directly uses
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-quasi-coherent-finite-type-affine` or
`lem-weil-pbc-finitely-presented-flat-module-projective`; those steps are assigned to the
supporting nodes, which still need these facts. Consequently no underlying mathematical
node is claimed globally unnecessary. No unit statement or unit proof step was bypassed.
No unused new proof import remains in the assigned module.

## Where the brief, the DAG or earlier work was wrong

The original node's second step included both the Nakayama argument and explicit
kernel/identity-pair cancellation, but its stated dependency only supplies projectivity.
None of its existing declarations states the required cancellation. The two new
statements make those missing parts separately available instead of hiding them in the
inductive proof. Existing affine criteria are still needed below them.

Read Stacks Tags 068V, 068U, 08EB, 00NX and 00MT online. Tag 068V is a derived perfectness
criterion, and 00MT is unit-entry cancellation for finite free complexes; neither is
claimed to state the new sheaf split-surjection theorem verbatim. The explicit
finite-projective cancellation argument is written by F2, following the existing node's
source specialization. Search found only ingredients in Mathlib: projective splitting,
localization detection, homotopy mapping and truncation interfaces. LeanSearch returned
Internal Server Error, recorded as unavailable. LeanFinder and logged Mathlib grep ran
successfully. Loogle's unqualified `IsSplitEpi` query was rejected as an unknown identifier.

The node ancestry script returned None because earlier created.item entries use module
names rather than node ids. The new nodes inherit the assigned node's already recorded
blueprint ancestor `lem-pc-coherent-hi` and the same shortening sentence. The unit's
realized lists are empty; its fixed perfect-complex/Nakayama shortening route is retained.
Whole-blueprint searches for split top differential and residue surjectivity returned
no duplicates. Read the related affine free unit-cancellation and finite locally free
residue-isomorphism declarations: neither applies here (arbitrary finite projectives and
residue epimorphisms, respectively).

## New nodes

`lem-pc-affine-residue-epi-splitting` states that residue epimorphy makes a morphism onto
a finitely presented flat quasi-coherent module on an affine scheme split. Its proof
identifies the finite section cokernel, applies local Nakayama and maximal-localization
detection, then splits by target projectivity and returns by tilde. Its only new Lean
module is `Sheaf.AlgebraicGeometry.AffineResidueEpiSplitting`.

`lem-pc-split-top-differential-cancellation` states the removal of one already-split top
differential in a sheaf complex. Its proof explicitly gives the kernel replacement,
chain maps, a homotopy supported at one adjacent pair, and termwise-property preservation
through retractions. Its only new Lean module is
`Sheaf.AlgebraicGeometry.SplitTopDifferentialCancellation`.

Both nodes are in sec-picard-framework and sk-thm-picard-coherence, with actual logged
Mathlib searches and source/proof records. No change record or forced adaptation is
necessary, since every existing interface remains unchanged.

## Second reading by F2

1. Compared the assigned module with the repository version. The theorem signature and all existing declarations are unchanged; only proof imports and proof bodies differ. Verdict: pass.

2. Compiled all three sandbox modules with `lcompile.py --all`. There are no compiler errors, forbidden declarations, or unnamed `sorry`s. The two remaining `sorry`s are the named split-off theorems listed above. Verdict: pass, subject to those nodes.

3. Read both split-off statements against the affine residue splitting and one-step contractible-pair arguments. Each is strictly smaller than the original shortening statement, has a source and proof explanation, and is not a duplicate found in the library or Mathlib. Edge cases include the zero bound, `m = 0`, and the empty affine scheme. Verdict: pass.

4. Checked the induction from the top downward: the already-short case is identity, the successor case obtains residue epimorphy from exactness, splits the top differential, transfers homology vanishing through the homotopy equivalence, and recurses. Removed imports are recorded above and no unused proof import remains. Verdict: pass.

5. Checked the assigned node and both new node records: declarations, proof steps, dependencies, origins, modules, and split status agree with the Lean files. The unit's shortening route remains represented by the original node and its dependencies. Verdict: pass.

Changed after this reading: added this review record only; no Lean statement or proof was altered.
