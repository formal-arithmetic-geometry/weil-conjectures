## What changed

Proved `AlgebraicGeometry.Scheme.exists_constructible_stratified_finite` in
`Sheaf.AlgebraicGeometry.ConstructibleStratifiedFinite`, without changing its signature.
Added two proof-only imports: `FlatFpLqfBoundedStratification` and
`QuasiFiniteLocallyQuasiFinite` (under `Sheaf.AlgebraicGeometry`). The existing
proof-only imports `FlatQuasiFiniteStratification` and
`HasUniversallyBoundedFibersOfIsLocallyQuasiFinite` remain used.

The proof compares the two existing degree filtrations on residue-field points. The bounded
filtration eliminates degrees above N from the compact-stratum filtration. Each closed
filtration complement is then a finite union of compact strata and is open, so its
constructibility follows from quasi-separatedness. Differences are constructible and
locally closed. A fully proved private helper realizes locally closed sets by vanishing-ideal
closed subschemes inside an open subscheme. The universal property makes each stratum
pullback finite locally free, and hence finite. Updated the item's DAG proof to this route. The public-import removal is recorded in
`coord/changes/ConstructibleStratifiedFinite-imports.md`; all 161 downstream modules
retain an independent Etale import at the sole direct importer and need no adaptation.

Source read: Stacks `more-morphisms.tex`, `lemma-stratify-flat-fp-qf` (07RZ) and the
07RY interfaces recorded in the node and Lean. The available local Stacks copy is under
`/home/ubuntu/c1-stacks-review/`; the repository's literature source is not materialized.

Searches run: launcher LeanFinder for a finite constructible stratification of a flat
separated quasi-finite morphism (Chevalley/image and quasi-finiteness results, no direct
stratification theorem); Loogle `Topology.IsConstructible, IsLocallyClosed` (no hits);
launcher grep `exists.*[Ii]mmersion|[Cc]onstructible.*stratif` (factorization criterion, no
ready-made realization theorem); direct rg searches of both library roots and Mathlib.

## Proved and sorry left

Proved the sole original sorry:
`AlgebraicGeometry.Scheme.exists_constructible_stratified_finite`
(node `lem-weil-pbc-etale-separated-stratified-finite-intermediate`).
Also proved the private helper `exists_immersion_of_locallyClosed`.
No sorry remains in the delivered module, and no new sorry or module was introduced.

This is a stage-3 proof from existing stated declarations. Its dependencies still include
`Hom.exists_closed_stratification_of_flat_quasiFinite`,
`Hom.exists_flat_fp_lqf_bounded_stratification`,
`Hom.hasUniversallyBoundedFibers_of_isLocallyQuasiFinite`, and
`Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact`.
It does not certify that the transitive closure is sorry-free.

Local compilation passed with no warnings. All four proposed proof imports passed
`tools/import_direction.py may`. Edge cases require no extra hypotheses: for bound zero
there is one degree-zero stratum; on an empty base all strata may be empty. No nonempty,
positive-degree, affine-base, or Noetherian assumption was added.

## No longer needed

Removed the direct public import `Mathlib.AlgebraicGeometry.Morphisms.Etale`, which the
statement and proof do not use. All other original public imports supply statement notions;
all four proof-only imports each supply a theorem actually applied.

The proof does not need `lem-weil-pbc-qcqs-scheme-spectral` or
`lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`; both were removed from this
node's proof dependencies. Constructibility is obtained directly with
`IsCompact.isConstructible`, complement, and difference. No separate spectral-space
instance, spectral-topology module, or reduced-induced-closed-subscheme theorem is needed.
The closed-subset/vanishing-ideal Mathlib leaf remains needed. These are local dependency
removals; other target paths may still require the removed nodes.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or signature change. The original single-step plan omitted the Lean
glue comparing a bounded filtration to the compact-stratum filtration. Their stated universal
properties are sufficient to write that comparison without a new lemma with sorry.
The source library's current `Topology.Stratification` already requires constructibility;
the proof supplies that field as well as the theorem's explicit constructibility conclusion.

The additional quasi-finite/local-quasi-finite equivalence
`pqf-lem-qf-locqf-qc` is used as a standard tool, as in the existing filtration proofs. It
belongs to another unit, but does not replace any unit statement or step. The bounded
stratification node is in the same `sk-thm-p1` unit. All its realized statement and step
nodes remain untouched. No new node or statement-change record is needed; the import-visibility record is named above.

The initial dry run required an import-visibility change record, now supplied. Its
second-reading requirement is deferred by deliver3.py for a first-worker dry run;
the second reader writes that section. No section was fabricated by this worker.


## Second reading by E1

1. PASS: compared the whole delivered Lean module and existing DAG node with the
repository versions. The sole existing theorem signature is byte-for-byte identical;
there is no changed definition or target statement. The public Etale import removal
is declared in `coord/changes/ConstructibleStratifiedFinite-imports.md`. Read the sole
direct importer and verified its independent public Etale import.
2. PASS: local compilation is clean. No sorry or forbidden declaration occurs in the
module. A scratch copy with `#print axioms` for both declarations shows only propext,
Classical.choice and Quot.sound for the private helper; the main theorem additionally
has sorryAx from the existing open filtration dependencies. No new axiom is introduced.
3. PASS: zero split-off statements. Read the fully proved locally-closed immersion helper:
it is direct glue from the existing closed-subset/vanishing-ideal Mathlib leaf, not a
renaming of the item. Independently searched library, upstream and Mathlib with
`IsLocallyClosed`, `range_subscheme`, and immersion/stratification queries; no shorter
matching realization or general finite-stratification theorem was found. Checked empty
subsets, an empty base, and bound zero: empty stratum schemes are allowed, the singleton
index Fin 1 covers the degree-zero case, and no positivity or nonemptiness is assumed.
4. PASS: read the two filtration interfaces and followed the proof top down. Their
universal properties at residue-field points give precisely the same strata; monotonicity
and the bound remove all high indices. The finite union complement argument correctly
uses quasi-separatedness to obtain constructibility. Every proof-only import supplies
an applied theorem. Both removed old proof dependencies are listed in No longer needed;
the unchanged sk-thm-p1 realized statement and steps are not bypassed.
5. PASS: checked each proof dependency's declaration or Mathlib match and the union of
step uses against proof_deps. The node's six steps and proof_origin describe the actual
Lean proof, including the filtration comparison and vanishing-ideal realization.

Second reading changed documentation only: corrected the count of newly added imports
(two added, two retained), in this report and the import-visibility change record. No
repair to the Lean proof or DAG route was needed.
