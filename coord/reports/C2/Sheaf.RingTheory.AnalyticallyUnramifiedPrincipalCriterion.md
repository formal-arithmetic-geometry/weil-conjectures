## What changed

Proved `isAnalyticallyUnramified_of_principal_quotient`, keeping its signature and public
imports unchanged. The proof follows Tag 0330: height one and regularity give DVRs;
codimension-one analytic unramifiedness gives domain localizations of the completion;
associated-prime localization injectivity divides square-zero elements by the image of t;
flatness preserves cancellation, induction puts them in all powers, and Krull intersection
kills them. Mathlib's square-zero criterion concludes reducedness.

Added the proved module `Sheaf.RingTheory.QuotientAssociatedPrimesFlatBaseChange` to connect
the existing tensor Bourbaki formula to quotient rings. Its S-action is exactly the transported
action of that formula. The quotient-tensor equivalence is a real Mathlib construction.
No definitions, existing signatures, targets or other held modules changed.

## Proved and sorry left

Closed the sole original hole: `isAnalyticallyUnramified_of_principal_quotient`
(node `lem-weil-pbc-analytic-unramified-principal-criterion`).

Also proved `associatedPrimes_quotient_map_of_flat`
(node `lem-weil-pbc-associated-primes-flat-quotient`). Both delivered modules contain zero
`sorry`s. Holes closed: 1; holes added: 0; split off with sorry: 0. This is a proof from
existing stated dependencies, not a decomposition into new holes. The imported Bourbaki,
codimension-one DVR and localization-injectivity results still contain their existing holes;
this delivery does not close those downstream items.

## No longer needed

Removed `Sheaf.RingTheory.RegularLocalDimOneIffNormal` and its node
`lem-weil-pbc-regular-local-dim-one-iff-normal` from this proof's dependencies. The already
proved `IsRegularLocalRing.isDiscreteValuationRing` gives the needed DVR directly.
The proof uses its source module `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.

The direct import of `Sheaf.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange` moved to
the new quotient module: that module and its Bourbaki node remain necessary, and are not
pruned. All other original statement and proof imports remain needed. No other original
planned node or module is claimed pruned; completion Noetherianity, flatness, localness,
height bounds, codimension-one analytic unramifiedness, associated-prime injection and Krull
intersection still provide the same steps. No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

Validation: both delivered modules compile with lcompile.py --all, with no warnings.
The mandatory dry run `deliver3.py C2 Sheaf.RingTheory.AnalyticallyUnramifiedPrincipalCriterion
--no-push` completed successfully (OK, commit 634dd21026; nothing pushed).
The original theorem signature remains byte-for-byte identical; the existing node changes
only proof, proof_deps and proof_origin, and both Lean files meet the 100-character limit.

No false statements or target changes were found. The plan described the tensor-to-quotient
identifications but did not expose their quotient-associated-prime consequence as a Lean
interface; the new proved lemma supplies it. The planned regularity-to-normality equivalence
is unnecessary because the source library already proves the more directly useful DVR theorem.
LeanSearch was unavailable (Internal Server Error), recorded by msearch; Loogle, LeanFinder,
Mathlib grep and direct searches of both library roots were used.

## New nodes

`lem-weil-pbc-associated-primes-flat-quotient`: a strictly smaller general quotient base-change
step, proved from the existing Bourbaki formula, Mathlib quotient-tensor equivalence, the
Noetherian association/annihilator equivalence, and elementary ideal extension identities.
Source: Stacks Algebra Tag 0312 and the displayed formula in Tag 0330. The statement includes
no local-ring, domain, principal-generator, regularity, analytic-unramifiedness or reducedness
assumption/conclusion. For I=top the hypothesis is empty, for I=bot it specializes to ordinary
flat base change, and the zero algebra also makes the hypothesis empty. Searches are recorded
in the node and searches.jsonl. No change record is required: the new module is proof-only
for the original interface, and every existing declaration keeps its signature.

## Second reading by C2

1. Compared both delivered modules with the repository versions. The existing theorem
   signature is unchanged byte for byte; the added theorem is a new, separately stated
   quotient base-change result and no existing declaration was altered.
2. Compiled both files with `lcompile.py --all`; compilation succeeds with no warnings.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions.
3. Checked the added statement against the Bourbaki formula and quotient-tensor equivalence.
   It is strictly more general than the principal-quotient use, has no extra local or domain
   assumptions, and its edge cases (top, bottom, and zero quotients) specialize correctly.
   Searches found no duplicate declaration.
4. The proof follows the unit route: completion flatness, height one, DVR localization,
   codimension-one completion domains, associated-prime base change, square-zero descent,
   and Krull intersection. The removed regular-local-dimension-one equivalence is unused;
   the direct DVR theorem is shorter. Imports are pruned only where reported.
5. DAG proof, proof dependencies, proof origin, new node metadata, and the unit route agree
   with the Lean proof. No target statement or definition changed.

Changed during second reading: added this review record only; no Lean proof changes were
needed after compilation.
