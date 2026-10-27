## What changed

Replaced the sole sorry in `Sheaf.Paper.PulledKoszulTowerChainComparison` by a
complete Lean proof from a smaller ordinary tensor-comparison statement and the
existing principal Koszul replacement theorem.

The proved private lemma `WeilConjectures.completed_pull_good` presents the actual
`CompletedTowerIndependent.pull` as inverse image followed by scalar extension,
using the existing structural-map and supplied-adjunction proofs. Uniqueness of
left adjoints gives its comparison with `pull`. The existing
`SheafOfModules.isKFlat_ringedToposPullback` proves K-flatness and flatness of every
term; both properties transport across the comparison. This lemma applies to P
and, using the source principal replacement theorem, to every source tower level.

Apply the principal replacement theorem on X to GP for the actual target
augmentation. `HomologicalComplex.quasiIso_iff_evaluation` proves the transposed
augmentation is a quasi-isomorphism. The existing `comparison_naturality` gives
the last asserted square. These are proofs about the specified comparison maps;
ordinary pullback is never asserted to preserve arbitrary quasi-isomorphisms.

The ordinary normalized tower isomorphism is isolated in the new module
`Sheaf.Paper.PulledKoszulTowerNormalizedIso`. Its theorem is exactly the scalar,
two-term tensor and strict-transition subargument of original proof steps 2--4.
It excludes all goodness and augmentation assertions. The original theorem's
signature, including both invertibility hypotheses and both universes, is unchanged.
Updated the original node's proof, proof dependencies and proof origin accordingly.

Validation: both modules compiled through lcompile.py. The original module
compiled with the full new proof on the first attempt; two unused-hypothesis
warnings were subsequently repaired without changing the signature.

## Proved and sorry left

Closed the original direct hole in
`WeilConjectures.pulled_koszul_tower_chain_comparison`
(node `lem-a1-pulled-koszul-tower-chain-comparison`). The original module now
contains zero sorrys. Its private `WeilConjectures.completed_pull_good` is proved.

Added exactly one hole:
`WeilConjectures.pulled_koszul_tower_normalized_iso`
(node `lem-a1-pulled-koszul-tower-normalized-iso`), in its own new module.
Its proof is exactly `:= by sorry`; its docstring and node give its source and
complete ordinary tensor/basis proof in words.

This delivery is a decomposition, not a net hole closure: one original hole
closed and one strictly smaller hole added, net zero. Preservation of goodness,
source-tower-level goodness, target levelwise augmentation, transposed
augmentation and augmentation naturality are all discharged in the main module.
Only the ordinary normalized tensor/tower isomorphism remains.

## No longer needed

Removed the direct proof import
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` from the main module:
the remaining ordinary tensor subargument is now in the new module.
The coherence node remains a proof dependency of that subargument and is not
claimed globally pruned. The new module needs only the normalization-definition
module to state its remaining theorem, so it does not import the generic
coherence proof module before using it. Removed the exploratory direct `import all` of
`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`: the K-flat isomorphism
transport already supplied by `KFlatRingedToposPullback` suffices.

The original node no longer directly cites
`def-weil-pbc-completed-pullback`, `def-sp-completed-uniformizer-section`,
`lem-pur-cochain-pullback-tensor-coherence`, `def-pc-tensor-complex-sheaves`, or
`def-weil-abstract-derived-category` in its proof. The normalized-isomorphism
node retains the scalar/tensor dependencies it actually needs. The transposed
augmentation is proved in the abelian category of complexes, by evaluation,
and needs no derived-localization argument. The completed pullback presentation
uses the existing independent-universe definition node directly.

No existing module or declaration is withdrawn. No entire mathematical
subargument or unit route is claimed pruned; the reduction isolates the remaining
ordinary tensor calculation while completing the other original steps.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The generic preservation
statement fits after identifying the specified pullback with the scalar-extension
presentation; this identification and the transport of both goodness properties
are written in Lean, rather than assumed definitionally.

The stated dependencies do not directly supply the principal-basis tower
specialization of ordinary cochain tensor coherence. Its explicit scalar,
two-term cone, total-summand and strict-transition glue is the remaining new
lemma. The downstream balanced finite-tower theorem contains related data but
cites this item in its proof plan, so it was not used as a circular shortcut.

The new ordinary isomorphism statement does not need invertibility of ell or
goodness of P. Checked its formulas on P=0, P=R[0], g=id, an empty scheme,
index n=0 (exponent 1), both Bool choices of Koszul degree, arbitrary total
degrees, and a non-flat completed structural map. The action unitor multiplies
coefficients and preserves t by all finite projections; no scalar crosses a
nonzero-degree factor. These checks require no missing flatness or boundedness
hypothesis. The new statement is strictly the original proof's ordinary
isomorphism subargument; it omits the separate homological conclusions proved
in the main module.

Read Stacks sites-cohomology.tex at lemma-pullback-K-flat (0G7E) and
lemma-pullback-tensor-product (07A4), sites-modules.tex at
lemma-tensor-product-pullback (03EL), and the current blueprint unit
sk-thm-dl-a1-upper. The unit route and its realized statements are preserved.
The generic cochain coherence dependency is used as the same ordinary tensor
tool already approved in the parent, not as a replacement geometric route.

## New nodes

`lem-a1-pulled-koszul-tower-normalized-iso`, module
`Sheaf.Paper.PulledKoszulTowerNormalizedIso`, states only the ordinary strict
Koszul tensor isomorphism, both basis normalizations and chain-map naturality.
Its three proof steps retain the original scalar, total-tensor and adjacent
transition calculations. Searches used LeanFinder, Loogle, LeanSearch, launcher
grep and local rg; Mathlib's free-module pullback comparison does not state the
two-term completed cochain/tower normalization. The all-chapter blueprint
search for Koszul found no identical blueprint statement. No change record is
needed: no existing definition, signature, attribute or public import changed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
