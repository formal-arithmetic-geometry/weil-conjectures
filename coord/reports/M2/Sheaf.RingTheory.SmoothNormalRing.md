## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.SmoothNormalRing`, preserving the exact
signature of `RingHom.Smooth.isNormalRing`. Two proved private helpers implement the
Noetherian case and the normal-domain case. The main proof performs the reduction
at each target prime using the tensor-product localization, extension and contraction
of primes, and an explicit equivalence of the two localizations.

Added `Sheaf.RingTheory.SmoothNormalDomainApproximation`, with one public intermediate
theorem constructing a filtered diagram whose objects are smooth algebras over
Noetherian normal base rings, together with a ring equivalence from its colimit to
the given smooth algebra. This is the structural content of steps 3-6 of the old
plan. It does not assert normality of the diagram objects or of its colimit. The
item proves those assertions separately, using the Noetherian helper and the existing
filtered-colimit normality theorem. Added its node and updated the item's proof,
proof_deps and proof_origin to match this Lean reduction.

Added proof imports of `Mathlib.RingTheory.Smooth.Flat`,
`Mathlib.RingTheory.Localization.BaseChange`, and the new approximation module.
The public imports and all existing public signatures are unchanged.

Validation: both sandbox modules compile together with lcompile.py. The Noetherian
helper uses the stated flat-normal-fibres, smooth-regular-ascent and regular-normality
lemmas. No new mathematical axiom or definition is introduced. The complete proof is
relative to those existing statements and the single new approximation statement.

## Proved and sorry left

- `RingHom.Smooth.isNormalRing` (node
  `lem-weil-pbc-smooth-over-normal-ring-normal`): complete Lean proof, no direct `sorry`.
- Private helpers `RingHom.smooth_normal_noetherian` and
  `RingHom.smooth_normal_domain`: complete Lean proofs.
- The only `sorry` in this delivery is
  `RingHom.Smooth.exists_noetherian_normal_model_colimit`, node
  `lem-weil-pbc-smooth-normal-domain-approximation`, in the new module. Its whole
  proof is `by sorry`, and its docstring and node describe the normalization,
  directedness and tensor-colimit construction. Existing imported statements still
  contain `sorry`; their proofs are not changed or claimed as closed here.

Edge cases checked: the original normal-ring condition remains vacuous on the zero
ring, and the proof introduces a target prime before forming a contracted prime.
The new approximation theorem assumes a domain only for the base; the smooth
algebra may be the zero ring or have several components. Its index is filtered and
therefore nonempty. Residue-field fibres may be zero; normality is stated at prime
localizations and does not impose an unjustified domain condition on the whole fibre.
Independent source and target universes are preserved; approximation diagrams live
in their maximum universe.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.DirectedColimitBaseChangeElementwise` (node
  `lem-weil-pbc-directed-colimit-base-change-elementwise`). This specialized lemma
  tensors over a distinguished diagram index, which need not be the descended R₀.
  It is no longer needed by this route; the approximation node instead cites
  `lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise` over the fixed base R₀.
- `Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite` (node
  `lem-weil-pbc-finite-type-z-domain-normalization-finite`). Its finiteness work is
  transferred to the approximation node, not globally pruned.

The following former direct proof dependencies now belong to the approximation
node, rather than the main theorem: `lem-weil-pbc-smooth-algebra-finite-type-model`,
`lem-weil-pbc-integral-closure-algebraic-extension-normal`,
`lem-weil-pbc-finite-type-z-domain-normalization-finite`,
`lem-weil-pbc-localization-normal-domain`,
and `def-weil-pbc-category-colimit`.

`lem-weil-pbc-tensor-cancel-base-change` is no longer needed by either node's route:
the diagram is formed directly as A tensor S₀ over the fixed descended ring R₀.
There is no need to rewrite all tensor products over the normalization R₀'.
This is the actual pruning; the main theorem never imported a separate module for it.

The definitions `def-weil-pbc-noetherian-ring`, `def-weil-pbc-smooth-ring-map` and
`def-weil-pbc-normal-ring` are no longer separately listed as direct proof
prerequisites; their notions remain present in the statements and cited lemmas.
No other original proof import was removed.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed hypothesis was found. The Noetherian part fits the
existing declarations exactly. The earlier plan's tensor-cancellation step is
unnecessary when every model is kept over R₀. For this route the general
`CommAlgCat.filteredColimit_tensorProduct_elementwise` statement is the fitting
colimit lemma: the original distinguished-index version would first require a
normalization and rebasing of R₀. The lengthy construction of the
directed normal bases and the tensor-product diagram was not available as a single
existing Lean declaration, so that strictly structural part is split off.

The remote repository contains only the literature lists, not algebra.tex or the
blueprint Markdown files. The unit record was read, and Stacks Tag 033C was checked
at https://stacks.math.columbia.edu/tag/033C, including its separate Noetherian,
localization and normal-domain approximation paragraphs. LeanSearch returned an
Internal Server Error; the node records this as unavailable, not as a negative
search. LeanFinder, Loogle and source searches ran successfully. The searches found
Mathlib's smooth Noetherian descent, but not the required normal-base diagram.

## New nodes

`lem-weil-pbc-smooth-normal-domain-approximation`, module
`Sheaf.RingTheory.SmoothNormalDomainApproximation`, declaration
`RingHom.Smooth.exists_noetherian_normal_model_colimit`. This packages the
normalization-and-colimit construction of Stacks Tag 033C, third paragraph. Each
model includes its actual smooth map from a Noetherian normal base; normality of
the stages and the final ring is proved in the original module. No change record
is needed: existing statements, definitions and public imports are unchanged.

## Second reading by M2

1. **Statements and accidental changes.** Compared the delivered item module with
   the repository version. The statement of `RingHom.Smooth.isNormalRing` is
   byte-for-byte unchanged; only its proof and proof-only imports changed. The
   new approximation statement is recorded verbatim in its node and has no effect
   on an existing declaration.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py
   --all`; both compile without errors. The item theorem has no direct `sorry`,
   while the deliberately split approximation theorem is the only new `sorry`.
   Its node, docstring, and source are present. The approximation theorem's
   expected dependency on `sorryAx` is confined to that split theorem.

3. **Split-off statement.** Checked the approximation statement against the
   filtered normal-base construction in Tag 033C. It is strictly structural and
   does not restate the item: it supplies a filtered colimit and smooth maps from
   Noetherian normal bases, while asserting no normality of the stages or target.
   Searches recorded in the node found no Mathlib or Sheaf declaration providing
   this result.

4. **Pruning and imports.** The proof uses the shorter Noetherian/fibre and
   localization route, with the approximation node supplying the structural
   descent. The removed directed-colimit base-change and finite-normalization
   imports are no longer used; the node proof dependencies and report list the
   corresponding pruning. The unit's realized route remains represented by the
   item and approximation nodes.

5. **DAG agreement.** Updated proof, proof dependencies, and proof origin match
   the Lean proof. The new node has the required statement, source, proof steps,
   searches, Lean record, chapter, and unit fields. No target or existing public
   signature was weakened or changed.

**Changes made:** added this second-reading record only; no proof or statement
changes were needed after review. The delivery remains a CODEX-class delivery
because it adds the documented approximation module and node.

