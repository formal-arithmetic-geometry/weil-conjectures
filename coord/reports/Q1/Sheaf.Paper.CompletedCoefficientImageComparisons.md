## What changed

Proved `WeilConjectures.CompletedCoefficientPushforward.coefficientComparisons_exists`
with its original statement and supplied source/target models. Constructed the ordinary
identity-on-sections coefficient squares, chose normalized total derived images, and
proved their normalization and all identity, quotient-composition and projection equations.
The coherence argument uses private lemmas for arbitrary supplied exact derived models,
so it does not replace those models by canonical ones.

Added the proved theorem `restrictionPushforward_acyclic` in
`Sheaf.Paper.ProEtaleRestrictionPushforwardAcyclic`. Its proof restricts a resolution to
all slice sites, applies the existing scalar-restriction sections theorem, and detects
quasi-isomorphisms sectionwise. Naturality of the supplied derived unit finishes the proof.
All added imports are proof imports. No existing public interface or shared definition changed.

Validation: both Lean modules passed remote single-file compilation within 60 seconds
(27.1 seconds for acyclicity and 45.7 seconds for the complete comparison proof).
Profiling and diagnostic commands were removed. The delivery tool reached the push
after compilation and server preflight on the earlier attempts. The current resumed session also passed compilation and server preflight, then failed at the required delivery push. The server reported `unable to create temporary file: No space left on device`, `failed to write object`, and `remote unpack failed: unpack-objects abnormal exit`. No push succeeded; all proof and node files remain retained in this sandbox. The launcher scripts and shared repository were not modified.

## Proved and sorry left

Closed the original one hole:
`WeilConjectures.CompletedCoefficientPushforward.coefficientComparisons_exists`
(`lem-pur-completed-coefficient-image-comparisons`).

The new theorem
`WeilConjectures.CompletedCoefficientPushforward.restrictionPushforward_acyclic`
(`lem-pur-proetale-restriction-pushforward-acyclic`) is proved, not a split-off hole.
There are zero `sorry` occurrences in the two delivered Lean modules. Holes added: zero.
No existing holed statement was weakened, renamed, or repackaged as an assumption.

## No longer needed

The item's separate planned dependency
`lem-pur-ringed-derived-composition-cocycle` is unnecessary: normalized-square naturality
and the ordinary section identities prove all three coherence laws directly.

The planned small-site derived-composition and site-equivalence transport nodes are no
longer direct proof dependencies of this item. The derived-composition and small-model
infrastructure is still used inside the existing sections and Grothendieck-category lemmas;
this delivery does not assert that those modules are globally unused. No module was
withdrawn. The original item stub contained only its public model import, which is retained;
no original Lean import line was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The proposed direct small-site application
cannot be applied literally to the independent universes and arbitrary supplied models.
The existing sections theorem already treats essentially small sites in the coefficient
universe. Checking a restricted resolution on each slice closes the needed acyclicity
step without constructing a second full transport of the geometric square.

The unit route is retained. The proof includes identity coefficient maps and identity
quotients, uses no nonzero-ring or flatness hypothesis, and retains the supplied source,
target and structural map by reflexivity.

## New nodes

`lem-pur-proetale-restriction-pushforward-acyclic` is a proved single-coefficient
acyclicity lemma. It has no target horizontal comparison, no choices of target exact
models, no tower, and no coherence obligation. Its source, complete proof, independent
universes, Mathlib searches and Lean attachment are recorded in the new node JSON.
No change record is needed because no existing signature or definition changed.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
