## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_affine_finite_module_presentation`
with a complete Lean reduction along the canonical affine isomorphism. The existing
`perfect_iff_affine_bounded_projective` supplies the complex, its finite terms and the
presentation on Spec A. The final isomorphism is an explicit composition of the inverse
counit, the image of the affine presentation, and the localization comparison.
The existing statement, universes, visibility and `affineModuleComplexFunctor` definition
are unchanged.

Added three general transport modules, each with one public theorem and a matching node:
`SchemeIsoDerivedEquivalence` constructs the derived equivalence and its natural
localization comparison from Mathlib, with no sorry;
`SchemeIsoDerivedQCoh` proves quasi-coherence preservation from exact homology comparison
and the already-proved source affine pushforward theorem;
`SchemeIsoPerfectTransport` isolates preservation of local strict perfectness.
All proof imports are non-public. The original presentation node now records this route.
No other existing module was changed and no forced adaptation is needed.

All four modules compile without warnings through the permitted launcher. The latest
complete compile took 5.3, 10.6, 4.4 and 17.5 seconds respectively. The `set_option` on
the main proof avoids costly elaboration of the composite functor while preserving its
signature. There is no universe relation: on Spec A the proof explicitly chooses standard
categories in universe u+1 and relates them to the given category on Y in universe w.

The remaining transport statement was checked on identity isomorphisms, arbitrary choices
of localization in different morphism universes, empty schemes, zero complexes and
unbounded objects that are only locally perfect. Its conclusion concerns local models,
not a global degree bound. Its comparison fixes the derived functor up to natural
isomorphism; no arbitrary witness is chosen to define data. The equivalence witness is
constructed in a proved theorem and used only inside a proposition proof.

Sources checked: [Stacks 08EB](https://stacks.math.columbia.edu/tag/08EB),
[Stacks 08CM](https://stacks.math.columbia.edu/tag/08CM), and the local Mathlib exact-functor,
homological-complex and localization-equivalence files. The new proof text is marked
agent-written, since the isomorphism transport expands the original node's argument.

## Proved and sorry left

Closed the original module's one hole:
`AlgebraicGeometry.Scheme.exists_affine_finite_module_presentation`
(node `lem-pc-perfect-affine-finite-presentation`). This is a decomposition, not a net
hole reduction: one original hole is closed and one strictly smaller geometric hole is
added. The combination with the existing affine criterion is fully proved Lean.

Also fully proved, without adding holes:
`AlgebraicGeometry.Scheme.exists_scheme_iso_derived_equivalence`
(node `lem-pc-scheme-iso-derived-equivalence`) and
`AlgebraicGeometry.Scheme.scheme_iso_derived_inverse_preserves_qcoh`
(node `lem-pc-scheme-iso-derived-qcoh`).

The only sorry in this delivery is
`AlgebraicGeometry.Scheme.scheme_iso_derived_inverse_preserves_perfect`
(node `lem-pc-scheme-iso-perfect-transport`), in its own new module. It is exactly
`:= by sorry`, with its source and the full local-model transport argument in the
docstring and node. It does not assert a finite module presentation, produce a module
complex, or assume affineness or quasi-coherence. The strictly smaller task is preservation
of a local predicate under a specified isomorphism-induced equivalence.

The already-existing affine criterion and any holes below its own dependencies remain
unchanged. No sorry occurs in a definition, private helper or partially written proof.

## No longer needed

Removed the redundant direct proof import
`Sheaf.AlgebraicGeometry.DerivedCategory` from the original module; its public statement
API already comes from `PerfectComplex`. This is only removal of a redundant direct
import, not pruning that module from the targets' closure.

No planned mathematical dependency, node or module was bypassed: the bounded-projective
affine criterion remains the essential input. In particular none of its ring-perfect,
affine-derived or local-projective dependencies is claimed pruned. No unit statement or
unit proof step was bypassed. The three transport nodes expand the original node's first
two steps, and its third step is implemented directly.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original transport plan did not have named Lean
interfaces for its first two steps. The usual derived-pullback preservation statement
(`DerivedPullbackPerfect`) is in a shared morphism universe and concerns the specified
`derivedPullback`; it is not a one-line substitute for the independently chosen
isomorphism-induced equivalence used here. The new comparison and transport interfaces
make that gap explicit.

The literature files are not present in this read-only clone, so the cited Stacks pages
were read online. LeanSearch returned Internal Server Error; that is recorded as service
unavailability, not evidence that a theorem is absent. Loogle returned no indexed matches
for the requested type patterns. Source searches found the Mathlib localization tools
and the source affine quasi-coherence theorem used in the completed proofs.

## New nodes

`lem-pc-scheme-iso-derived-equivalence` records the completely proved construction of an
isomorphism-induced derived equivalence with a natural Q comparison, allowing independent
morphism universes. Module: `Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence`.

`lem-pc-scheme-iso-derived-qcoh` records the completely proved quasi-coherence preservation
for its inverse. Its source-library input is only the quasi-coherence clause of
`lem-pc-affine-morphism-hi`, used as an existing generic tool.
Module: `Sheaf.AlgebraicGeometry.SchemeIsoDerivedQCoh`.

`lem-pc-scheme-iso-perfect-transport` records the remaining general preservation of
perfectness, with independent derived categories on all open sites. Module:
`Sheaf.AlgebraicGeometry.SchemeIsoPerfectTransport`.

All inherit chapter `sec-picard-framework`, unit `sk-thm-picard-duality`, and the original
node's blueprint ancestor. Existing node changes are restricted to proof, proof_deps and
proof_origin. There are no change records because no existing interface changed.

## Second reading by M2

1. **Visible declarations and interfaces.** Compared every delivered existing module against the repository version. The target theorem's signature and all pre-existing declarations are byte-for-byte unchanged; only proof imports and the target proof body changed. Verdict: pass.

2. **Proof and axioms.** Compiled all four delivered modules with `lcompile.py --all`. There are no forbidden declarations or hollow definitions. The two complete new theorems use only `propext`, `Classical.choice`, and `Quot.sound`; the target and the explicitly split perfectness theorem retain only their documented `sorryAx`. Verdict: pass.

3. **Split statements.** Read each new theorem and its node, checked edge cases described by the report, and searched the local library for duplicates. The equivalence and quasi-coherence statements are true and exactly the interfaces used by the target. The remaining perfectness statement is strictly more general than the target and is isolated as a named theorem with source documentation and a matching node. Verdict: pass.

4. **Route and pruning.** The affine bounded-projective criterion remains on the target's route and all unit steps are retained. The redundant direct `DerivedCategory` proof import was removed; the three transport imports are proof-only. Verdict: pass.

5. **DAG agreement.** Checked every node's Lean declaration, proof dependencies, origin, chapter and unit against the actual proofs and imports. New nodes contain the required source, proof, search and creation metadata. Verdict: pass.

Changed only this report section during second reading; no Lean statement or proof was altered.
