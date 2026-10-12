## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.exists_normal_noetherian_refinement`
by a complete compiling proof using finite normal stage data and a proved limit comparison.
The theorem's signature and all original public imports are unchanged. The construction
uses the supplied index category.

`NormalFiniteStageDiagram` isolates construction of integral normal stages, dominant
projections and finite natural comparison maps to the supplied approximation. It does
not assert a limit property, affine transitions or Noetherianity.

`DominantFiniteRefinementLimit` proves
`AlgebraicGeometry.Scheme.isLimit_of_dominant_finite_refinement` with no holes.
Finite maps to the original Noetherian stages are locally of finite presentation, so
`exists_map_at_refinement_of_affine_limit` descends each projection to a later original
stage. Naturality and `ext_of_isDominant_of_isSeparated` identify its composite with
the comparison map with the replacement transition. The lift of any cone is the
original limit lift after composition with the comparisons. A Lean calculation proves
factorization, and the original limit proves uniqueness. This avoids a separate
unproved affine-chart limit/gluing assertion. The limit lemma needs no normality or
compactness of S and no affine-transition hypothesis on the replacement diagram.

The main proof derives affine transitions from naturality, composition of affine maps,
and `IsAffineHom.of_comp` using separated finite comparison maps. It derives
Noetherianity from finite-type maps to the original Noetherian stages and compactness
from quasi-compactness, then quasi-separatedness by the existing instance.
A local unused-variable linter option preserves the original unused existential binder
names without warnings. All three modules compile through the required compiler.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_normal_noetherian_refinement`
(node `lem-sbc-normal-noetherian-refinement`), one original hole.

Also proved, with no holes:
`AlgebraicGeometry.Scheme.isLimit_of_dominant_finite_refinement`
(node `lem-sbc-dominant-finite-refinement-limit`).

Added, exactly `:= by sorry` in a separate public theorem module:
`AlgebraicGeometry.Scheme.exists_normal_finite_stage_diagram`
(node `lem-sbc-normal-finite-stage-diagram`).

No holes remain in the item module. This is a decomposition: one hole closed and one
added, net zero. The diagram construction remains; the limit comparison, transition
affineness, Noetherianity and quasi-separatedness are complete proofs. The remaining
statement is strictly a part of the argument, with no limit or affine-transition
assertion. No definition or arbitrary witness construction was added.

## No longer needed

Removed the item's direct proof import
`Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite`; it is now the proof dependency
of `NormalFiniteStageDiagram`, which imports it. Its node
`lem-weil-pbc-finite-type-z-domain-normalization-finite` therefore remains needed.
No original node or module is globally pruned. No public import was removed.

The source's omitted affine-chart limit calculation need not be formalized for this
route: finite-presentation morphism descent and dominant-map extensionality prove the
same limit claim. No new hole for that calculation is delivered.

## Where the brief, the DAG or earlier work was wrong

The original DAG marked transition construction and the limit comparison elementary,
although no existing declaration directly states the latter. The construction is now
explicit; the limit comparison is actually proved using existing API.
The finite-type normalization theorem alone does not construct the geometric diagram.

Read Stacks Tag 0EZJ directly, especially its normal-stage paragraph and limit claim,
and Tag 01ZM for the morphism descent used in the proved limit lemma.
Used the original node's own-function-field normalization route. Mathlib's relative
normalization of S -> N_i is not a substitute: it can be infinite when S contains an
infinite algebraic extension. No such stronger finiteness claim was stated.

Checked edge cases for the remaining construction: S cannot be empty because it is
integral. Original affine charts can miss S; their scheme-theoretic image is empty,
so they contribute empty charts rather than a spurious nonempty normalization.
For nonempty charts, normality of section rings embeds the normalization of the image
ring's own fraction field into S. Identity normal finite-type systems admit the identity
stage replacement. No separation assumption on S is used.

The proved finite-refinement lemma includes the identity refinement and works without
normality of S. It uses relative separatedness of p_i, not separatedness of S or X_i;
reducedness for cancellation follows from the stated integral-stage hypothesis.
The finiteness hypothesis supplies finite presentation over the original Noetherian
stage. Its local limit data are built from the original IsLimit, not an arbitrary
witness of mere existence.

The existing proved `Subalgebra.exists_fg_integrallyClosed_extension` was also read.
It is an affine ring enlargement result, not a qcqs scheme diagram, and does not supply
the finite natural comparison maps required for the remaining construction.

## New nodes

`lem-sbc-normal-finite-stage-diagram` realizes the original construction and functoriality
steps in one public theorem. Its source, complete construction proof, normalization
finiteness dependency, Lean signature and searches are in its node and module.

`lem-sbc-dominant-finite-refinement-limit` records the proved finite-refinement limit
comparison. Its proof dependency is the existing, proved
`lem-sbc-pointed-section-stage-descent`. Its Lean proof constructs every IsLimit field.
Its source, signature and searches are recorded. LeanSearch was unavailable;
LeanFinder and local source searches succeeded.

Both nodes inherit `sec-smooth-base-change` and `sk-prop-input-spreading` and retain the
unit's normal Noetherian limit reduction. No change record or forced adaptation is needed.

## Second reading by D3

1. I compared the delivered item module with the repository version. The signature of
   `exists_normal_noetherian_refinement` is byte-for-byte unchanged; the added imports
   are proof-only imports. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile without
   errors. The item has no remaining holes; the only remaining `sorry` is the named,
   separately documented construction theorem `exists_normal_finite_stage_diagram`,
   whose node is `lem-sbc-normal-finite-stage-diagram`. No definitions contain `sorry`,
   and no forbidden declarations occur. Verdict: pass.
3. I checked the split statements and searched the library and Mathlib for duplicates.
   The finite-stage diagram is a strict construction subclaim, and the dominant finite
   refinement theorem is the separate limit comparison used by the item; both are true,
   needed, and strictly narrower than the target. Their docstrings, nodes, signatures,
   proof dependencies and sources agree. Verdict: pass.
4. I read the proofs from the target downward. The item uses the two split nodes, and the
   finite-stage node uses the existing finite normalization dependency. No shorter existing
   declaration was found. The unit route through normal finite replacements and the limit
   reduction is retained; no unused public import was removed. Verdict: pass.
5. I checked the DAG records against the Lean declarations and proof bodies. The target's
   proof dependencies now name both split nodes, each new node records its module and
   declaration, and the report records the one hole closed and one hole added. Verdict: pass.

I changed only this report section during second reading; no Lean statement or proof was
changed.
