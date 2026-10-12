## What changed

The statement of `Algebra.exists_gabber_integral_section_factor` is unchanged. Its proof
now obtains a finite closed-fibre section model, applies the existing finite Gabber
polynomial theorem, constructs the root idempotent explicitly, transfers its integral
factor, and extends the original section by localization.

Two new modules accompany it. `FiniteGabberSectionModel` states the construction before
the choice of a Gabber polynomial or root, with no Jacobson or root-lifting hypothesis.
`FiniteIdempotentFactorTransfer` proves the transfer completely from Mathlib. In the
latter proof, `bd = αd` with α a unit implies `b ∣ d`, so Mathlib's
`Localization.awayMap_bijective_of_dvd` avoids iterated-localization glue. The quotient
structure map is injective because the section provides a left inverse. It is
surjective because every localized element is the image of an element of the finite
subalgebra and multiplying its difference from a scalar by d puts it in ID.

The main proof cancels the monic polynomial X-1 over A/I by its regularity, without
assuming the quotient is a domain or a nonzero ring. It evaluates the factorization
and the polynomial difference identity to prove d²=d and bd=αd. It then checks
that d and b have the same reduction, using n≥1. All three modules compile cleanly
with the required local compiler. The required delivery dry run performs the local compilation, axiom probe and
preflight as its final check; the current delivery tool defers server compilation
to the global build.

## Proved and sorry left

Closed: `Algebra.exists_gabber_integral_section_factor`, node
`lem-weil-pbc-gabber-root-criterion-integral-section-factor` (one original hole).
Its proof is a decomposition through one new hole, not a sorry-free proof of the
whole dependency closure.

Added and proved: `Algebra.finite_idempotent_factor_transfer`, node
`lem-weil-pbc-finite-idempotent-factor-transfer`. No sorry occurs in this module.

Added and left with exactly `by sorry`: `Algebra.exists_finite_gabber_section_model`,
node `lem-weil-pbc-finite-gabber-section-model`. This is the only new hole and the
only sorry in the delivery. It states steps 1–3 of the old plan. The docstring and
node supply the source and complete construction, and the proof imports retain
integral-closure localization and étale section splitting for the next worker.

The existing finite Gabber polynomial theorem is used, not restated or reproved.
The ledger effect is one original hole closed and one new hole added: net zero,
with the polynomial idempotent argument and the entire transfer argument proved.

## No longer needed

Removed from the item's direct imports:
`Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization` and
`Sheaf.RingTheory.EtaleSectionIdempotentSplitting`. Both remain imports of the
finite-model module and remain needed by its construction. Their nodes, and the
étale base-change, finite-presentation and finite-integral-generators nodes, move
into that model's proof dependencies rather than disappearing from the argument.

The old direct dependency `lem-weil-pbc-etale-ring-base-change` is replaced by
`lem-weil-pbc-etale-quotient-base-change` in the finite model, which records the
quotient specialization needed here. The other old dependencies relocated to
that model are `lem-weil-pbc-etale-section-idempotent-splitting`,
`lem-weil-pbc-etale-algebra-finite-presentation-localization`,
`lem-weil-pbc-integral-closure-finite-fibre-part-localization`, and
`lem-weil-pbc-finite-of-integral-generators`. The old
`lem-weil-pbc-zariski-pair-finite-gabber-polynomial` remains directly used.

No old dependency node is globally pruned; no module is claimed to leave the targets'
closure. No import needed to realize the unit's statement or steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The existing dependency signatures
do not directly supply the finite subalgebra with the compatible first-factor section;
this glue is the new finite-model statement. The rest of the old plan was implemented,
including the steps previously marked elementary that require polynomial and
localization calculations.

The source .tex file named by the node is absent on this machine. Tags 09XI, 09XH and
0EM0 were read on the official Stacks Project site. LeanSearch returned Internal
Server Error and is recorded as unavailable; LeanFinder, Loogle and actual Mathlib
and library searches were used. The logged searches are in searches.jsonl.

`tools/blueprint_refs.py ancestor` returns no blueprint ancestor for the item: its
existing created.item is a module name rather than a node id. The new nodes therefore
retain from.node = null, with an exact source place and via = [the item's node],
instead of inventing a blueprint ancestor. Blueprint searches for finite subalgebra
and idempotent found no duplicate of either new statement. The item's existing
blueprint metadata is unchanged, since stage 3 owns only its proof-route fields.

Edge cases checked mathematically: the finite model has no Jacobson restriction, so
I=⊤ and A/I the zero ring are allowed; the first factor is then zero and b may be 0.
A zero complementary factor is also allowed. For B=A and σ the quotient, the model
D=A, b=1, C=0 works. For the transfer lemma d=0 forces A/I=0 and both localized target
and its quotient are zero; the proof's section and surjectivity remain valid. The
polynomial proof uses regularity of a monic linear polynomial, which applies to
quotients with zero divisors and to the zero ring. The model's complementary corner
has the universe of B, so no restriction on the relative universes of A and B is added.

## New nodes

`lem-weil-pbc-finite-gabber-section-model`, module
`Sheaf.RingTheory.FiniteGabberSectionModel`: a finite A-subalgebra D of an étale
A-algebra B containing a localization parameter b, a closed-fibre product D/ID =
A/I × C with first projection the supplied section, and D[1/b] ≅ B[1/b]. This is
strictly the construction before polynomial and root choice; it has neither the
root hypothesis nor the final integral idempotent factor conclusion. Source:
09XI, proof of (5) implies (2), first through fourth paragraphs, and 09XH.

`lem-weil-pbc-finite-idempotent-factor-transfer`, module
`Sheaf.RingTheory.FiniteIdempotentFactorTransfer`: given a finite subalgebra model,
an idempotent d with bd=αd for a unit α, and the specified closed-fibre product,
prove integrality and quotient bijectivity for the image of d in B. Source:
09XI, passage from B'₁ to A'₁ and compatibility of splittings. It is completely
proved from Mathlib, with no étaleness or Gabber-root assumption.


## Second reading by H2

1. Compared the delivered main module with the repository by diff and extracted
   its signature: `Algebra.exists_gabber_integral_section_factor` is byte-for-byte
   unchanged. There are no existing definitions changed, no other existing Lean
   modules delivered, and no undeclared statement changes. Verdict: pass.
2. Independently compiled all three modules through lcompile.py. Scanned for
   forbidden declarations and sorry occurrences: the only sorry is the named
   `Algebra.exists_finite_gabber_section_model`; no definition contains sorry.
   Scratch copies with `#print axioms` checked all three delivered declarations:
   the transfer uses only propext, Classical.choice and Quot.sound; the model and
   main theorem additionally use only the reported sorryAx.
   The transfer is proved independently of sorry; the main theorem depends on
   the reported finite-model hole and existing polynomial dependencies. Verdict: pass.
3. Read both new statements, their docstrings, and matching nodes against Stacks
   Tags 09XI and 09XH. The finite model isolates construction before any root
   hypothesis or final idempotent choice, so it is a strictly simpler part of the
   argument, not a restatement. Checked I=top, I=bot, B=A, a zero complementary
   factor, and d=0: no nontrivial-ring assumption is missing. For I=bot the section
   factor is already A, and the integral-closure construction still applies.
   Repeated LeanFinder and Loogle searches with finite integral approximation and
   idempotent localization queries, and rg searches throughout both library roots.
   Read the related finite-subalgebra-away theorem and private congruence helpers:
   they do not give this compatible global section model. No duplicate or short
   complete proof of the remaining construction was found. Verdict: pass.
4. Read the main proof top down: it uses the existing finite Gabber polynomial,
   monic cancellation, explicit polynomial evaluation and localization lifts.
   Read the transfer proof: awayMap_bijective_of_dvd plus idempotent surjectivity
   supplies the integral factor; the section gives quotient injectivity and the
   product coordinates give surjectivity. Proof-only imports are plain imports;
   public imports support signatures. The finite-model imports retain its planned
   construction dependencies. Checked sk-thm-p1 realized statement and every
   realized step: none is bypassed by this reduction. Verdict: pass.
5. Compared the original node JSON: only proof, proof_deps and proof_origin differ.
   Those steps agree with the Lean proof. The two new nodes have matching verbatim
   Lean signatures, source, complete construction/transfer proofs, search records,
   creation metadata, chapter, unit and blueprint ancestry explanation. Verdict: pass.

Changes by the second reader: completed the explicit old-dependency accounting
under No longer needed and corrected the report's description of current delivery
compilation. No Lean proof or statement required repair. This remains a decomposition:
one original hole closed, one new hole added, net zero.
