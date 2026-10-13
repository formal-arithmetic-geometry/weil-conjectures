## What changed

The signature of `FieldTheory.triangularFieldModel_reconstruction_bijective` is unchanged.
Its proof now expands the displayed linear map pointwise, proves injectivity by
subtracting two coefficient functions and applying uniqueness of zero expansions,
and proves surjectivity from bounded-monomial spanning. Two new proof-only imports
provide those strictly partial conclusions. All three modules compile together with
`lcompile.py --all`.

## Proved and sorry left

Closed one hole: `FieldTheory.triangularFieldModel_reconstruction_bijective`.
Added two holes, so this is a decomposition, not a completed structural proof:

- `FieldTheory.triangularFieldModel_bounded_independent`, node
  `lem-weil-pbc-triangular-field-model-bounded-independent`.
- `FieldTheory.triangularFieldModel_bounded_spanning`, node
  `lem-weil-pbc-triangular-field-model-bounded-spanning`.

Each new hole is a public theorem with its exact signature, source, complete proof in
words, and its own node. No definition chooses data from these theorems.

## No longer needed

No original imports or planned dependency modules are pruned. Both parts retain the
localization presentation and triangular monic division route. The parent node now
points to the two parts rather than directly to their common ingredients.

## Where the brief, the DAG or earlier work was wrong

The first dry run required a nonempty `## Earlier second reading (a previous round; superseded)` section. This worker's
explicit brief forbids writing that section and assigns it to the independent next
worker. No second-reader attestation has been fabricated. The tool cannot currently
accept the requested first-worker dry run without that later worker's contribution.

LeanFinder returned `AdjoinRoot.powerBasisAux'` and its coordinate formulas; Loogle
returned `Module.Basis.smulTower` and its apply/repr lemmas; grep found those and
`IsLocalization.Away.mvPolynomialQuotientEquiv`. These supply the single-step
ingredients, not the simultaneous triangular quotient identification. The source
proofs at Stacks Tags 07BV and 08JZ were read. The new docstrings expand the monic
remainder existence and uniqueness arguments rather than claiming the sources
already contain this exact Lean statement.

Edge cases were checked: m=0 leaves one coefficient over the localization; h=0
makes the coefficient ring zero; a zero e_i makes the tuple index empty and puts
the unit relation in the quotient ideal. Thus both new statements remain true.

## New nodes

`lem-weil-pbc-triangular-field-model-bounded-independent` isolates uniqueness of
coefficients in a vanishing expansion. Its induction applies monic-remainder
uniqueness to the last variable and then to the earlier coefficient expansions.

`lem-weil-pbc-triangular-field-model-bounded-spanning` isolates existence of a bounded
expansion. Its induction divides by the last monic relation and expands the
remainder coefficients. Both nodes stay in the parent's chapter and unit and use
the parent's localization/monic-quotient route. The parent node's proof,
proof dependencies, and proof origin are updated to match its compiling Lean proof.

## Second reading by X3

1. **Unchanged interfaces.** Compared each delivered module with the repository version;
the existing reconstruction theorem has the same signature byte for byte. The two added
theorems are new split statements and are recorded by matching DAG nodes. Verdict: pass.
2. **Proof checks.** Compiled all three modules with `lcompile.py --all`; there are no
definitions containing `sorry`, axioms, unsafe declarations, or other prohibited constructs.
The only remaining `sorry`s are the two named split theorems. Verdict: pass.
3. **Statements.** Checked the bounded independent and bounded spanning statements on
the m=0, h=0, and zero-degree edge cases; they remain true and are strictly smaller than
the parent target. Grep and library searches found no duplicate declarations. Verdict: pass.
4. **Route and pruning.** The reconstruction proof uses exactly the two split results,
and the localization and triangular monic route remains represented in their proof
dependencies. No unused imports or old proof dependencies were found. Verdict: pass.
5. **DAG agreement.** The parent node records the two split nodes as proof dependencies;
each split node records its theorem, source, proof outline, unit, and module. Verdict: pass.

I added this second-reading attestation, with no Lean source changes required after the
compilation review.
