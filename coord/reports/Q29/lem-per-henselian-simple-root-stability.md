## Worker report

The module `Sheaf.FieldTheory.HenselianSimpleRootStability` states
`Valued.exists_open_coefficients_simple_root`, with one theorem and its entire proof
`sorry`. It introduces no definitions. The copied node changes only its `lean` field;
the reviewed split, source, natural statement and dependencies remain intact.

Source read: ILO, *Travaux de Gabber*, Exposé XX, section 4.4, printed pages 373--374,
especially page 374's dense henselian valued field comparison and its citation of
Bourbaki VI, section 8, exercises 12 and 14(a). This page invokes forms of Krasner;
it does not separately print this perturbation lemma. The supplied DAG spells out
that intermediate lemma and its seven-step valuation argument. Also read Stacks
`algebra.tex`, `definition-henselian` (04GF) and `lemma-characterize-henselian`
(04GG), whose nonmonic root-lifting clause is part (2). The module's docstring
follows all seven steps of the reviewed DAG, using its monic reciprocal-translation
argument and the existing root-lifting dependency.

Hypotheses and clauses, individually matched:

| Node text | Lean rendering |
| --- | --- |
| F is a field | `(F : Type u) [Field F]` |
| An arbitrary totally ordered value group | `(Γ₀ : Type v) [LinearOrderedCommGroupWithZero Γ₀]`, in an independent universe |
| F carries its valuation topology | `[vF : Valued F Γ₀]`; `Valued` includes the compatible uniform space and hence topology |
| Nontrivial valuation | `[vF.v.IsNontrivial]`; its definition is an element with value different from zero and one, equivalent over a field to a nonzero element of nonunit value |
| Henselian valuation ring | `[HenselianLocalRing vF.v.integer]`, imposed on the actual subring `{x : F | vF.v x ≤ 1}` |
| Degree n at least one | `(n : ℕ) (hn : 1 ≤ n)` |
| The n lower coefficients | `(c : Fin n → F)` |
| Monic polynomial `T^n + sum c_i T^i` | `Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)` |
| Root a belongs to F | `(a : F)` |
| `f(a) = 0` | `ha`, evaluation of exactly the displayed polynomial at a |
| `f'(a) ≠ 0` | `hda`, evaluation of its formal `Polynomial.derivative` at a |
| Every open neighbourhood U of a | Arbitrary `(U : Set F) (hU : IsOpen U) (haU : a ∈ U)` |
| There exists an open neighbourhood V of the original tuple | `∃ V : Set (Fin n → F), IsOpen V ∧ c ∈ V ∧ ...` |
| V uses the product topology | The standard Pi topological-space instance on `Fin n → F`, inherited from the valued topology on F |
| Every perturbed tuple in V | `∀ d ∈ V, ...` |
| Its polynomial is monic of the same degree | The same explicit polynomial expression with `d` in place of `c` |
| It has a root b in U | `∃ b ∈ U, (...).eval b = 0 ∧ ...` |
| b is a simple root | The final conjunct `(...).derivative.eval b ≠ 0` |
| Arbitrary rank, no completeness | No archimedean, rank-one, metric, complete-space or discrete-valuation hypothesis occurs |

The additive convention of the node and Mathlib's multiplicative convention are
equivalent by reversing the ordered value group: additive `v(x-a) > gamma` becomes
multiplicative `v(x-a) < radius`. Zero has additive value infinity and multiplicative
value zero. This is only a notation change, not a rank or topology restriction.
`Valued.mem_nhds` gives exactly these translated valuation balls. Its value-group
restriction avoids dependence on unused ambient values. The explicit polynomial
is automatically monic of degree n because the sum has exponents strictly below n;
no additional monicity or degree hypothesis has been introduced.

Dependency declarations read and used:

- `def-trf-valuation-ring`: its Mathlib match is `ValuationRing` and
  `ValuationRing.TFAE` in `Mathlib.RingTheory.Valuation.ValuationRing`, read at
  lines 62--64 and 407--416. The integer subring is the canonical realization:
  `Valuation.integer` in `Mathlib.RingTheory.Valuation.Integers`, lines 31--39,
  defines its carrier by value at most one. `Valuation.valuationSubring` in
  `Mathlib.RingTheory.Valuation.ValuationSubring`, lines 438--447, equips that
  same subring with the fraction-field inverse alternative. These are available
  through the public valuation-topology import; no separate ring is chosen.
- `def-weil-pbc-henselian-terminology`: its record explicitly lists
  `HenselianLocalRing` (Mathlib) alongside the upstream strict-henselian class.
  This theorem uses only the former, whose full signature and docstring were
  read in `Mathlib.RingTheory.Henselian`, lines 100--112. The module
  `WeilConjectures.Mathlib.RingTheory.Henselian` is imported publicly as recorded;
  its lines 31--34 identify the blueprint's local henselian terminology with
  Mathlib's class. No repair of the mixed record is needed.
- `def-weil-polynomial-ring`: the recorded `Polynomial`, from
  `Mathlib.Algebra.Polynomial.Basic`, lines 67--78, is used directly. Evaluation
  is `Polynomial.eval` (Eval/Defs.lean:250), and formal differentiation is
  `Polynomial.derivative` (Derivative.lean:46). The public derivative import
  provides this interface and the polynomial ring.
- Proof-only dependency `lem-weil-pbc-henselian-local-root-lifting`:
  `IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting` from
  `Sheaf.RingTheory.HenselianLocalRootLifting`; its full docstring and signature
  at lines 121--162 were read. The module is imported nonpublicly for stage 3.
- Topology infrastructure: `Valued` (ValuationTopology.lean:125--130),
  `Valued.mk'` (:138--147), and `Valued.mem_nhds` (:170--174) were read. They
  supply the existing valuation topology rather than a new notion.

Edge cases checked against the statement and the seven-step argument:

- `n = 1`: the polynomial is linear and its derivative is one; the conclusion
  requires the root near a, exactly as the node. The reciprocal polynomial has
  reduction `Y+1`, so its residue root remains simple.
- `n = 0`: excluded exactly by the node's `n ≥ 1`, represented by `hn`.
- Positive characteristic, including characteristic two: no characteristic
  assumptions occur; simplicity is derivative nonvanishing. The residue root
  `-1` in the proof has derivative `(-1)^(n-1)`, still nonzero in characteristic two.
- Arbitrary valuation rank: only a linear ordered commutative group with zero
  is required. The proof uses finite bounds, never cofinal powers of one element.
- Discrete valuation topology: singleton V works, as in proof step 1; the
  statement imposes no nondiscreteness assumption.
- Repeated roots elsewhere: permitted; `ha` and `hda` test only the selected a.
- Empty U is excluded precisely by `a ∈ U`; U may otherwise be any open set.
  V must contain c, so the result cannot hold vacuously with an empty V.
- Independent field and value-group universes are explicit; all variables are
  bound and `autoImplicit` is disabled.

Searches run (the wrapper's exact queries and result metadata are retained in
`searches.jsonl` in the sandbox):

- LeanFinder: `Simple roots of monic polynomials over henselian valued fields persist under small coefficient perturbations`.
  Eight hits: henselian root-lifting criteria, p-adic Hensel, `Field.henselian`,
  a model-theoretic monic-polynomial sentence and an Eisenstein statement.
  None states coefficient stability in an arbitrary-rank valuation topology.
- Loogle: `Valuation, HenselianLocalRing`. Zero hits.
- LeanSearch: `Simple roots are stable under coefficient perturbation over a henselian valued field`.
  Eight hits, led by p-adic `hensels_lemma`, `HenselianLocalRing.is_henselian`
  and `.TFAE`; none gives the requested topological perturbation conclusion.
- Wrapper grep: `HenselianLocalRing|Krasner|simple.root` in
  `RingTheory/Henselian.lean`. Five source lines concerning the henselian
  class and simple-root terminology; no coefficient-stability statement.
- Direct `rg`: `simple.root|simpleRoot|root_stability|rootStability` in upstream
  `WeilConjectures` and project `lean/Sheaf/RingTheory`; found only root-lifting
  and étale-presentation material. Read the relevant henselian source signatures.
- Direct `rg`: `root.*stability|stability.*root|simple.*perturb|perturb.*simple`
  throughout project `lean/Sheaf`; no matching theorem. The dense comparison
  module cites this item in its proof docstring but does not state it.
- Direct `rg`: the item id in upstream `WeilConjectures` and
  `dag/lean_names_upstream.json`; no matches. Exact proposed declaration name
  `exists_open_coefficients_simple_root` was searched across Mathlib, upstream
  and project Lean; no pre-existing declaration.

No statement correction, missing dependency, new definition node, hollow data,
or statement dispute was found. In particular the previous stage-1 preflight
refusal is not addressed by changing the reviewed split: this delivery adds
the previously absent stage-2 Lean record and theorem module.

Validation: the prescribed `scompile.py Q29 lem-per-henselian-simple-root-stability`
compiled the delivered file in both sandbox and library-module contexts, cleanly
and without warnings (3.4 seconds and 3.0 seconds, respectively). The recorded
signature is extracted verbatim from the file, and the only changed node field
is `lean`. All Lean lines have at most 100 characters.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
