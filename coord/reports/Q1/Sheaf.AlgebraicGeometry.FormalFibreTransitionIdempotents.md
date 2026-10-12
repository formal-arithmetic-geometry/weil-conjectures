## What changed

Replaced the proof of `AlgebraicGeometry.formalFibreTransition_idempotents` with a
complete reduction to the existing `nilpotent_baseChange_idempotents` theorem.
The existing theorem signature, definitions, visibility, imports and original
mathematical docstring are unchanged. No change record is needed.

For the quotient transition `r : A/m^(n+2) → A/m^(n+1)`, Mathlib's `factor_ker`
identifies its kernel with the image of `m^(n+1)`. Ideal-map compatibility with
powers and `2*(n+1) ≥ n+2` prove that this kernel squares to zero. The surjective
quotient equivalence and pullback pasting then identify the chosen formal fibre
with the nilpotent quotient base change. Transport of global sections along this
proved isomorphism gives exactly the required unique idempotent lift.

Removed the first worker's proposed existence and uniqueness declarations and
their two unlanded node files. Their entire geometric content is now proved in
the original theorem rather than postponed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.formalFibreTransition_idempotents`
(node `lem-weil-pbc-formal-fibre-transition-idempotents`).

No `sorry` remains in the delivered module; no holes are added elsewhere.
Against the repository baseline: one hole closed, zero holes added. This is a
proof, not a decomposition. Compared with the initial sandbox, the holes named
`AlgebraicGeometry.formalFibreTransition_idempotent_exists` and
`AlgebraicGeometry.formalFibreTransition_idempotent_unique` were removed together
with their proposed declarations, not counted as additional baseline proofs.

Local compilation succeeds without warnings. A scratch copy with `#print axioms`
shows only `propext`, `Classical.choice`, and `Quot.sound` for both the delivered
theorem and `nilpotent_baseChange_idempotents`; neither has `sorryAx`.

## No longer needed

No existing proof-dependency nodes or imports were pruned. Both original
proof dependencies remain used: `def-weil-pbc-formal-fibre-cohomology` and
`lem-weil-pbc-base-change-nilpotent-thickening-idempotents`.
`FormalFibreCohomology` is needed by the signature and remains a public import;
`NilpotentBaseChangeIdempotents` is used only by the proof and remains private.

The proposed, unlanded nodes
`lem-weil-pbc-formal-fibre-transition-idempotents-existence` and
`lem-weil-pbc-formal-fibre-transition-idempotents-uniqueness` are withdrawn.
They are not existing library nodes or pruned modules.

## Where the brief, the DAG or earlier work was wrong

The initial sandbox replaced one hole by two and described the pullback
identification as omitted from the DAG. The repository node already includes
that identification in its first proof step. Mathlib supplies `factor_ker`,
`factor_surjective`, `quotientKerEquivOfSurjective`, `IsPullback.of_right`,
`IsPullback.of_iso`, and `isoPullback`; these complete the planned reduction
without any new statements. The earlier second reading recorded in the initial
report is superseded by the independent reading below.

## Second reading by Q1

1. Compared the delivered file against the repository with `diff` and checked
   the existing theorem signature byte for byte. Verdict: identical statement;
   only its proof changed. No definitions, public imports or visibility changed.
2. Compiled the module locally through `lcompile.py`, scanned for holes and
   forbidden declarations, and compiled a scratch axiom check. Verdict: no
   errors, warnings or local `sorry`; only the three permitted axioms. The
   quotient equivalence and pullback isomorphism are justified by proved
   universal properties, with no arbitrary data chosen from an unproved claim.
3. Read the two proposed split-off statements and their nodes. They express true
   existence and injectivity facts, including `n=0`, zero/one idempotents, and
   empty fibres, but their sketches repeat the same unfinished geometric work.
   Repeated searches with different queries using leanfinder, loogle and grep,
   and searched `lean/Sheaf` and `lean/WeilConjectures`. Verdict: use the existing
   nilpotent-base-change theorem and Mathlib's quotient/pullback tools; no new
   statements are needed. Removed both proposed declarations and nodes.
4. Read the original proof plan and `dag/units/sk-thm-p1.json` including its
   `realized` field. Verdict: the proof follows the original quotient/pullback
   reduction and retains the unit route. Both original imports and dependencies
   are used, so the list of existing nodes no longer needed is empty. Checked
   the cited Stacks Tags [0G7X](https://stacks.math.columbia.edu/tag/0G7X),
   [09ZU](https://stacks.math.columbia.edu/tag/09ZU),
   [04EX](https://stacks.math.columbia.edu/tag/04EX), and
   [00EE](https://stacks.math.columbia.edu/tag/00EE). For `n=0` the exponent bound
   is equality; neither the quotient nor the section transport assumes
   nonemptiness, properness or Noetherianity.
5. Compared the repository node's `proof`, `proof_deps`, and `proof_origin`
   with the final Lean argument. Verdict: they already record precisely the
   square-zero quotient, pullback identification, application of the nilpotent
   base-change theorem, and transport of existence/uniqueness. No metadata
   edit is needed, and no new nodes remain in the delivery.

Changes made by the second reader: replaced the existence/uniqueness split with
the complete original proof, restored the repository docstring and header,
removed the two proposed node files, and corrected this report's progress and
DAG descriptions.
