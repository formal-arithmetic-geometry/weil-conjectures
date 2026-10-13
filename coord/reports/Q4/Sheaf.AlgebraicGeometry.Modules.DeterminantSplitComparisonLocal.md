## What changed

Repaired `determinant_split_comparison_restriction` by retaining the corrected natural
linear family hypothesis and removing the unused rank equality and finite-locally-free
instances. Naturality follows by substitution of `hd` into `hn`; the companion caller
was adapted to the reduced interface. The module and adapted caller compile together.

## Proved and sorry left

`determinant_split_comparison_local` and `determinant_split_comparison_restriction` are
proved with no `sorry`s. No holes were added.

## No longer needed

The restriction theorem no longer needs the rank equality or either finite-locally-free
instance. No proof imports were removed.

## Where the brief, the DAG or earlier work was wrong

The upstream review correctly identified the unconstrained `c` statement as false. The
repository already contained the stronger natural-family repair, but the queued repair
was stale and deliver3 rejected an unchanged assignment. This delivery records the
repair in the current item and further removes hypotheses unused by its naturality proof.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison

The caller previously passed `hr` to `determinant_split_comparison_restriction`; after
removing that theorem's unused equality hypothesis, the explicit argument had to be
removed. All signatures and visibility of the caller theorem are unchanged.

## Earlier second reading (a previous round; superseded)

Pending independent second reading.

The statement change and forced caller adaptation are recorded in
`coord/changes/determinant_split_comparison_restriction_hypotheses.md`.

## Second reading by Q4

1. **Visible declarations.** I compared both delivered modules with the repository
versions. The target and caller theorem signatures are unchanged. The only changed
interface is `determinant_split_comparison_restriction`, and that intentional change is
recorded in `coord/changes/determinant_split_comparison_restriction_hypotheses.md`; the
caller edit removes exactly the now-unused `hr` argument.

2. **Compilation and trust.** I compiled both sandbox modules with
`lcompile.py --all`. They compile cleanly, contain no `sorry`, `axiom`, `unsafe`,
`opaque`, `implemented_by`, or `extern`, and the restriction proof is the direct
substitution `simpa only [hd] using hn ...`.

3. **Statements and nodes.** The revised restriction statement is true for arbitrary
ranks because its conclusion follows pointwise from `hd` and `hn`; the removed rank
equality and finite-locally-free assumptions are unused. The statement is not a
restatement of the item: it is the strictly simpler naturality conversion needed by
the caller. Its node records the exact Lean statement, source, and proof route.

4. **Route and pruning.** The local construction still follows the existing linear-map
and local-bijectivity route, and the caller still uses the natural family supplied by
that construction. No proof dependency import became unused, and the unit route is
unchanged. The removed hypotheses are documented in the change record.

5. **DAG agreement.** The node's `lean` declaration and statement match the delivered
module, with `proof_deps` empty and an elementary substitution proof. The forced
adaptation is limited to the one caller application site and preserves its public
signature.

I changed only the report by adding this second-reading record; the Lean proofs and
node content already passed local compilation and review checks.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-pbbpaxbf/lean/Sheaf/AlgebraicGeometry/Modules/DeterminantSplitComparison.lean:100:62: error: Application type mismatch: The argument
  hr
has type
  r₂ = r₁ + r₃
of sort `Prop` but is expected to have type
  X.Opens
of sort `Type v` in the application
  determinant_split_comparison_restriction S r₁ r₂ r₃ hr
/tmp/forced-adaptation-pbbpaxbf/lean/Sheaf/AlgebraicGeometry/Modules/DeterminantSplitComparison.lean:101:27: error(lean.invalidField): Invalid field `trans`: The environment does not contain `TopologicalSpace.Opens.trans`, so it is not possible to project the field `trans` from an expression
  hW
of type `TopologicalSpace.Opens ↥X`

(with the modules compiled into /tmp/forced-adaptation-pbbpaxbf/.lbuild) [3.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
