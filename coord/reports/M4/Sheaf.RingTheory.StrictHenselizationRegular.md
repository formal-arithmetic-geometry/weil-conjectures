## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.StrictHenselizationRegular` with a
complete proof from the existing dependencies. No signatures, visibility, imports,
definitions, or proof route changed.

The proof installs Noetherianity of `C` using
`Algebra.isNoetherianRing_iff_isStrictHenselization`, extracts locality and the
cotangent finrank equality from
`Algebra.finrank_cotangentSpace_eq_of_isStrictHenselization`, and rewrites Mathlib's
`IsRegularLocalRing.iff_finrank_cotangentSpace` for both rings using that equality
and `Algebra.ringKrullDim_eq_of_isStrictHenselization`.

## Proved and sorry left

Closed 1 of 1 holes:
`Algebra.isRegularLocalRing_iff_strictHenselization`
(node `lem-sc-strict-henselization-regular`). No holes added or split off; no
`sorry` remains in the delivered module. The existing imported dimension and
cotangent comparison theorems remain separate proof obligations outside this
item; this delivery proves the requested theorem from their stated interfaces.

The unchanged theorem compiled cleanly with `lcompile.py` (2.2 seconds).

## No longer needed

None. All three existing proof imports supply declarations used by this proof.
The Mathlib regular-local criterion is used from the existing public import.
No nodes or modules of the recorded proof plan are bypassed or pruned.

## Where the brief, the DAG or earlier work was wrong

No discrepancy in the proof plan or Lean interfaces. The recorded proof route
works directly, including obtaining the `IsLocalRing C` instance from the
cotangent comparison theorem. The unit `sk-thm-br` route is unchanged.

Short-route searches: LeanFinder returned eight results about Henselian rings,
regular sequences and DVRs, with no strict-henselization regularity equivalence;
Loogle (`IsRegularLocalRing, HenselianLocalRing`) returned no hits; the launcher
grep search for strict henselization and regularity returned no hits. Direct
source inspection found Mathlib's cotangent criterion, exactly the leaf already
named by the DAG.

The literature paths recorded in the node and unit are absent in this checkout;
the existing node proof, dependency interfaces, and Mathlib criterion were read.
No new source-dependent assertion or proof obligation was introduced.

## Second reading by M4

1. Compared the delivered module with the repository version. The theorem signature,
   definitions, visibility, and imports are unchanged; only the original proof body
   was replaced.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings.
   The proof contains no `sorry`, axiom, unsafe declaration, or hollow definition.
   The imported open theorems are used only through their stated interfaces.
3. Checked the theorem statement and the existing node: the equivalence is unchanged,
   and no new statements or nodes were introduced. The regular-local criterion is
   applied after constructing the required Noetherian and local instances for `C`.
4. Checked the proof route and pruning. It follows the node's three recorded steps:
   Noetherianity, cotangent finrank equality, and Krull dimension equality, followed
   by Mathlib's criterion. No recorded proof dependency or import is bypassed.
5. Checked the unit route and metadata. The unit `sk-thm-br` remains realized by the
   same node, and the DAG proof dependencies agree with declarations used in the file.

No changes were needed during second reading beyond adding this review record.
