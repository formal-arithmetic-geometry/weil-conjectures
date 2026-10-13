## What changed

Proved `finite_normal_cover_sup_normal` in
`lean/Sheaf/RingTheory/FiniteNormalCoverSupNormal.lean` without changing its signature.
Added the proof-only import `Mathlib.RingTheory.Localization.AsSubring`, which supplies
canonical embeddings of prime localizations into K and the fraction-field instance
for intermediate subalgebras. Updated the declaration docstring and the node's proof
and proof_origin to describe the actual denominator argument.

The proof follows the final paragraph of Stacks Tag 0333, read at
https://stacks.math.columbia.edu/tag/0333. It selects the normal C_r over the contracted
prime, clears a denominator of the monic equation over B_q, and clears another
denominator using normality of C_r. Their product avoids q, giving a fraction in B_q.
No additional intermediate localization ring is needed.

## Proved and sorry left

Closed: `finite_normal_cover_sup_normal`
(node `lem-weil-pbc-finite-normal-cover-sup-normal`), the only original hole.
Added: none. Sorries left: none. This is a proof, not a decomposition;
all dependencies used in the proof are Mathlib results without sorry.

Local single-file compilation is clean. The delivery dry run also checks axioms.

## No longer needed

No imports removed and no entire nodes or modules pruned. The originally planned
use of localization preserving integral closedness is unnecessary; the existing
Mathlib leaf `lem-weil-pbc-localization-normal-domain` remains a dependency for its
fraction-field clause, via `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`.
The proof uses no Sheaf or WeilConjectures proof imports.

## Where the brief, the DAG or earlier work was wrong

No incorrect statements or interfaces found. The original DAG's intermediate ring T
and further-localization construction are avoidable: two explicit denominators give
the same normality conclusion. The unit route is preserved; this node is not one of
the unit's statement or step realizations.

Edge cases: if s is empty, the covering hypothesis cannot hold for the zero prime of
the domain A; no nonempty assumption was added. Zero integral elements use the same
fraction construction. Contraction of primes and avoidance of q are checked in Lean,
so no maximality or Noetherian hypothesis is used.

The repository lacks the local `literature/stacks-project/algebra.tex`; the cited
Stacks page was read online. No source or project coordination files were modified.

## Second reading by T2

1. Interface: PASS. Diffed the sole delivered Lean module against the repository.
   The existing theorem signature is byte-for-byte identical, also equal to the
   node's Lean statement. No definitions, visibility, or public imports changed;
   the added AsSubring import is proof-only. No change records are needed.
2. Proof: PASS. Compiled the file locally through lcompile.py without diagnostics.
   A scratch copy with `#print axioms finite_normal_cover_sup_normal` reports exactly
   propext, Classical.choice, and Quot.sound. There are no sorries, forbidden
   declarations, or data chosen from an unproved theorem. The contraction and two
   denominator steps prove the original conclusion without additional hypotheses.
3. Split statements: PASS, none added or left. Checked the empty-family case (the
   cover hypothesis fails at the zero prime), the singleton case, and zero integral
   elements. Repeated searches with LeanFinder (normality from a birational integral
   overring), Loogle (`IsIntegrallyClosed, Subalgebra`), and rg in Mathlib and both
   project roots; no applicable direct theorem or shorter complete route was found.
4. Route and pruning: PASS. Read Stacks Tag 0333, final reverse-implication paragraph,
   and dag/units/sk-thm-p1.json. This node is below the unit realizations; none is
   bypassed. The public imports supply signature notions and the proof-only import
   supplies localization embeddings and intermediate-subalgebra fraction fields.
   No old proof dependency or import is unused: the localization-normal-domain
   Mathlib leaf remains used for its fraction-field clause, via the more general
   lemma that does not assume global integral closedness. No modules are pruned.
5. Nodes: PASS after correction. The steps, dependency union, and document origin
   match the actual proof. Corrected the erroneous named reference
   Localization.subalgebra.isFractionRing to the anonymous intermediate-subalgebra
   instance in AsSubring, and named the exact localization fraction-field theorem.
   No new nodes or statements were introduced.

Second reading changed only the node's proof description and this report. The Lean
proof was retained. Closed finite_normal_cover_sup_normal (1 of 1 original holes);
added 0 holes; 0 split off. Final delivery validation is performed with deliver3.py.
