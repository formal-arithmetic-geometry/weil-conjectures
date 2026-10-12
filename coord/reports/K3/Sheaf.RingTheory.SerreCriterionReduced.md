## What changed

Filled `Ring.isReduced_iff_serreR_zero_and_serreS_one` without changing its signature
or its existing docstring. The proof follows all five steps of Stacks Algebra,
Tag 031R; the source was read in the local Stacks checkout at
`/home/ubuntu/c1-stacks-review/algebra.tex`, lemma-criterion-reduced.
The forward implication uses minimal-prime localizations being fields and proves
positive depth by excluding the maximal associated prime. The converse uses strong
induction on the finite natural height of a prime, the height-zero regular-local
case, a regular element supplied by positive depth, and two iterated-localization
isomorphisms. Joint detection of zero and injectivity of principal localization
finish the argument. The ring with no primes is covered by joint detection; in
height zero the depth bound is automatic.

Added five fully proved private helpers for depth, regular elements, joint local
detection, and the height-zero case. These helpers introduce no public signatures.
Added the proof-only import `Mathlib.RingTheory.LocalProperties.Reduced`; the
remaining Mathlib lemmas are already available through the existing public imports.
Local compilation passes without warnings.

## Proved and sorry left

Closed the one original hole:
`Ring.isReduced_iff_serreR_zero_and_serreS_one`
(node `lem-weil-pbc-serre-criterion-reduced`).

No sorry remains in the item, and no new holes or modules were added. This is a
complete proof from the existing stated dependencies, not a decomposition.
It still uses the existing holed theorem
`exists_mem_maximalIdeal_smul_injective` in
`Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated`
(node `lem-weil-pbc-nonzerodivisor-if-maximal-not-associated`);
therefore this delivery does not claim the target's transitive proof is sorry-free.

## No longer needed

Removed the direct proof-only import `Sheaf.RingTheory.Depth`: the public statement
import `Sheaf.RingTheory.SerreConditions` already supplies it. Its definitions and
DAG node remain needed; this is removal of a redundant import, not pruning of the
Depth module from the target closure. No mathematical dependency nodes or modules
are pruned. Trial explicit imports of KrullDimension.Zero,
Localization.LocalizationLocalization, and Spectrum.Maximal.Localization were
removed after compilation showed that the existing imports already supply them.
The original DAG's five-step route is retained, so no DAG update is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The local repository lacks the cited Stacks
source file, but another read-only local Stacks checkout supplies the exact lemma.
No statement, definition, or unit route changed.

## Second reading by K3

1. Compared the delivered module with the repository using `diff -u`. The sole
   existing declaration's signature and docstring are byte-for-byte unchanged.
   The only changes are its proof, five fully proved private helpers, replacement
   of the redundant private Depth import by the private Mathlib Reduced import.
   No definition, public import, or statement was changed. Verdict: pass.
2. Compiled the module locally through `lcompile.py`: no errors or warnings.
   Scanned for sorry, axiom, unsafe, opaque, extern, implemented_by and kernel
   bypasses: none. A scratch copy with `#print axioms` for all six declarations
   compiled. Four helpers use only propext, Classical.choice and Quot.sound;
   `depth_ge_one_of_reduced` and the criterion additionally use sorryAx through
   the existing `exists_mem_maximalIdeal_smul_injective`. This is the open
   dependency already disclosed above, not a new hole. Verdict: pass.
3. No statement was split off and no new sorry or node was added. Read all five
   private helper proofs. Checked the zero ring (no primes; joint detection
   still applies), fields and height-zero primes (the S1 bound is zero), and
   positive-height local rings (a unit annihilator would force dimension zero).
   The depth-to-element helper excludes the infinite-depth branch using
   Nakayama, then extracts the head of a nonempty regular sequence. Fresh
   LeanFinder search for positive-dimensional reduced local rings with a
   regular element, and grep searches of Mathlib, upstream and Sheaf, found no
   shorter criterion or existing depth helper. Mathlib's maximal-localization
   reducedness theorem is available, but the existing short joint-injectivity
   helper directly implements the planned prime-localization step. Verdict: pass.
4. Read Stacks algebra.tex, lemma-criterion-reduced (Tag 031R), and checked
   both implications from the top down. The converse contracts each prime of
   A[1/t] twice, proves strict containment by avoidance of t, uses finite prime
   height for strong induction, and transports reducedness across the two
   localization isomorphisms. All three remaining imports are needed: Serre
   definitions, localization preserving reducedness, and the nonzerodivisor
   theorem. Every old proof dependency remains used, so No longer needed is
   complete. Read sk-thm-p1.json and its realized fields: this supporting node
   bypasses none of the unit's statement or steps. Verdict: pass.
5. Read the criterion node and every proof dependency's Lean/Mathlib record.
   The five proof steps, proof_deps and document proof_origin match the Lean
   argument, including uses through definitions and instances. No new node or
   change record is required. Verdict: pass.

Changes by the second reader: added this review and independent search/axiom
verification; no Lean proof repair or DAG change was needed.
