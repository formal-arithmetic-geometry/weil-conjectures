## What changed

The target module now proves the polynomial-presentation part rather than assuming it.
It imports CompletionFiniteQuotientData privately. AdjoinRoot.tensorAlgEquiv base-changes
R[X]/(X^p-f), and mapAlgEquiv along Algebra.TensorProduct.rid identifies its coefficient
ring with the completed base. Monomial induction proves the formula for every polynomial.
Composing with the tensor comparison proves the target, with its original signature and
original docstring unchanged. CompletionFiniteQuotientPresentation and its proposed node
were removed from the sandbox before delivery.

## Proved and sorry left

Closed: AdicCompletion.completion_finite_quotient (one original hole).
Added and still open: AdicCompletion.completion_finite_quotient_data,
node lem-weil-pbc-completion-finite-quotient-data (one hole).
No other hole is added. This is a decomposition with net zero holes closed, not a
sorry-free proof of the target. The entire polynomial presentation and compatibility
argument is now kernel-checked; the finite local completion comparison remains open.
The proposed completion_finite_quotient_presentation hole has been discarded.

## No longer needed

The direct target import Sheaf.RingTheory.CompletionFiniteExtension is removed, but
remains transitively imported by CompletionFiniteQuotientData. No existing module is
claimed pruned. The proposed CompletionFiniteQuotientPresentation module and node were
never landed and are not delivered.

The target's old proof_deps no longer used directly are
lem-weil-pbc-monic-quotient-free, def-weil-finitely-generated-module,
lem-weil-pbc-finite-algebra-is-integral,
lem-weil-pbc-integral-maximal-contracts-maximal,
lem-weil-pbc-integral-prime-over-maximal-maximal,
lem-weil-pbc-localization-units-or-zero, def-weil-pbc-localization-at-prime,
def-weil-pbc-adic-completion, lem-weil-pbc-completion-finite-extension,
def-weil-polynomial-ring and def-weil-pbc-mv-polynomial-ring.
The first nine remain in the open comparison node's argument (and the polynomial-ring
notion remains a statement dependency); they are transferred, not globally pruned.
The generic MvPolynomial definition is unnecessary for the direct AdjoinRoot proof.
The existing presentation-base-change node remains, specialized via Mathlib's
AdjoinRoot.tensorAlgEquiv, not via a new presentation theorem.

## Where the brief, the DAG or earlier work was wrong

The first worker merely divided the target conclusions into two new open theorems,
then reassembled the witnesses. Its presentation lemma duplicated the whole first
conclusion and its docstring did not contain a complete proof. The original item node
was not updated; the new node statements were not self-contained, and their searches
were copied from historical records rather than run for these nodes. The second reader
removed the presentation lemma, wrote the actual base-change proof, supplied a complete
natural-language proof for the remaining hole, and updated the original route record.

## New nodes

lem-weil-pbc-completion-finite-quotient-data is the single-prime finite-completion
comparison (original plan steps 1-4). Its statement specifies every ring, ideal,
coordinate, and tensor formula, and its docstring explains the finite/integral reduction,
uniqueness of the prime, localization identifications, and transport of 07N9 including
S-linearity and the completed-base formula. It does not assert the polynomial
presentation, which the target now proves. No change record is needed: no existing
statement, definition, or public import changes.

## Second reading by M2

1. Compared the target with the repository using diff and an exact signature extraction:
   the theorem header through := by is byte-for-byte identical, as is its docstring.
   No other existing module is delivered; all four public imports are unchanged.
   No existing definition or statement is altered.
2. Compiled the two delivered modules in dependency order using lcompile.py. There is
   exactly one sorry, in the named comparison theorem; no forbidden declarations or
   hollow definitions. The axiom probe reports the target and comparison use only
   propext, Classical.choice, Quot.sound, and sorryAx from the comparison. All local
   equivalences in the target are explicitly constructed from Mathlib equivalences;
   existential witnesses are eliminated in a proof, never selected for a definition.
3. Read Stacks 07N9 (lemma-completion-finite-extension), 07PR (lemma-helper-G-ring),
   and 00MA (lemma-completion-tensor) at their tag pages. The remaining statement is
   exactly original steps 1-4, with Noetherian R, positive p, and local quotient S.
   Integrality gives the contraction and unique prime, so the quotient-level maps are
   well-defined. Tested conceptually p=1 (S is R by z=f), f=0 over a field (the nilpotent
   quotient is Artinian local and already complete), k=0 (both quotients are zero), and
   a ramified local quotient (cofinal mS- and n-adic filtrations; equality is not assumed).
   The base R cannot be the zero ring under IsLocalRing; no extra nontriviality is added.
   Fresh LeanFinder and grep searches found only finite-module completion ingredients;
   LeanSearch returned Internal Server Error, recorded as unavailable. Loogle found
   AdjoinRoot.tensorAlgEquiv and its root/coefficient formulas, used in the repair.
   Searched upstream WeilConjectures and lean/Sheaf for completion and finite-quotient
   statements: the existing general 07N9 theorem supplies the comparison's proof plan,
   but no direct finite local comparison with these unlocalized coordinates was found.
4. The target proves the presentation with the shortest direct Mathlib route found:
   tensorAlgEquiv, coefficient rid, mapAlgEquiv, then monomial compatibility. It no
   longer assumes a second copy of the first conclusion. All surviving public imports
   occur in the target signatures; the comparison import is proof-only. All old target
   proof_deps removed or transferred are listed above. Read dag/units/sk-thm-p1.json
   realized: neither this item nor its comparison realizes a unit step, and the existing
   curve-calculation and strict-henselian unit route is retained. Blueprint searches for
   completion and polynomial quotient found no duplicate blueprint statement.
5. The original node now records the open finite-completion comparison followed by the
   proved polynomial base change and compatibility. Its proof_deps equal the union of
   the steps' uses. The new comparison node copies precisely original steps 1-4, with
   the union of their actual dependencies, complete source and signature records, and
   fresh recorded searches. The invalid presentation node is absent.

Changes made by the second reader: removed the redundant presentation hole and node;
wrote the real polynomial base-change/compatibility proof; completed the comparison
proof docstring and self-contained node statement; corrected search provenance and the
original node's proof route; restored the general finite-extension import in the open
comparison module; rewrote the report to distinguish decomposition from proof.
