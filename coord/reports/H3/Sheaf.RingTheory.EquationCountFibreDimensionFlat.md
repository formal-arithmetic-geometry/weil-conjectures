## What changed

Closed the proof of `MvPolynomial.exists_flat_away_of_fibre_dimension_eq` in
`Sheaf.RingTheory.EquationCountFibreDimensionFlat`. Its signature, visibility,
public imports, and existing docstrings are unchanged. Updated its DAG node's
proof, proof dependencies, and proof origin to match the Lean argument.

The shorter route uses the existing
`Algebra.exists_localization_relativeGlobalCompleteIntersection` (Stacks 00ST (3)).
Unfold its intrinsic complete-intersection predicate, apply
`Algebra.flat_of_isRelativeGlobalCompleteIntersection_quotient` (00SW) to the
finite presentation it supplies, and transport flatness through the algebra
isomorphisms to the principal localization. Construct the canonical further
localization at the prime and use `IsLocalization.flat` and `Module.Flat.trans`.
For the last clause, give the prime localization precisely the algebra structure
from the stated `Localization.localRingHom`; its scalar compatibility follows
from `Localization.localRingHom_to_map`. Then use
`Module.flat_iff_of_isLocalization` (00HT (2)). No auxiliary definitions or
witnesses chosen in definitions were added.

Added proof import:
- `Sheaf.RingTheory.EquationCountLocalizeRelativeGlobalCompleteIntersection`.

The second reader removed the redundant direct import of
`Mathlib.RingTheory.Localization.LocalizationLocalization`: the existing public
`Mathlib.RingTheory.RingHom.Flat` import already supplies it transitively.

Searches: LeanFinder via `msearch.py` for equation-count flatness returned smooth
flatness and standard smoothness results, which require stronger hypotheses.
Loogle searched `Module.Flat, Localization.AtPrime`. Local `rg` over both library
roots found the existing equation-count localization declaration, which already
packages the first step. Read both definitions of relative global complete
intersection and the flatness declaration before applying them. The proposed
import passes `tools/import_direction.py may`. Read the unit record
`dag/units/sk-thm-p1.json`: none of its realized statement or proof-step nodes
is bypassed by this reduction; both substantive dependencies are in this unit.

The local Stacks TeX and original blueprint section are absent on this machine.
Checked the source against the official pages for
[00ST](https://stacks.math.columbia.edu/tag/00ST),
[00SW](https://stacks.math.columbia.edu/tag/00SW), and
[00HT](https://stacks.math.columbia.edu/tag/00HT).
The final single-file compile succeeded with no warnings.

## Proved and sorry left

Closed the sole hole:
`MvPolynomial.exists_flat_away_of_fibre_dimension_eq`
(node `lem-weil-pbc-equation-count-fibre-dimension-flat`).

There are no sorries left in the delivered module and no holes added or split off.
This is a proof from existing stated dependencies, rather than a new decomposition.
It still depends on the existing sorries
`Algebra.exists_localization_relativeGlobalCompleteIntersection`
(node `lem-weil-pbc-equation-count-localize-relative-global-complete-intersection`)
and `Algebra.flat_of_isRelativeGlobalCompleteIntersection_quotient`
(node `lem-weil-pbc-relative-global-complete-intersection-flat`), which are next
items under stage 3. All three original conclusions are proved unchanged.

Edge cases are retained: arbitrary coefficient ring without Noetherian hypotheses,
`N = c`, and `c = 0`. The original `c ≤ N` hypothesis suffices for the existing
localization theorem. An empty spectrum requires no special argument because the
statement quantifies over a prime. No nontriviality or field hypothesis is added.

## No longer needed

Removed these direct imports:
- `Sheaf.RingTheory.FibreDimensionNeighborhood`, node
  `lem-weil-pbc-fibre-dimension-neighborhood`;
- `Sheaf.RingTheory.PolynomialQuotientDimensionLowerBound`, node
  `lem-weil-pbc-polynomial-quotient-dimension-lower-bound`;
- `Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`, a redundant proof
  import since `Sheaf.RingTheory.RelativeGlobalCompleteIntersectionFlat` publicly
  imports it. Its definition node remains needed.

The following original direct proof dependencies are subsumed by the existing
localization lemma and are removed from this node's `proof_deps`:
`lem-weil-pbc-fibre-dimension-neighborhood`,
`lem-weil-pbc-localization-away-universal-property`,
`lem-weil-pbc-polynomial-scalar-extension`,
`lem-weil-pbc-tensor-quotient-base-change`, and
`lem-weil-pbc-polynomial-quotient-dimension-lower-bound`.
Scalar extension and tensor-quotient base change remain transitive dependencies
of the imported localization lemma; this report does not claim they are globally
unreachable. The flat-local-ring-maps node
`lem-weil-pbc-flat-local-ring-maps` is also no longer directly needed: the last
clause instead uses `lem-weil-pbc-flat-over-localization`. Localization transitivity,
localization flatness, the complete-intersection definition, complete-intersection
flatness, and the flat-module definition remain needed. No unit-level realized
statement or step was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The original DAG plan repeats
the argument already supplied by the existing equation-count localization node;
using that declaration makes a shorter composition. Its Option-indexed enlarged
presentation need not be reindexed here, because the intrinsic complete-intersection
predicate already supplies a Fin-indexed presentation to which the flatness lemma
applies. The old proof docstring describes the expanded route; the updated node
records which existing declaration packages those steps and the actual final
flat-over-localization argument. No target, statement, definition, or other module
was changed, so no change record or forced adaptation is needed.

## Second reading by H3

1. Compared the only delivered Lean module with the repository using `diff`.
   Restored a stray proof comment and indentation inside the theorem signature;
   verified the entire existing signature is now byte for byte identical.
   Public imports, visibility, definitions, and existing docstrings are unchanged.
   No other Lean module, new declaration, or change record is delivered. PASS.
2. Compiled the module locally through `lcompile.py` without errors or warnings.
   The delivered source contains no `sorry`, forbidden declaration, or hollow
   definition. A scratch copy with
   `#print axioms MvPolynomial.exists_flat_away_of_fibre_dimension_eq` reports
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is expected from the two existing open dependencies listed above;
   this delivery closes one local hole, not its complete dependency closure.
   Checked that flatness is transported along R-algebra equivalences and that
   the final algebra structure is precisely the stated `localRingHom`, with
   scalar compatibility proved by `localRingHom_to_map`. PASS.
3. There are no split-off statements or new nodes to validate. The existing
   localization theorem supplies a strictly separate geometric step, followed
   by the existing complete-intersection flatness theorem and Mathlib localization
   flatness. Existential witnesses are eliminated only inside this theorem proof;
   no data definition is chosen from a mere unproved existence theorem.
   Checked the boundary cases `c = 0`, `N = c`, and the zero coefficient ring:
   no extra hypotheses enter the argument, and the zero ring has no prime `q`.
   Independently searched the library for flatness from fibre dimension and
   Mathlib for flatness/localization results; Loogle query
   `Module.Flat, IsLocalization` confirmed the exact localization lemmas used.
   No shorter applicable proved equation-count theorem was found. PASS.
4. Read both complete-intersection definitions, the two substantive dependencies,
   the Mathlib localization constructions, and the `sk-thm-p1` unit's `realized`
   record. The reduction is below unit level and bypasses no realized unit step.
   All six removed old direct proof dependencies are listed under
   `## No longer needed`; this is direct-dependency pruning, without claiming
   that their modules are unreachable from every target. Removed the redundant
   added Mathlib localization import and compiled a scratch copy without it
   successfully. The remaining two proof imports are used. PASS.
5. Compared the delivered node with its repository version: only `proof`,
   `proof_deps`, and `proof_origin` differ. Checked that `proof_deps` is exactly
   the union of the proof steps' `uses`, and that every step matches the Lean
   argument, including the extracted finite presentation and the final
   flat-over-localization equivalence. Independently checked the source route
   against [00ST](https://stacks.math.columbia.edu/tag/00ST),
   [00SW](https://stacks.math.columbia.edu/tag/00SW), and
   [00HT](https://stacks.math.columbia.edu/tag/00HT). PASS.

Second-reading changes: restored the signature text, removed one redundant
proof import, and corrected the import list in this report. The mathematical
proof and node record required no repair. Holes closed: one; holes added: zero.
