## What changed

Re-delivered `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal` with an explicit
three-step `calc` proof for `determinant_split_comparison_restriction`. The proof rewrites the
converted linear equivalence to the retained natural linear family on both sides and applies its
restriction naturality. The repaired interface already present in the library uses `dNatural` and
its naturality hypothesis, so the unconstrained tuple-family counterexample from upstream review
cannot apply.

## Proved and sorry left

`determinant_split_comparison_local` and `determinant_split_comparison_restriction` are proved.
No `sorry` remains in the delivered module, and no new declarations were added.
Holes closed relative to the repository: none (both declarations were already proved).
Holes added: none. This is a repair-item proof refinement, with net hole reduction zero.

## No longer needed

None. The imports and proof dependencies recorded by the existing DAG node remain necessary for
the local construction; the restriction proof uses only its explicit naturality and equality
hypotheses.

## Where the brief, the DAG or earlier work was wrong

The upstream review correctly rejected the former statement with an unconstrained family `c`.
The repository had already repaired that statement by replacing `c` and its generator equation
with a natural linear family `dNatural` and pointwise equality `hd`. The previous sandbox report
called this item verification-only, so `deliver3.py` rejected it as unchanged; this delivery
contains the explicit proof refinement while preserving the corrected signature.

## Second reading by N2

1. Compared the entire delivered module with the repository using `diff -u`.
   Only the body of `determinant_split_comparison_restriction` differs: the existing
   `simpa only [hd]` is expanded into a three-step equality calculation. Both theorem
   signatures, visibility, definitions, docstrings and imports are byte-for-byte unchanged.
   Read the landed natural-family correction record
   `coord/changes/determinant-split-restriction-right-inverse.md`: that correction predates
   this delivery. No new hypothesis or statement correction is introduced here. Verdict: pass.
2. Compiled the delivered file with `lcompile.py --all`, without errors or warnings.
   Scanned the entire delivery for sorry and forbidden declarations: none.
   Compiled a scratch copy with `#print axioms` for both fully qualified theorem names.
   Reviewed the local proof: it obtains the uniquely characterized linear family, applies
   local bijectivity on the same family, and uses `LinearEquiv.ofBijective`, whose forward
   map preserves the generator formula definitionally. No arbitrary witness is used to
   define data. The restriction calculation rewrites the source using `hd`, applies `hn`,
   and rewrites the target using `hd`. Both axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
   Verdict: pass.
3. No statement is split off and no new node or sorry is added. The local proof uses the
   existing `determinant_split_linear_maps_exists` and
   `determinant_split_linear_maps_locally_bijective`, whose signatures were read in full.
   The former is unique existence of a natural linear family, not unconstrained existence.
   Empty U makes the pointwise local assertion vacuous; zero ranks use empty tuples;
   the restriction argument also works on empty opens and for identity restrictions.
   No nonzero-ring or positive-rank assumption is smuggled in. Verdict: pass.
4. Searched the determinant modules for existing comparisons and conversions. The local
   construction already follows the short route through the two stated dependencies and
   `LinearEquiv.ofBijective`; the restriction proof is elementary equality substitution.
   The repository's one-line proof is shorter, but the delivered calculation exposes exactly
   the same reasoning without adding a dependency. Both plain proof imports are used;
   the public imports supply the exterior, tensor, locally-free, short-complex and biproduct
   statement language and preserve the existing exported interface. Neither old proof
   dependency is unused. No pruning is claimed. Read `dag/units/sk-thm-picard-rr.json`:
   its `realized` arrays are already empty; this delivery neither changes them nor bypasses
   a unit step. The blueprint source file named by the node is absent on this machine;
   this review checks the unchanged signatures against the available node records and
   landed correction record, not a fresh source-statement certification. Verdict: pass.
5. Read `new-determinant-split-local.json` and `new-determinant-split-restriction.json`.
   The local node's three steps match construction, local bijectivity, and conversion;
   its proof dependencies are precisely the two calls in Lean. The restriction node's
   elementary substitution step and empty proof dependencies match the new calculation.
   Their proof origins remain accurate; no node edit is necessary. Verdict: pass.

Second reading changed only this report: made the zero holes-closed/zero holes-added
accounting explicit and recorded the independent checks. The Lean proof refinement is retained.
