## What changed

Replaced the sorry in AlgebraicGeometry.IsCurve.dense_open_high_cohomology_pullback
with a complete Lean proof. It constructs the reduced closed complement, applies the
existing open-closed short exact sequence, forgets coefficients by a proved private
helper, and pulls back the sequence. Exactness and vanishing of its third term in
degrees one and two give injectivity and surjectivity separately. The theorem's
signature and public imports are unchanged. Removed five unused proof imports listed below.
Added proof imports of
Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme,
WeilConjectures.SixFunctors.OpenClosed.Exact, and the new complement-vanishing module.
The private coefficient-forgetting proof follows the existing proved
shortExact_map_forget₂ in WeilConjectures.SixFunctors.Etale.Gabber, without importing
that large module and its unrelated dependencies. Updated the item's proof and DAG dependencies.

## Proved and sorry left

Proved AlgebraicGeometry.IsCurve.dense_open_high_cohomology_pullback
(lem-pbc-s2-dense-open-cohomology-pullback): one of one original sorries closed.
Also proved the private underlyingAbelian_additive instance and
shortExact_underlying_abelian helper. No sorry remains in the item's module.
One new sorry remains: AlgebraicGeometry.IsCurve.dense_open_complement_pullback_vanishing,
node lem-pbc-k2-dense-open-complement-pullback-vanishing, in
Sheaf.AlgebraicGeometry.Curve.DenseOpenComplementPullbackVanishing.
This states vanishing for the closed direct-image term for arbitrary G, not a
renaming of the target's bijectivity assertion. The actual combination through the
short exact sequence and long exact sequence is proved in Lean.

## No longer needed

Compared with the repository version at second reading, removed these proof imports:
- Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
- Sheaf.AlgebraicGeometry.CurveCoefficientPair
- Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder
- Sheaf.Paper.ZeroDimensionalCohomology
- WeilConjectures.SixFunctors.Finite.Exact

The trial proof import WeilConjectures.SixFunctors.Etale.Gabber was also removed by
proving coefficient-forgetting exactness locally. All three public imports remain
necessary for the unchanged statement; the open-closed exactness import is used.

Every old proof dependency absent from the new direct proof_deps is:
- def-weil-pbc-curve-setting
- lem-weil-pbc-closed-point-residue-field-base
- lem-weil-pbc-finite-type-over-noetherian
- lem-weil-pbc-noetherian-finitely-many-components
- lem-weil-pbc-zero-dimensional-cohomology
- lemma-weil-pbc-finite-direct-image-exact
- lem-weil-pbc-cohomology-pullback-derived-unit
- lem-weil-pbc-extension-by-zero-adjunction
- lem-weil-pbc-pullback-cohomology-long-exact-ladder

The curve setting and extension-by-zero adjunction remain in the statement's
public imports. The geometric facts and finite-direct-image comparison remain in
the complement lemma's mathematical route. Thus these are removals from this
item's direct proof dependencies, not claims that every listed module is globally
unreachable. The new proof uses the existing Ext cohomology long exact sequence
rather than a pullback naturality ladder. No unit statement or realized step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG proof concealed the restriction/forgetting identification
and vanishing of the closed-complement term. These are now explicitly isolated.
The item had only its statement imports, despite the standing brief saying proof
imports were already present. Its blueprint ancestor lookup returns None because
the earlier created.item chain uses module names rather than node ids; the new
node names the imported dense-open-reduction ancestor explicitly.
The source was read at /home/ubuntu/c1-stacks-review/etale-cohomology.tex,
label lemma-restrict-to-open, proof and remark (d). The cited repository literature
file is absent on this machine. The checked source gives precisely closed-complement
vanishing and the long-exact-sequence argument. Constructibility is used there only
for degree-zero finiteness, which this theorem does not assert.
Edge cases checked: U=X gives empty complement and the zero direct-image sheaf;
empty X or W gives zero cohomology; dimension-zero X forces the dense open to be
all of X; zero G or the zero coefficient ring gives the same zero-object argument.
Nonreduced complements are allowed: zero-dimensional etale cohomology includes
nilpotent invariance. No torsion, smoothness, reducedness or constructibility is added.
LeanSearch returned an HTTP 500 and is recorded unavailable. LeanFinder, Loogle,
grep, both library roots and the DAG were searched; the finite-edge-map and Ext
exactness declarations were reused. No existing module states the complement lemma.

## New nodes

lem-pbc-k2-dense-open-complement-pullback-vanishing isolates positive cohomology
vanishing for arbitrary module sheaves pushed forward from the dense-open closed
complement, after arbitrary open restriction. Its proof records the finite boundary,
finite base-change comparison, module/abelian compatibility, finite edge map and
zero-dimensional vanishing. Its module is
lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenComplementPullbackVanishing.lean.
No definition, existing statement or public interface changed, so no change record
is required. Blueprint searches for dense-open complements and zero-dimensional
cohomology found no equivalent blueprint statement; a broad dense-open search
identified the imported dense-open-reduction ancestor, whose proof uses this fact.

## Second reading by K2

1. PASS: Compared the delivered item with the current repository by diff. The
   existing theorem signature and docstring are byte for byte unchanged; no
   definition or public import changed. The new theorem is separately named and
   recorded in its own node. No change record is needed.
2. PASS: Both modules compiled through lcompile.py in import order. The sole
   remaining sorry is the complete proof of the reported new public theorem;
   there are no hollow definitions or forbidden declarations. Read the exactness,
   coefficient-forgetting and long-exact-sequence proofs, including the definitional
   identification of R.f with the displayed pulled-back counit. Explicit axiom
   checks and the delivery probe check the trust basis; sorryAx is expected from
   the new vanishing obligation, not claimed eliminated. Explicit #print axioms
   gave only propext, Classical.choice and Quot.sound for both private helpers;
   the target and new theorem additionally use sorryAx, as reported.
3. PASS: The split theorem is positive cohomology vanishing of an arbitrary closed
   direct image, strictly a part of the argument, rather than a restatement of
   counit bijectivity. Read Stacks lemma-restrict-to-open and remark (d) in the
   available source. Density excludes every generic point of the complement;
   its dimension-zero reduction is a finite union of Spec k, and closed direct
   image commutes with open restriction. Checked U=X, empty X/W, dimension-zero
   X, zero coefficients and arbitrary nonreduced closed complements. Independent
   LeanFinder, Loogle and grep searches with direct-image/finite-support wording,
   and searches of both Lean roots, found no matching existing lemma. The known
   finite edge map and zero-dimensional theorem are already in the node's plan.
   Closing the new lemma requires substantial geometric and comparison work,
   beyond a short repair.
4. PASS: The proof uses the open-closed sequence and existing Ext exactness directly;
   no naturality ladder is needed. The three public imports serve the unchanged
   statement; all three remaining proof imports serve the proof. The private
   forgetting helper repeats the short proved argument in Gabber to avoid its
   unrelated import closure. Checked sk-thm-p1.realized: no realized statement or
   step is bypassed, and the dense-open curve reduction remains the route. Fixed
   No longer needed to list all five removed repository imports and all nine old
   dependencies absent from the new direct proof_deps.
5. PASS: Existing node changes are confined to proof, proof_deps and proof_origin.
   Their steps describe the actual Lean argument. The new node has the required
   source, complete mathematical proof, dependency union, search records, creation,
   blueprint ancestor, chapter/unit and verbatim normalized Lean signature.

Changes by second reading: corrected the stale import/pruning claims in this report
and added this review. No Lean proof or statement needed repair.
