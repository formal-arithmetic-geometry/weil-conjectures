## What changed

Proved AlgebraicGeometry.IsCurve.dense_open_low_base_change without changing its signature.
Added proof-only imports of DenseOpenClosedTerm, PullbackCohomologyLongExactLadder, and
Mathlib.Algebra.FiveLemma. The existing proved pullback ladder and Mathlib's additive
four-lemma variants complete the simultaneous degree-zero/one diagram chase.
The geometric first step is isolated in the new module DenseOpenClosedTerm.

## Proved and sorry left

Proved AlgebraicGeometry.IsCurve.dense_open_low_base_change (one of one original sorries).
The only new sorry is AlgebraicGeometry.IsCurve.dense_open_closed_term, node
lem-pbc-k2-dense-open-closed-term. It states an actual short exact cokernel of the counit,
its degree-zero comparison bijection, and degree-one vanishing on both rows; it does not
restate the comparison equivalence. Both modules compile without warnings.
The remaining geometric assertion has been checked for the empty scheme, full open,
empty complement, arbitrary stalk modules, and nonreduced curves. Its proof follows
[Stacks Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA), whose online proof was read
because the literature checkout is not present on this machine. The source's
constructibility hypothesis is used for finite stalks, not for the closed-term
vanishing or comparison needed here.

## No longer needed

Removed from the parent module (proof-only imports):
- Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
- Sheaf.AlgebraicGeometry.CurveCoefficientPair
- Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections
- Sheaf.Paper.InverseImageStalkGerm
- Sheaf.Paper.ZeroDimensionalCohomology
- WeilConjectures.SixFunctors.Finite.Exact
- WeilConjectures.SixFunctors.OpenClosed.Exact

The geometric proof imports move to DenseOpenClosedTerm, except CurveCoefficientPair:
the unchanged signatures use IsCurve directly and need no torsion coefficient pair.
DenseOpenClosedTerm additionally imports Finite.BaseChange for its planned closed-term
base-change identification. Both existing public imports of the parent are retained.

Every old dependency removed from the parent's direct proof_deps is listed here:
- def-weil-pbc-curve-setting
- lem-weil-pbc-closed-point-residue-field-base
- lem-weil-pbc-cohomology-pullback-derived-unit
- lem-weil-pbc-extension-by-zero-adjunction
- lem-weil-pbc-finite-type-over-noetherian
- lem-weil-pbc-inverse-image-stalk-germ
- lem-weil-pbc-noetherian-finitely-many-components
- lem-weil-pbc-open-closed-short-exact
- lem-weil-pbc-zero-dimensional-cohomology
- lem-weil-pbc-zero-dimensional-pullback-global-sections
- lemma-weil-pbc-finite-direct-image-exact

These remain dependencies of the geometric split node; no original geometric node is
pruned globally. The ladder and five-lemma nodes remain direct dependencies of the parent.
The unused CurveCoefficientPair import is removed; no claim is made that its module is
globally unreachable, since other curve items use it. The sk-thm-p1 dense-open reduction
route remains in place, and its realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker's snapshot initially imported no proof dependencies. The repository now
contains the planned proof imports and the proved ladder import; the comparison in this
second reading lists their actual removal or relocation above.
The geometric declarations are not individually shaped to supply the closed-term data
without additional glue; that glue is now a separate item. A pointwise equivalence
in each degree independently would not follow from the five-term ladder; the delivered
proof correctly transfers the simultaneous pair of bijections.

## New nodes

lem-pbc-k2-dense-open-closed-term: lean/Sheaf/AlgebraicGeometry/Curve/DenseOpenClosedTerm.lean,
AlgebraicGeometry.IsCurve.dense_open_closed_term. It contains precisely the geometric
construction and acyclicity of the closed term (original proof step 1), leaving the
nontrivial simultaneous diagram chase completed in the parent module. No change records
are required because all existing signatures and public imports are unchanged.

## Second reading by K2

1. Compared both delivered modules with the repository. DenseOpenClosedTerm is new;
   the only existing declaration, dense_open_low_base_change, has a byte-for-byte
   unchanged signature, with unchanged public imports and no definitions altered.
   No change record is required. Verdict: pass.
2. Compiled both modules locally in import order without errors or warnings. The only
   local sorry is the named dense_open_closed_term theorem. Scratch #print axioms checks
   show only propext, Classical.choice, Quot.sound and sorryAx (the open geometric input).
   No forbidden declarations, attributes, or hollow definitions occur. Verdict: pass
   as a partial proof, not an axiom-free closure of the parent.
3. Read the closed-term statement and complete proof docstring against Stacks 0GJA,
   including the open-closed exact sequence, finite direct image, and remark (c).
   Checked U=X, X empty, empty complement, dimension-zero X (density forces U=X),
   nonreduced X (the reduced complement has the same etale topos), and arbitrary,
   possibly infinite module stalks. Constructibility is needed for finite stalks,
   not for these vanishing or comparison claims. The split supplies only the geometric
   first step; the parent contains the actual simultaneous four-lemma diagram chase.
   Independent leanfinder, loogle and grep searches, plus direct rg in lean/, found
   upstream open-closed exactness and finite exchange inputs but no duplicate of this
   combined closed-term statement. Existing comparison lemmas require extra torsion or
   constructibility assumptions or cover only higher degrees. Closing the geometric
   glue is not a few-minute application of an existing declaration. Verdict: pass.
4. Read the parent proof from the target downward and checked each exactness segment
   and each injective/surjective vertical-map hypothesis. It uses the proved canonical
   pullback ladder and Mathlib's additive four-lemma variants, with Unit for the zero
   endpoints. Both directions use the simultaneous degree-zero/one hypotheses correctly.
   No shorter whole-statement route was found. Proof imports are private; the geometric
   split retains the imports for its pending plan, with finite exchange added explicitly.
   The removed imports and every old direct dependency are now enumerated above.
   Checked dag/units/sk-thm-p1.json: the dense-open reduction of the curve calculations
   is preserved, with no realized step bypassed. Verdict: pass.
5. Checked both node records against Lean, including proof_deps equal to the union of
   step uses, source, proof_origin, chapter/unit, blueprint parent, creation fields,
   searches, and Lean declaration/module. Replaced the new node's flattened signature
   with its verbatim multiline Lean signature, and added lemma-weil-pbc-finite-exchange
   to the geometric plan's dependencies for its closed-direct-image base change.
   Verdict: pass after these metadata repairs.

Second-reading changes: completed the pruning report against the current repository;
retained geometric plan imports in the split module; added the finite-exchange input;
recorded independent searches; corrected the new node's verbatim signature. No existing
statement or proof body changed.
