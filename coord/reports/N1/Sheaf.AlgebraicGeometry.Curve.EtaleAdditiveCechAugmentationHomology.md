## What changed

Reduced `exists_additiveCech_augmentation_homology` to separate alpha and beta
comparison statements. The existing signature, visibility and docstring stay unchanged.
The complete combining proof builds the alpha homology equivalence from a
quasi-isomorphism, builds the beta equivalence with `AddEquiv.ofBijective`, lifts cycles,
and proves both representative formulas using naturality and injectivity of cycle inclusion.

## Proved and sorry left

Closed the hole in `AlgebraicGeometry.Scheme.Modules.exists_additiveCech_augmentation_homology`.
This is a decomposition, not a proof without sorry dependencies.
The alpha comparison is the existing node `lem-pbc-etale-additive-cech-alpha-quasiiso`
(and its still-open theorem
`AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_alpha_quasiIso`), reused directly.
This delivery does not prove or change that theorem. It closes one original local hole
and adds one strictly smaller beta hole, so the net hole reduction is zero.
Added one hole:

- `AlgebraicGeometry.Scheme.Modules.exists_additiveCechBeta_homology`
  (`lem-pbc-etale-additive-cech-beta-homology`).

The new beta statement is strictly part of the argument: it has no global-resolution
complex or alpha assertion. The reused alpha statement has no coefficient complex or
affine hypotheses. The sole hole in delivered modules is the beta theorem above;
the imported alpha theorem remains open. No data are defined from a mere existence witness.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation`,
`Sheaf.Algebra.Homology.FirstQuadrantAugmentation`,
`Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural` and
`Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison` from the main module.
All four old proof_deps are replaced at the main node by the alpha and beta comparison
nodes: `lem-sc-etale-open-cech-injective-augmentation`,
`lem-sc-first-quadrant-column-augmentation`, `lem-sc-etale-tensor-unit-sections-natural`,
and `lem-sc-etale-qcoherent-ulift-finite-cech-comparison`. They remain dependencies of
the comparison plans: the first two through the existing alpha module, and the last
three through the new beta module. No module is claimed as globally pruned, and no
original mathematical dependency has been shown unnecessary.

## Where the brief, the DAG or earlier work was wrong

The finite lifted Čech comparison gives only a nonempty equivalence in positive degree.
Its signature does not expose beta or a cycle normalization, and it does not cover degree zero.
Thus applying it directly cannot supply the specified augmentation formulas. The new beta
statement isolates that missing chain-map and descent interface, including degree zero.

The alpha statement needs only a finite covering, not affine intersections or separatedness.
Both comparison statements allow empty covers (forcing the empty scheme), zero groups, repeated
opens and empty intersections. Their proofs follow the same two augmentations as the item;
no unit statement or unit step is bypassed.

Searches were run through msearch.py: LeanSearch was unavailable (HTTP internal server error);
LeanFinder and Loogle located generic quasi-isomorphism and homology naturality APIs;
grep found no explicit alpha/beta theorem. Blueprint search for augmentation found only
definition-level results, not these comparison statements. The source tags 01FD, 03P2 and
03AW were read from the Stacks Project website; the local literature mirror contains no
Stacks source files on this machine.

## New nodes

`lem-pbc-etale-additive-cech-beta-homology` states the additive cycle lift and
bijective homology descent of the coefficient augmentation. Its new module is
`Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaHomology`.

The original node now records the actual combining proof and these two dependencies.
No change record is needed because no existing statement, definition or public import changes.

## Second reading by N1

1. Compared the main module with the repository using diff and checked the complete
   existing theorem signature byte for byte. Verdict: unchanged hypotheses,
   conclusion, visibility, definitions and public import. The alpha sandbox copy
   was identical to the repository and has been removed from the delivery.
2. Read the combining proof: alpha uses cyclesMap and the homology isomorphism of
   the specified quasi-isomorphism; beta uses its bijective additive map. Monicity
   of iCycles makes every supplied lift equal to the canonical lift, and homology
   naturality gives the representative formulas. No arbitrary data definition is
   introduced. Local compilation and explicit axiom checks are recorded below.
3. Read the beta theorem and docstring against Stacks Tags
   [01FD](https://stacks.math.columbia.edu/tag/01FD) and
   [03P2](https://stacks.math.columbia.edu/tag/03P2). Verdict: true, strictly smaller
   than the combined item, and it retains the actual coefficient augmentation.
   In degree zero it is sheaf gluing; on a singleton affine cover positive
   homology vanishes; empty covers force the empty scheme and zero groups.
   Repeated opens and empty intersections preserve the same argument. Searched
   with different LeanFinder and grep terms and Loogle cyclesMap_i: generic
   chain/homology APIs exist, but no theorem identifies this explicit beta with
   the affine-cover edge map. The existing beta_closed theorem only states
   closedness, and the finite Cech comparison exposes neither beta nor degree
   zero. Thus neither closes the beta hole in a short proof.
4. Checked the top-down reduction, all four original proof_deps, and
   dag/units/sk-thm-p1.json realized. Verdict: both augmentation faces are kept,
   no unit step is bypassed, and no global module pruning is claimed. The main
   module's private proof imports suffice. Added private proof-dependency imports
   to the open beta module so its imports retain its recorded proof plan.
5. Checked the main node's three proof steps against the Lean proof, its two
   proof_deps, and proof_origin. Checked all required fields of the new beta node,
   its exact Lean statement, source, searches, unit and chapter. Verdict: they
   agree with the Lean and the decomposition; no change record is required.

Clarified the beta node plan: apply the finite comparison to singleton affine
covers to obtain positive-degree vanishing; do not assume its bare equivalence
identifies the explicit augmentation. The flipped total comparison also uses
the signed flip-total isomorphism, which is unsigned on resolution degree zero.

Changes made by the second reader: corrected the report's false claim that an
alpha theorem was proved; explicitly counted the unchanged imported alpha hole
and the zero net hole reduction; removed the unchanged alpha copy; retained the
beta plan's three dependency modules by private imports; expanded the complete
list of old dependencies replaced at the main node. The combining proof and the
new beta statement were left unchanged.

Verification: `lcompile.py --all` compiled both delivered modules without errors
or warnings. An appended scratch-copy `#print axioms` for the combined theorem,
the beta theorem and the reused alpha theorem reported exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx` in each case; the latter is expected
from the explicitly reported open comparisons and their imported dependencies.
The scratch copy was removed before delivery. Static checks found zero local
holes in the main module, exactly one in beta, no forbidden declarations, and
matching node signatures and proof-dependency unions.
