## What changed

Replaced the hole in `AlgebraicGeometry.principalOpenCech_homology_injective` by a
compiling reduction to two strictly separate steps of its existing proof plan.
The signature and all original public imports are unchanged. Added proof-only imports
of `Sheaf.AlgebraicGeometry.PrincipalOpenCechInjectiveComparison` and
`Sheaf.AlgebraicGeometry.PrincipalOpenCechInjectiveTerms`.

The comparison step supplies an actual commuting square to subset-coordinate complexes
with injective coefficient terms, with a quasi-isomorphism on the section side. It
makes no homology assertion about either augmentation. The injective-term step proves
monicity under termwise injectivity, without K-injectivity or boundedness. The original
module combines them using homology functoriality and `mono_of_mono_fac`; its proof has
no local holes. Updated the parent DAG proof and dependencies to this reduction.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.principalOpenCech_homology_injective`
(node `lem-sc-principal-open-cech-homology-injective`) by decomposition, not a complete
sorry-free proof. No sorry remains in the item module.

Added two named public holes, each the entire proof of its theorem:

- `AlgebraicGeometry.principalOpenCech_injective_comparison`, node
  `lem-sc-principal-open-cech-injective-comparison`.
- `AlgebraicGeometry.principalOpenCech_homology_mono_of_injective_terms`, node
  `lem-sc-principal-open-cech-injective-terms`.

This closes one upper hole and adds two lower holes: net -1 before any closure overlap.
Every lower statement is a part of the original argument, with its source and complete
proof in words in both its docstring and node. The comparison cannot alone establish
monicity, and the injective-term statement cannot apply to the original arbitrary
K-injective J without the comparison. No data is chosen in a definition from an
unproved existence theorem; all comparison witnesses are destructured inside the proof.

Compilation of all three modules succeeded via lcompile.py, independently repeated by the second reader. Boundary cases checked
mathematically: empty cover, empty or repeated opens, zero ring, and arbitrary unbounded
coefficient degrees. The row argument requires only the finite horizontal strip.

## No longer needed

No original public import was removed: each is used in the unchanged signature.

The injective half no longer needs `lem-sc-alternating-cech-total-homotopy` or its module
`Sheaf.AlgebraicGeometry.AlternatingCechTotalHomotopy`: only the section comparison must
be invertible on homology. The total comparison b need only be a chain map. This is a
pruning of this argument, not a claim that the module is globally unreachable; the
surjective half may still need it.

The original resolution and row-exactness dependencies have moved to the appropriate
new steps, and are not pruned:
`prop-pur-kinjective-resolutions-exist`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-module-injective-open-cover-cech-acyclic`, and
`lem-pc-alternating-cech-computes`. No other planned dependency is discarded.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan asks for homotopy equivalences on both
sides of the comparison square, but monicity needs one only on the section side.

The existing `kInjective_alternatingCech_augmentation_quasiIso` and
`injectiveTerms_alternatingCech_augmentation_quasiIso` use increasing tuples, scalar
modules over global sections, and a cover of the whole scheme. The item instead uses
finite subsets, A-module coordinates, and a cover of the possibly proper open V.
They are not directly applicable without the restriction, scalar and reindexing bridge.
Their proofs provide useful models for the remaining coordinate work; no duplicate of
their tuple-indexed statements was introduced. LeanSearch returned Internal Server
Error, recorded as unavailable; LeanFinder, Loogle and Mathlib/library grep completed.

WANTED: literature/stacks-project/cohomology.tex, Tag 08C1, and
literature/stacks-project/injectives.tex, Theorem 079P, for both new nodes.
These source files are absent in this read-only checkout. The new proof descriptions
are consequently marked `proof_origin.by = agent`; they expand the already recorded
parent proof and the existing resolution and row-exactness nodes.

## New nodes

`lem-sc-principal-open-cech-injective-comparison`, in
`lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechInjectiveComparison.lean`, isolates the
resolution and coordinate-comparison construction. Its output pins the displayed
section and subset-total differentials and singleton augmentation for injective terms;
it does not assume or assert the conclusion of the original theorem.

`lem-sc-principal-open-cech-injective-terms`, in
`lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechInjectiveTerms.lean`, isolates exact
augmented rows and finite-column boundary elimination under termwise injectivity.
There is no K-injectivity hypothesis, and no coefficient-degree boundedness hypothesis.
Both nodes stay in `sk-thm-picard-duality`; no unit or chapter route changed.
No existing statement, definition, visibility or downstream module was changed, and
no change record or forced adaptation is needed.


## Second reading by X2

1. **Unchanged public statements — pass.** Compared the original module with the
   repository version by diff and by extracting the theorem signature: it is byte
   for byte identical. Only proof-only imports, the proof body and its explanation
   change. The two other Lean files are new. No definitions, existing visibility,
   target statement, or downstream module changed; no change record is necessary.
2. **Kernel proof and holes — pass.** Independently compiled all three modules in
   import order with lcompile.py. The original theorem has no local hole. Exactly
   the two public named theorems listed above retain `:= by sorry`; each has a
   source, a complete proof description, and a node. No definitions or prohibited
   declarations occur in the delivered modules. The homology square is used in
   the correct direction: its right composite is monic, which forces the original
   homology map to be monic. Axiom verification is recorded below.
3. **Split statements and duplicates — pass.** Read both signatures and every
   differential and augmentation formula. The comparison statement asserts a
   resolution square, not monicity of an augmentation. The injective-term theorem
   has termwise injectivity and does not assume K-injectivity: it is the exact-row
   half of the argument, not a renamed assertion for arbitrary K-injectives.
   Checked r=0 (empty section and subset modules), r=1 (augmentation identifies
   the section complexes), repeated/empty opens, the zero ring, and unbounded
   coefficient degrees. The finite horizontal strip makes boundary elimination
   terminate without a vertical bound. Repeated LeanFinder, Loogle and Mathlib
   searches with different queries, and searched lean/ for subset comparisons,
   injective augmentations and exact finite rows. Read the existing proved
   injectiveTerms_alternatingCech_augmentation_quasiIso and
   kInjective_alternatingCech_augmentation_quasiIso and their finite-strip helper.
   They still require a coordinate/restriction/scalar bridge to apply here; neither
   new statement is already supplied in these coordinates. Closing either hole
   requires that bridge or an explicit subset construction, beyond a short repair.
4. **Top-down route, imports and pruning — pass.** The original theorem genuinely
   combines the two separate steps through homology functoriality. Every original
   import supplies names or structure in its unchanged signature; the new imports
   are proof-only. The old total-homotopy dependency is the only discarded planned
   dependency; the other four move to the lower nodes and remain recorded under
   No longer needed. This is decomposition, net -1 holes, not a complete proof.
   Read dag/units/sk-thm-picard-duality.json: its existing realized record is empty;
   this delivery neither changes that record nor bypasses any realized unit step.
5. **DAG agreement — pass.** Compared the parent node: only proof, proof_deps and
   proof_origin differ. Checked both new nodes' source, searches, created,
   blueprint, chapter, unit and Lean records. Their Lean signatures equal the
   normalized source signatures; each proof_deps is exactly the union of step uses.
   The nodes describe the constructions and exact-row argument left as the two
   named holes. No data is extracted into a definition from an existence hole.

**Second-reader changes:** corrected the original theorem's proof docstring to
match the one-sided monicity transfer actually compiled: only the section
comparison must be invertible on homology. The previous docstring unnecessarily
claimed two homotopy equivalences. No Lean proof, statement or node was rewritten.
The cited Stacks Tags [08C1](https://stacks.math.columbia.edu/tag/08C1) and
[079P](https://stacks.math.columbia.edu/tag/079P) were independently read online;
they confirm the finite-cover comparison route and injective K-injective
replacement. The coordinate constructions remain agent expansions as recorded.

**Axiom verification:** a scratch copy with `#print axioms` for all three
declarations compiled. Each printed exactly `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`; the last is expected for the two named lower holes.
The scratch copy was removed before delivery.
