## What changed

The item now proves the unchanged derivedLimitRoosAbelianGroups from the positive-degree
Roos computation in the new module Sheaf.CategoryTheory.RoosPositiveDerivedLimit.
The kernel identification and its naturality are proved outright via kernel.lift,
limit.lift, NatTrans.ofOpSequence, projection extensionality and kernel-inclusion cancellation.
Finite-limit preservation is inferred directly from Mathlib. Existing enough-injectives
and additivity proofs are preserved. No existing public signature or definition was changed. The second reading makes
OfSequence a proof-only import and uses the public Category.Preorder import for
the natural-number indexing in statements.

## Proved and sorry left

Closed the original hole CategoryTheory.derivedLimitRoosAbelianGroups
(lem-pc-derived-limit-roos-abelian-groups) by decomposition: one hole closed, one added;
net zero holes. The entire degree-zero kernel comparison and its naturality, and the
finite-limit-preservation conjunct, are now genuinely proved.
Added one remaining hole CategoryTheory.roosPositiveDerivedLimit
(lem-pc-roos-positive-derived-limit), in its own module. It contains only degree-one
cokernel/naturality and higher vanishing, strictly fewer conclusions than the original.
No sorry remains in the item; every helper is completely proved. The two structural
clauses were already proved before this delivery and are not counted as newly closed.

## No longer needed

Removed direct imports Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact
(lem-pc-tower-limit-left-exact) and Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor
(lem-weil-pbc-horseshoe-delta-functor). The left-exactness hole is not used: Mathlib
infers finite-limit preservation. HorseshoeDeltaFunctor is not used by the completed
kernel argument; its result is still needed in the new positive-degree node's future
proof, so this is a direct-import removal, not a claim it is mathematically unnecessary.
The main node no longer directly needs lem-pc-tower-surjective-lim-acyclic, since it
uses the new positive-degree lemma; the latter still needs that acyclicity in its plan.
InjectiveTowerEmbedding and InjectiveSplitTower remain used by the structural theorem.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing sandbox was identical to the base and provided no reduction.
The planned surjectiveTowerLimitAcyclic module publicly imports the current item,
so the current item cannot import it directly without a Lean cycle. The new
positive-degree module is independent of the current item and takes the structural
instances as hypotheses. A future worker using SurjectiveTowerLimitAcyclic there
must first untangle its structural-instance import; this delivery adds no cycle.
The finite-limit-preservation clause needs no new proof theory or holed project lemma.
Edge cases: the zero tower gives zero throughout; for a constant tower with identity
transitions the kernel consists of constant tuples and the positive cokernel vanishes.
The proved kernel construction works for arbitrary transitions, without surjectivity.

## New nodes

lem-pc-roos-positive-derived-limit, at
 dag/nodes/sec-picard-framework/lem-pc-roos-positive-derived-limit.json,
states only the positive-degree computation and retains source steps 3 and 4.
Its sole theorem is in lean/Sheaf/CategoryTheory/RoosPositiveDerivedLimit.lean.
Searches were actually run and logged; LeanSearch was unavailable, while LeanFinder,
Loogle and Mathlib grep found generic derived-functor facts but no exact match.
The import visibility correction is recorded in
coord/changes/DerivedLimitRoosAbelianGroups-imports.md; signatures are preserved.

## Second reading by P1

1. Compared the item against the repository with diff. Every existing declaration's
   signature and the roosMap definition are byte for byte unchanged; the structural
   proofs are preserved. The new helpers are private and construct actual maps,
   cones and an isomorphism. No existing statement or definition changes. The preflight requires an import
   change record; coord/changes/DerivedLimitRoosAbelianGroups-imports.md records it. Verdict: pass.
2. Compiled both modules in import order with lcompile.py, without errors or warnings.
   Scanned the delivered Lean: the sole sorry is the named public theorem
   CategoryTheory.roosPositiveDerivedLimit. No axiom, unsafe, opaque, implemented_by,
   extern, or hollow definition occurs. Scratch #print axioms probes show only
   propext, Classical.choice and Quot.sound for roosLimitAdditive and each new kernel
   helper, including the cone, isomorphism and naturality. roosTowerEnoughInjectives,
   the main theorem and the positive-degree theorem additionally have sorryAx from
   the existing structural dependencies or the reported open theorem. Verdict: pass;
   the main theorem is conditional on open lower proofs, not axiom-closed.
3. Read the new positive-degree Lean statement and node against Stacks Tag 07KW,
   Lemma 15.88.1, assertions (1)-(3) and its B/C construction, online at
   https://stacks.math.columbia.edu/tag/07KW (the local literature file is absent).
   Checked n=0: B_0=A_0, C_0=0, the injection is the identity. Downward recursion
   proves surjectivity of B_n -> C_n without any surjectivity hypothesis on A.
   The zero tower gives zero kernel/cokernel. Constant identity towers give constant
   tuples and an onto difference map (solve x_(n+1)=x_n-y_n). As a non-surjective
   check, the integer tower with transition multiplication by 2 has zero limit;
   the statement allows its nonzero degree-one cokernel and only asserts vanishing
   above degree one. The docstring explains exactness, acyclicity, the long exact
   sequence, the canonical cokernel factorisation and its naturality. Explicit
   EnoughInjectives/Additive parameters are structural instances, not assumptions
   on transitions. There is no arbitrary data choice from this existence theorem
   in any definition. The split omits the genuinely proved kernel identification
   and left exactness, so it is strictly smaller, not an equivalent renaming.
   Independently searched LeanFinder for higher-derived-limit vanishing and Loogle
   for rightDerived with lim, and rg searched lean/Sheaf, lean/WeilConjectures,
   the upstream source checkout and Mathlib's abelian category theory. Searches
   found generic injective vanishing, not this theorem. Read RoosComplex.lean:
   its K-injective complex comparison is a different, still open statement and
   does not directly supply the required Mathlib rightDerived computation.
   Verdict: pass; the remaining homological work cannot be closed in a few minutes.
4. Read from the main theorem down through every kernel helper. The proof first
   constructs the kernel comparison by universal properties and obtains finite-limit
   preservation from Mathlib. Only positive degrees use the new open theorem.
   Removed imports and every dropped old proof dependency are listed above:
   lem-pc-tower-limit-left-exact, lem-weil-pbc-horseshoe-delta-functor, and
   lem-pc-tower-surjective-lim-acyclic. The latter two remain in the positive node's
   mathematical plan; no claim of their removal from the whole import closure is
   made. Read dag/units/sk-thm-picard-duality.json: realized.statement=[] and
   realized.steps=[[]]; this subordinate reduction changes no realized route.
   Verdict: pass, a decomposition with one closed and one added hole, net zero.
5. Compared the existing node diff: only proof, proof_deps and proof_origin differ.
   Its steps follow the structural proofs, kernel construction and final packaging.
   The new node's Lean signature matches its module, its source and two proof steps
   follow the source B/C construction and the cited acyclicity/long-exact statements,
   and it records creation, chapter/unit, blueprint ancestry and actual searches.
   Read SurjectiveTowerLimitAcyclic.lean and confirmed its import of this item;
   the report correctly warns about the future import-cycle obstruction without
   introducing a Lean import cycle in this delivery. Verdict: pass.

Changes by this reader: changed the main module's OfSequence import to proof-only,
added public Category.Preorder for the index-category statements, and replaced the
new positive module's unnecessary public OfSequence with Category.Preorder. Removed
one extra blank line. The mathematical proofs and new theorem statement were left
unchanged. Updated this report with independent source, search and axiom findings.

The dry-run preflight requested a change record for the public import correction.
Added coord/changes/DerivedLimitRoosAbelianGroups-imports.md after checking the seven
direct importers with downstream.py. MilnorSequence is the only sequence-constructor
user among them and already has its own plain OfSequence import; no adaptations needed.
