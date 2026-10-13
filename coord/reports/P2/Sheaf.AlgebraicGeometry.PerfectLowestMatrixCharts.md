## What changed

Replaced the whole proof hole of
`AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts` by a complete Lean
combination of the existing finite-free residue model, two narrower structural
statements, derived-pullback composition, and invariance of finite local freeness
of fixed rank under a homology isomorphism. Its signature and all original public
imports are unchanged. Added three proof-only imports for the residue model,
model restriction, and affine matrix locus, plus the proof-only derived-composition
import. Updated the item's DAG proof and dependencies to match.

Added two modules, each with one public theorem whose entire proof is `by sorry`:
`Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen` and
`Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus`. Both have source citations,
complete natural-language proofs, and matching new DAG nodes. No definition,
existing statement, visibility, or target signature changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts`
(node `lem-sc-perfect-lowest-matrix-charts`). There are no sorries in the item.

Added two holes:

- `AlgebraicGeometry.Scheme.lowestResidueModel_withinOpen`
  (node `lem-sc-lowest-residue-model-within-open`). This takes a supplied residue
  model and restricts/transports it inside a prescribed open, with terms below the
  Tor bound zero. It asserts no rank locus or representing closed scheme.
- `AlgebraicGeometry.Scheme.exists_affineFreeLowestMatrixLocus`
  (node `lem-sc-affine-free-lowest-matrix-locus`). This takes a supplied affine
  bounded-above finite-free complex starting in degree a with first rank s <= r.
  It asserts matrix representability, with no perfectness, Tor amplitude, Betti
  function, point, or choice of neighbourhood.

This is a decomposition, not a sorry-free proof of the original mathematical
result: one hole closed and two added, for net -1 before any closure effects.
Existing dependencies still containing sorry are reused as required by stage 3;
they are not new holes of this delivery. The main Lean argument genuinely combines
independent model and matrix steps, constructs the derived homology isomorphism,
and proves both directions of the desired factorization equivalence.

Local compilation of all three modules passes, with no compiler warnings.
The new statements were checked mathematically for r=0, s=0<r, empty sources and
bases, zero rings, and a>b. In the last case all residue ranks vanish. For s<r,
the padded square injection cannot exist over a nonzero affine source ring;
for s=r=0 the matrix ideal is zero and its closed subscheme is the entire chart.
These are mathematical edge-case checks, not claims that the remaining Lean
proof holes have been discharged.

## No longer needed

No original import or module is pruned. The flat-complex pullback,
square-injection dual-cokernel, quasi-coherent ideal closed-subscheme, and local
finite-presentation dependencies move from the item's immediate proof to the
new affine matrix node; they remain needed. The residue-model dependency remains
explicitly used. The original immediate proof dependencies no longer used directly by the item's
Lean proof are `lem-pc-flat-complex-derived-pullback`,
`lem-sc-square-injective-free-map-dual-coker-zero`,
`lem-weil-pbc-quasi-coherent-ideal-closed-subscheme`, and
`def-sbc-locally-finite-presentation`. Each is retained in the affine matrix
node's proof dependencies, so none is declared globally unnecessary.
No unit-level route is bypassed. No unrelated universal-freeness,
jump-locus, gluing, or degree-zero-only model module is imported.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned residue model lives on an over-site,
whereas the conclusion and derived pullbacks use module sheaves on the open
scheme. Exact restriction, transport through the module equivalence, and vanishing
below the Tor bound require a structural bridge not directly asserted by the
listed declarations. The first new node isolates precisely this bridge using an
already supplied model. The second isolates the scheme-theoretic matrix argument;
neither is the original statement under another name.

LeanFinder and pinned-source grep found no replacement for either new statement.
LeanSearch returned Internal Server Error and was recorded as unavailable, without
an absence verdict. Whole-blueprint searches for 0BDL, 0BCD, matrix, and residue
model yielded no duplicate statement. Existing residue-model and universal-free
bottom-model declarations were read; the latter assume universal freeness or zero
bottom differential and do not establish a representing locus here.

## New nodes

`lem-sc-lowest-residue-model-within-open`, in
`dag/nodes/sec-abelian-varieties/lem-sc-lowest-residue-model-within-open.json`,
states the open restriction and lower-bound step for a supplied model. Its module
is `Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen`.

`lem-sc-affine-free-lowest-matrix-locus`, in
`dag/nodes/sec-abelian-varieties/lem-sc-affine-free-lowest-matrix-locus.json`,
states the fixed-complex affine matrix representability step. Its module is
`Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus`.

Both inherit chapter `sec-abelian-varieties` and unit `sk-prop-av-cube`, have their
nearest blueprint ancestor recorded, and include three executed kinds of Mathlib
search. No change record or forced adaptation is needed.

## Second reading by P2

1. Interface: compared PerfectLowestMatrixCharts.lean with the repository using
   diff. The only changes are four plain, proof-only imports and the body of
   exists_perfectLowestMatrixCharts. Its existing declaration signature, docstring,
   visibility and six public imports are byte-for-byte unchanged. Both other
   modules and nodes are new; there is no definition or statement adaptation.
   Verdict: pass.
2. Proof and trust: compiled all three delivered modules locally in import order;
   all pass without warnings. Inspected every proof and definition, and appended
   #print axioms for each of the three public theorems through lcompile's temporary
   probe copies. Each lists exactly propext, Classical.choice, Quot.sound and
   sorryAx. The item has no sorry; the only new holes are the two named theorems
   listed above, each with its entire body `by sorry`. There are no new definitions,
   forbidden declarations or arbitrary data chosen from existence theorems.
   Verdict: valid decomposition, not an axiom-free mathematical completion.
3. Split statements: read both full signatures, docstrings and nodes and checked
   Stacks 0BDL, 0BCD and 0EWY. The restriction lemma preserves ranks at the same
   point, shrinks inside the prescribed open and uses the lower Tor bound only
   to kill lower fibre ranks. The matrix lemma works for every source scheme,
   not just affine sources: affine trivializations prove vanishing locally and
   closed-immersion monomorphy glues the factors. For s<r, padding a square
   injection contradicts transpose injectivity on every nonempty affine source.
   Checked s=r=0, s=0<r, empty schemes, zero rings and a>b. Both statements are
   true and strictly isolate separate parts of the argument. Independent
   LeanFinder search for exact restriction/free-module/derived-pullback transport
   and Loogle search for injective matrices found component results, not either
   complete statement. Independent rg searches read OpenPerfectModelTransport,
   OpenDerivedRestrictionComparison, PerfectUniversalH0BottomModel and the
   upstream Modules.Sheaf comparisons: their conclusions or extra hypotheses
   differ, so no complete replacement was found. Closing either remaining hole
   requires more than a short component-lemma application. Verdict: pass.
4. Route and pruning: followed the proof from the existing residue model through
   open restriction, affine matrix representability and the derived-composition
   homology isomorphism. Its directions are correct: eK.symm starts at Q(K), and
   eH and eH.symm transport the fixed-rank property in opposite directions.
   Each added import supplies a used declaration; the original public imports
   supply signature notions. All four old dependencies removed from the item's
   immediate proof are now named explicitly above and remain in the affine
   matrix node. Read sk-prop-av-cube.json: its realized statement is [] and its
   realized steps are [[]]; this delivery changes neither and stays below the
   unit's cube-theorem step. Verdict: no module pruned, unit route preserved.
5. DAG: checked the existing node's proof, proof_deps and proof_origin against
   each Lean step. The dependency union is exactly its five recorded nodes.
   The two new nodes have matching verbatim Lean signatures, chapter/unit,
   source, proof steps, dependency unions, origin, searches, split status,
   created and blueprint ancestry fields. Read the square-injection node's
   Mathlib composite: mulVec_injective_iff, linearIndependent_col_iff_row and
   vecMul_injective_iff justify the transpose argument. Verdict: pass.

Second reading changed only this report: made the four displaced immediate
proof dependencies explicit and recorded this independent review. No Lean
proof or statement needed repair. Counts remain one original hole closed,
two holes added, a decomposition with net -1 before closure effects.
