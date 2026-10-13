## What changed

Completed the Lean proof of `AlgebraicGeometry.coherentFormalModule_annihilated_iff`
without changing any existing signature, definition or visibility. The proof now gives
five implications: (1) to (2), (2) to (3), (3) to (1), (3) to (4), and (4) to (2),
then assembles the TFAE. The finite affine subcover and positive maximum exponent are
proved directly using Mathlib. The (3) to (1) implication uses the existing kernel and
cokernel double-exponent declarations. The formal kernel and cokernel forks are the
canonical ones supplied by the existing abelianness theorem.

Two strictly narrower geometric steps are stated in separate new modules:
`CoherentFormalModuleAnnihilatedLimit` gives the fixed-exponent termwise-to-limit
implication on one affine open; `CoherentFormalModuleAnnihilatedFormalCover` tests
annihilation of given formal kernel and cokernel objects at a fixed exponent on an
arbitrary affine cover. Their docstrings and nodes give complete source-based proof
plans. The latter is used both for the finite cover and the cover of all affine opens.
Neither statement repeats the four-way equivalence or asserts that formal kernels
are termwise kernels.

The item's DAG proof and proof dependencies now describe all three of its declarations.
All delivered Lean modules compile locally without warnings. `deliver3.py --no-push`
printed OK: compilation and preflight passed except for the second reading, which
the second reader supplies. Nothing was pushed.

## Proved and sorry left

Closed the one remaining original hole:
`AlgebraicGeometry.coherentFormalModule_annihilated_iff`, node
`lem-weil-pbc-formal-systems-annihilated-by-power`.

The existing complete proofs of
`AlgebraicGeometry.coherentFormalModule_annihilated_double` and
`LinearMap.ker_coker_reduction_annihilated_double` are retained unchanged.
There is no `sorry` left in the item's module.

Added two named holes, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.coherentFormalModule_annihilated_affine_limit`, node
  `lem-weil-pbc-formal-annihilation-affine-limit`.
- `AlgebraicGeometry.coherentFormalModule_annihilated_formal_cover`, node
  `lem-weil-pbc-formal-annihilation-kernel-cokernel-cover`.

This is a decomposition: one hole closed and two strictly narrower holes added,
not an axiom-free proof of the equivalence. The existing kernel/cokernel reduction
lemmas also remain external dependencies. No data was selected from an arbitrary
unproved existence statement. The canonical kernel and cokernel constructions are
specified by their universal properties.

Edge checks: the finite-cover exponent is `max 1 (S.sup t)`, so it stays positive even
on an empty scheme. The cover-comparison lemma permits an empty index type only when
it covers the empty scheme. With K the zero ideal, both annihilation tests hold; with
K the unit ideal, both tests mean that the relevant formal objects or affine modules
vanish. Identity maps give zero kernels and cokernels on both sides. Doubling the
positive exponent in the termwise-to-limit implication agrees with Remark 0888.

## No longer needed

Removed seven unused direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`.
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.
- `Sheaf.RingTheory.AdicCompletionNoetherian`.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

The affine equivalence, local exactness and ideal-product facts remain in the proof
plans of the new geometric nodes; they are not claimed unnecessary project-wide.
The finite-type bridge and explicit completion-Noetherianness module are unnecessary
as direct dependencies of this proof. No whole-library module-pruning count is claimed:
the existing double-exponent modules can still reach some of the removed direct imports.
Every original public import remains unchanged.

Discarded the previous attempt's uncommitted
`CoherentFormalModuleAnnihilatedComponent` module and
`lem-weil-pbc-coherent-formal-module-annihilated-double-component` node: their assertion
is already the pair of the existing double-kernel and double-cokernel declarations.
They are absent from this delivery and are not needed by its proof.

## Where the brief, the DAG or earlier work was wrong

The saved report described a decomposition through a new component theorem, but the
saved item already used the existing kernel and cokernel component declarations.
The new component theorem was redundant, and the only remaining item hole was the
four-way equivalence. The previous dry-run rejection was therefore addressed by
completing that equivalence's implication assembly, rather than changing the already
complete double-exponent proof.

The current parent DAG proof described only pairing the double-exponent kernel and
cokernel results, omitting the main equivalence and the algebraic assertion. It now
records the actual implications, finite-cover argument and scalar-reduction application.
The blueprint unit's statement and realized steps are unchanged; all new work is below
that level. The second reader updated the main theorem's proof docstring and the double
exponent docstring to match the new DAG steps, replacing obsolete step references.

The cited Stacks TeX source is not installed in this read-only clone. The three source
places were read directly at https://stacks.math.columbia.edu/tag/0888,
https://stacks.math.columbia.edu/tag/087W and https://stacks.math.columbia.edu/tag/087X.
The source paths in the DAG remain the project's canonical paths. LeanSearch returned
an internal server error; it is recorded as unavailable, with actual successful
LeanFinder and Mathlib-source searches recorded alongside it.

The first main-file compile could not find cached object files for the two existing
double-exponent modules. No dependency module was copied or rewritten. A scratch check
against the cached parent double-exponent theorem verified the implication proof while
waiting. After the shared compiled library refreshed, the actual item compiled using
its declared kernel and cokernel imports. The scratch file is outside the delivered
Lean tree.

## New nodes

`lem-weil-pbc-formal-annihilation-affine-limit` is stated by
`AlgebraicGeometry.coherentFormalModule_annihilated_affine_limit` in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleAnnihilatedLimit.lean`.
It isolates the uniform termwise-to-affine-limit implication with explicit exponent
2t; its source is the final paragraph of Stacks Remark 0888.

`lem-weil-pbc-formal-annihilation-kernel-cokernel-cover` is stated by
`AlgebraicGeometry.coherentFormalModule_annihilated_formal_cover` in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleAnnihilatedFormalCover.lean`.
It isolates fixed-exponent annihilation detection for given limiting and colimiting
forks on an affine cover, using the affine description in Lemmas 087W and 087X.

No change record is required: no existing statement, definition or public import changed.

## Second reading by U4

1. Interface: PASS. Compared the item with the read-only repository using `diff` and
   extracted all three existing theorem signatures: each is byte-for-byte identical.
   Their visibility and the four original public imports are unchanged. There are no
   existing definitions edited, forced adaptations, or undeclared interface changes.
2. Proof and axioms: PASS as a decomposition. Compiled all three delivered modules with
   `lcompile.py --all`, without errors or warnings. The item has no remaining hole;
   the two new modules contain only the reported public named theorem holes, each
   with proof exactly `by sorry`. No forbidden declaration or hollow definition occurs.
   A scratch-copy `#print axioms` check of all five declarations shows only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from open dependencies. In particular
   neither the retained double-exponent theorem nor the algebraic theorem is claimed
   to be axiom-free. Selecting an Abelian structure selects proof data; canonical
   kernels and cokernels are determined by their universal properties.
3. Split statements: PASS. Independently read Stacks
   [Remark 0888](https://stacks.math.columbia.edu/tag/0888),
   [Lemma 087W](https://stacks.math.columbia.edu/tag/087W), and
   [Lemma 087X](https://stacks.math.columbia.edu/tag/087X).
   The affine-limit statement isolates just one implication at a fixed exponent;
   naturality of the scalar lifting formula justifies passage to the limit. The cover
   statement tests given universal forks at a fixed exponent, using separatedness
   of their completed modules, without assuming termwise kernels. Checked the empty
   scheme and empty cover, zero and unit ideals, identity and zero maps, and I equal
   to the unit ideal (all formal objects then vanish). The exponent max(1, S.sup t)
   remains positive. Both source-based docstrings and nodes match these arguments.
   Independent LeanFinder search for compatible scalar inverse maps, Loogle search
   `Module.annihilator, LinearMap.ker`, and Mathlib grep for kernel preservation,
   quotient annihilators and adic separatedness found ingredients but no duplicate.
   Also searched both library roots; the closed-immersion and push-pull annihilation
   statements have extra geometric hypotheses and cannot replace these criteria.
   Neither open geometric statement can be closed by a short existing application.
4. Route and pruning: PASS. Reviewed the five implications and the finite affine
   subcover argument. All remaining proof imports are used; new proof imports are
   private. The seven removed direct imports are listed above. Comparing the old and
   new parent `proof_deps`, no old dependency was removed: the original kernel,
   cokernel, abelianness and scalar-reduction dependencies all remain used. Several
   removed direct imports are needed by lower nodes, as the report already explains.
   No global module-pruning claim is made. Read `dag/units/sk-thm-p1.json`: its
   `realized` route remains unchanged, and this decomposition stays below unit level.
5. DAG: PASS. The parent changes only `proof`, `proof_deps`, and `proof_origin`,
   recording the five implications and both retained companion declarations.
   Each new node has the required source, self-contained statement, proof steps,
   dependencies, search records, creation and blueprint data, chapter/unit, and
   verbatim Lean signature. Its proof dependencies are the union of its step uses.

Changes by the second reader: corrected the main equivalence proof docstring to
list the five actual implications and explicitly identify the remaining decomposition;
corrected the double-exponent docstring's obsolete step references. No proof, statement,
definition, import, node or hole count needed repair. Added this independent review.
