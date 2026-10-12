## What changed

The existing declaration `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_module_acyclic`
is proved by induction on degree, generalizing over all module sheaves. The successor case
uses a right exact ladder from an injective embedding and Mathlib's
`AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact`. The degree-zero theorem
is proved using the existing canonical degree-zero pullback formula and the new underlying
sections compatibility obligation. This is a reduction, conditional on the two named
obligations below; it is not an axiom-free closure of the comparison theorem.

The existing signature and docstring are unchanged. The original public import remains.
All three new imports in the item are proof-only (`import`, not `public import`).
Every new declaration is in its own module. New intermediate statements do not require
primality. The base case does not assume positive-degree acyclicity, and the effacement
ladder does not assume the global sections comparison or any cohomology comparison.
No existing statement or definition was changed, so no change record is required.

## Proved and sorry left

Proved: `AlgebraicGeometry.Etale.bijective_cohomologyMap_of_module_acyclic` (the only original
sorry: 1 of 1), and the new
`AlgebraicGeometry.Etale.bijective_cohomologyMap_of_module_acyclic_zero`
(node `new-module-acyclic-comparison-zero`).

Exactly two named theorem sorries remain in new modules:

- `AlgebraicGeometry.Etale.bijective_underlying_globalSectionsUpperStarMap`:
  `Sheaf.AlgebraicGeometry.ModuleAcyclicUnderlyingSections`,
  node `new-module-acyclic-underlying-sections`.
- `AlgebraicGeometry.Etale.exists_module_acyclic_effacement_ladder`:
  `Sheaf.AlgebraicGeometry.ModuleAcyclicEffacementLadder`,
  node `new-module-acyclic-effacement-ladder`.

Both are whole proofs `:= by sorry`, with complete natural-language constructions in their
docstrings and matching independent DAG nodes. Local compilation of all four delivered
modules succeeds without errors or non-sorry warnings. Scratch `#print axioms` for all four
declarations reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` (as
applicable). The main and degree-zero proofs depend on the documented open obligations.

## No longer needed

`lemma-weil-pbc-leray-acyclicity` is no longer needed by this comparison route: induction
uses only the first step of an injective resolution and the long exact cohomology ladder.
No original import was removed, and no claim is made that this node is globally unreachable.

For completeness, the other old direct proof dependencies replaced in the item's node are
`lem-weil-pbc-module-sheaves-enough-injectives`, `def-sp-injective-resolutions`,
`lem-weil-pbc-injective-module-abelian-acyclic`, and `prop-weil-pbc-inverse-image-exact`.
They are retained in the proof dependencies of `new-module-acyclic-effacement-ladder`,
so they are not globally pruned. `def-weil-pbc-cohomology-pullback` remains a direct dependency.
The old proposed positive-degree helper and its node were removed from the sandbox;
they were never in the repository.

## Where the brief, the DAG or earlier work was wrong

The earlier submission only divided the original theorem into degree-zero and positive
restrictions, leaving both unproved. Worse, both new nodes cited the original theorem as
a proof dependency, creating a circular route if the item's node were updated to use them.
The original item's proof node was not updated. The split docstrings said the resolution
comparison was postponed, rather than supplying complete arguments.

The repair gives a genuine dimension-shifting reduction. It avoids the full acyclic
resolution comparison without bypassing any unit statement or realized unit step.
The existing mathematical docstring remains a valid alternative resolution proof; the
node's updated proof and the Lean body record the shorter induction actually delivered.

## New nodes

`new-module-acyclic-underlying-sections`: underlying abelian section restriction is
bijective when the module restriction for that same sheaf is an isomorphism. This isolates
coefficient forgetting, inverse image and the adjunction-unit compatibility; it says nothing
about positive cohomology.

`new-module-acyclic-comparison-zero`: the degree-zero comparison, with no acyclicity
hypothesis. It is proved by conjugating the preceding section bijection with the canonical
H-zero/sections equivalences and applying the existing pullback formula.

`new-module-acyclic-effacement-ladder`: an injective embedding and its cokernel supply
right exact rows and a commuting boundary square. It supplies no bijectivity assertion,
and does not use the section-isomorphism hypothesis or the parent theorem. Its word proof
includes the constant-ring/module-valued sheaf equivalence, exact forgetting, exact inverse
image, source and target injective acyclicity, and naturality of canonical boundaries.

Mathlib searches were performed afresh via msearch: LeanFinder, Loogle and grep succeeded;
LeanSearch returned an internal-server error and is recorded as unavailable, without a
claimed negative result. Searches found the right exact five lemma used in Lean and
sheafification/forgetful primitives, but no existing theorem giving either split obligation.
Repository searches also found the degree-zero pullback formula used in the new base proof
and the existing abelian pullback long exact ladder used in the effacement node's word proof.

## Second reading by F1

1. Compared the original module with the repository using diff and a byte comparison of
   the theorem signature. Verdict: the existing signature is byte-for-byte identical;
   existing definitions, target statements and public imports did not change. The sibling
   modules and declarations are new and have matching nodes.
2. Compiled every module locally in import order and checked all four declarations using
   scratch `#print axioms`. Verdict: no error; precisely the two listed named theorem
   sorries; no forbidden declaration, hollow definition, or nonstandard axiom beyond the
   permitted open `sorryAx` dependency.
3. Read the split statements and complete docstring constructions and searched with
   different terms from the earlier submission. Tested q=0 in the ladder (only H-one of
   the injective is needed), M=0, identity pullback, and r=0/1 in the now stronger helper
   statements. Verdict: the statements are true; neither restates comparison in all
   positive degrees, and neither assumes the desired conclusion. Constant-ring modules
   and the module-valued sheaf encoding are related by an equivalence, not by asserting
   that the underlying abelian sheaf is injective. The existing degree-zero formula and
   Mathlib right exact five lemma are reused.
4. Checked the proof from the top and all imports. Verdict: the main proof uses the
   shortest available induction step; all new imports are proof-only where appropriate.
   The complete old dependency disposition is listed above. The unit
   `dag/units/sk-thm-p1.json` realized statement and steps are untouched; this comparison
   lemma is below the unit level, and only its implementation route changed.
5. Read every delivered node against its declaration and the induction. Verdict: signatures
   match; the main node now records the actual degree-zero/induction proof; each new node
   has its source, steps, exact union of proof dependencies, search evidence, provenance,
   chapter/unit and Lean record. No new node depends on the parent theorem as a proof
   premise, so the previous circularity is removed.

Second reading changed: removed the positive-degree restatement; proved the degree-zero
case; extracted the underlying-sections obligation; replaced the case split by induction
through an injective-effacement right exact ladder and Mathlib's lemma; strengthened all
new helpers by removing unnecessary primality assumptions; repaired nodes, searches,
docstrings, proof-only imports, and pruning/report metadata.
