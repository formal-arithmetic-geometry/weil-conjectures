## What changed

Replaced the sole remaining sorry in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity`, in
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant`,
with a complete Lean reduction. Its signature and all other declarations are unchanged.
Added the proof-only import `Sheaf.AlgebraicGeometry.Modules.ConstantRankComplexHomology`.

The proof chooses the existing finite-free complex and bases, selects nonvanishing maximal
minors of the two adjacent differentials, and intersects their basic opens with the open
constant-dimension fibre through the chosen point. The rank formula and two lower bounds
force both ranks to remain equal to their values at the point. It then applies the new
constant-rank homology lemma and transfers its conclusion through the existing base-change
and open-restriction isomorphisms. All this glue, including singleton images of lifted
residue-field points and the natural-number rank arithmetic, is proved in Lean.

Updated the proof route of `thm-pc-semicontinuity-base-change` and recorded the Grauert
declaration in its Lean declaration list. No target, definition, or existing statement changes.

## Proved and sorry left

Reduced the one original sorry:
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteLocallyFreeOfRank_higherDirectImage_of_isLocallyConstant`
(node `thm-pc-semicontinuity-base-change`). The item's module now contains no sorry.

One new sorry remains:
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_homology_pullback_of_constantRank`
(node `lem-pc-constant-rank-complex-homology`), in
`Sheaf.AlgebraicGeometry.Modules.ConstantRankComplexHomology`.
Its entire proof is `by sorry`, with the source and complete normal-form/kernel-image argument
in the docstring. It is an independent linear algebra statement about an arbitrary complex
and an open immersion: no proper morphism, higher direct image, flat sheaf, or locally
constant cohomology function occurs in its hypotheses. Thus this is strictly the remaining
normal-form step, rather than a renamed Grauert theorem.

Local compilation succeeded for both modules, with no warnings. The remaining imported
sorries in the finite-free model and open-restriction comparison are existing dependencies;
this delivery does not add them or claim to eliminate their axioms.

## No longer needed

None. No existing imports were removed. The original paper-level dependencies of the derived local-model argument remain in the
node: they support the unit route and the canonical-map clause not stated by this module.
The Lean reduction uses the existing finite-free-model API instead of importing the
separate Sheaf derived-category modules; they are not claimed as literal Lean imports. No unit statement or proof step is bypassed. The new proof
implements the locally constant rank argument using basic opens and arithmetic; it does
not need a separate theorem defining globally locally constant differential rank functions.

## Where the brief, the DAG or earlier work was wrong

The module has one remaining sorry, although its primary node's recorded declaration is
`upperSemicontinuous_hFiber`, which already has a proof. The Grauert declaration was in the
node's audit but missing from its main declaration list; the delivery records it there.
The reduced-ring normal-form step was marked elementary with no separate Lean declaration.
It is now a named generic remaining item; the rest of the argument is real Lean.

The finite-free complex model explicitly provides only nonempty isomorphisms, without
canonical-map compatibility. This suffices for the actual Grauert declaration in this
module, which asserts local freeness and rank only. This delivery does not claim that the
paper's separate canonical base-change-map clause has been formalized.

The blueprint source files are absent from this clone; their complete proof text is present
in the existing node and the unit record. The new lemma follows precisely the reduced-ring
normal-form claim in that text. LeanSearch returned an internal server error, recorded as
unavailable; Lean Finder, Loogle, and a Mathlib grep found no matching homology theorem.
The source library's Schur-complement lemmas provide matrix ingredients but no theorem
connecting them to local homology sheaves. Whole-DAG and library searches found no duplicate.

## New nodes

`lem-pc-constant-rank-complex-homology`: homology of a finite-free complex on a reduced
scheme, restricted to an open subscheme where both adjacent differential ranks are constant,
is finite locally free of the expected rank. The input ranks can be tested at one
field-valued point above each point; matrix rank is invariant under field extension.
Source: `thm-pc-semicontinuity-base-change`, proof (3), the normal-form claim and its
application to the kernel and image. Search records are included in the node.

Edge cases checked mathematically: an empty open gives a vacuous locally free condition;
zero adjacent ranks use the empty minor 1 and give the free middle term; homology rank zero
gives the zero module; q=0 still uses the differential from integer degree -1 (no natural
predecessor truncation); fields larger than the residue field preserve ranks. Reducedness
and an open immersion are essential: over dual numbers a differential multiplication by
epsilon has constant residue rank zero while its homology need not be free. No boundedness
assumption is needed because only three adjacent terms enter the argument.

No change records are required: no existing signature or definition was changed.

## Second reading by D2

1. **Interface: PASS.** Read both delivered modules in full and compared the item with
   the repository using `diff -u` and the delivery declaration parser. All seven existing
   declaration signatures are unchanged; the only existing body changed is the original
   Grauert sorry. There are no definition changes, new hypotheses, or weakened conclusions.
   The added constant-rank module import is proof-only. The two public imports in the new
   module supply objects occurring in its signature.

2. **Kernel and axioms: PASS as a reduction.** Recompiled both modules in import order,
   without errors or warnings. Inspected both files for forbidden declarations and hollow
   definitions. The item has no sorry; the only added sorry is the entire proof of the
   public constant-rank theorem named in the report and its node. Scratch `#print axioms`
   checks for that theorem and the Grauert declaration returned exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Thus the original obligation is reduced,
   not independently closed under the three permitted final axioms. Existing local-model
   and restriction-comparison dependencies also remain open.

3. **Split-off lemma: PASS.** Checked the signature against its node and docstring.
   After identifying the open subscheme with its image, affine charts inherit reducedness
   and the bases. A field-valued point factors through the residue field at its image,
   so its ranks detect residue ranks. Vanishing larger minors and invertible maximal
   minors give split image and kernel locally; restricting the image retraction to the
   kernel gives a finite projective homology quotient of the asserted rank. This is
   strictly the normal-form/homology step, not a restatement of Grauert. Empty opens,
   zero differentials, zero middle rank, maximal image rank, negative integer degrees,
   and extensions of residue fields cause no exception. In a nonempty open the complex
   identity forces a+b <= r(q); on an empty open any subtraction rank is vacuous.
   Repeated Lean Finder, Loogle, and Mathlib grep searches with different words
   (split kernels/images over reduced rings; projective homology), and searched the
   project's Lean and DAG. No existing theorem supplies this homology conclusion.
   Read the upstream Schur-complement lemmas: they supply matrix ingredients, but the
   sheaf/homology and local-projectivity bridge remains substantial and cannot be closed
   in a few minutes. The complete mathematical proof and source are present.

4. **Route and pruning: PASS, with a pre-existing bookkeeping gap.** Checked the
   nonvanishing-minor neighbourhoods, the open constant-dimension fibre, both rank lower
   bounds, the rank-sum arithmetic, and the composed base-change/restriction isomorphism.
   Every existing import still supplies signatures or the other existing proofs; none
   is removed. The unit's sole proof paragraph still passes through the finite-free
   local model, adjacent differential ranks, and the reduced-ring normal form. The node
   retains the paper-level dependencies for that route and its additional canonical-map
   clause; these are distinguished from the Lean API used in this delivery. The actual
   `dag/units/sk-thm-picard-semicon.json` has `realized.statement = []` and
   `realized.steps = [[]]` already on the base. No realized entry is removed or bypassed;
   the empty realization record is reported here, not silently treated as complete.
   The paper's canonical-map assertion remains outside the existing Grauert signature.

5. **DAG: PASS for the delivered reduction.** Checked the existing node's proof changes,
   proof-dependency union, source, and declaration list, and the new node's full statement,
   source, docstring tag, declaration signature, proof steps, dependency union, searches,
   creation record, chapter, unit, and blueprint provenance. The new lemma is called by
   the delivered Grauert proof with exactly the two ranks established there. The unchanged
   derived local-model and canonical-map parts of the node describe the paper route,
   rather than additional Lean results claimed closed by this delivery.

Second reading changed the report's inaccurate assertion that every retained paper-level
DAG dependency is used through existing Lean imports, documented the empty pre-existing
unit realization record, and added independent search evidence to the new node. No Lean
proof, statement, definition, or import needed repair.
