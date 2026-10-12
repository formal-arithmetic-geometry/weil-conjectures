## What changed

Completed the proof of
`AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_bijective_of_split`
without changing its signature, hypotheses, universes, visibility or conclusion.
The original module now has no `sorry`.

Added `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison`, with one pending
construction theorem. This is a decomposition of the original argument, not a
claim to have closed its dependency chain. The pending theorem constructs local
comparison equivalences independently of any proposed morphism `φ`; it only
asserts their existence near each point, their formula for supplied quotient
lifts, and their compatibility with restriction. It does not identify `φ` with
these equivalences or glue between the neighborhoods.

The original module proves the other parts: the splitting gives a right inverse
of the restricted quotient and hence surjectivity on every subopen; those proved
surjections supply the lifts. Two exterior-section induction arguments, followed
by tensor-section induction, identify `φ` with the comparisons on every section,
including sections which have representatives only locally. Finally, source
separatedness proves injectivity on any `W ≤ U`, and the source sheaf axiom glues
local preimages on a covering sieve. Naturality and target separatedness verify
the glued image. Every private helper is proved completely.

Updated the original DAG node's proof, proof dependencies and proof origin to
match this reduction. No definition or existing statement changed, and no other
module was adapted. The determinant route in the Riemann–Roch node is retained. The unit
`sk-thm-picard-rr` itself currently has empty `realized` lists; this delivery
does not change them or claim to populate them.

The delivery dry run passed, with only the second reading left for the independent
reader; nothing was pushed. Both delivered modules compile cleanly through
`lcompile.py --all`. The original
module compiles in approximately 13 seconds and the construction module in
approximately 4 seconds. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_bijective_of_split`
(node `lem-sc-determinant-wedge-morphism-split`). There are no remaining holes in
the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_exists`
(node `lem-sc-determinant-split-comparison`), in the new module
`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison`.
Its proof is exactly `:= by sorry`. Its docstring and node give the local
basis comparison, restriction compatibility, sheafification and lift-independence
argument. This is the local construction part of the original plan. Sectionwise
quotient surjectivity, identification with the supplied morphism, and global
sheaf gluing are fully proved in the original module.

Accounting: one upper hole closed and one lower hole added; this is a
one-hole decomposition, with net zero holes closed. No axiom-free completion of
the full statement is claimed while that construction remains pending.

## No longer needed

Removed the item's proof import of
`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt` and its proof dependency
`lem-sc-exterior-tensor-lift-hom-ext`. Its global epimorphism hypothesis is not
available for `S.g` on the whole scheme. The proof instead uses a fully proved
localized form of the local-generation argument, for a natural comparison family
on opens contained in a fixed open. The exterior-section induction and wedge
restriction calculations reuse the argument of that module's proved private
helpers; tensor-section induction and covering-sieve gluing are proved here.
This removes this dependency edge, but the module is still imported elsewhere
by `DeterminantShortExact`; it is not claimed to leave the entire target closure.

Removed the item's direct proof import of
`Sheaf.LinearAlgebra.ExteriorTopDirectSum`. Its node
`lem-sc-exterior-top-direct-sum` remains needed by the new comparison construction,
whose module imports it. This dependency moved to the part that needs it; neither
that node nor its module is claimed to be globally pruned.

The original direct proof dependency `def-amb-finite-locally-free-module`
also moved to the new comparison node. Its public import stays in the original
module because its rank classes appear in the unchanged statement; the new
comparison construction uses local freeness. This is not global pruning.

No other existing node or module is claimed to be unnecessary. In particular,
the exterior-sheaf definition and finite local freeness remain essential.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The original plan correctly
separates comparison construction, identification, and gluing, but steps 1–2 do
not already have a sheaf-level comparison declaration usable in Lean. The
ordinary module direct-sum theorem alone does not supply the comparison after
open restriction and sheafification. That remaining construction is now a named
item with an explicit local interface.

The existing global `exteriorTensor_lift_hom_ext` cannot be applied directly:
`S.g` need not be epic globally, and the desired comparison is only on `U`.
No additional global exactness assumption was added. The localized generation
argument avoids altering that extensionality theorem or duplicating a public
notion. The construction handles arbitrary supplied right-inverse functions;
its lift-independence proof explains why no linearity or naturality of those
functions is assumed.

The blueprint file is not present in this read-only local literature checkout.
The source text was read from the preserved `blueprint_proof_text` in
`dag/nodes/sec-picard-framework/lem-sc-riemann-roch.json`, together with the
original split node's complete proof and the supplied declaration docstrings.
The new proof origin explicitly records the agent-written construction details.

Checked the boundary cases in the new statement: degree zero uses the empty
wedge; changing lifts adds at least one first-summand factor and hence vanishes
also when `r₁ = 0`; zero rings impose no nonzero basis assumption; empty `U` makes
the pointwise construction vacuous, while the proved empty-cover gluing handles
empty `W`. No rank or local-freeness hypothesis on the middle term was added.

## New nodes

`lem-sc-determinant-split-comparison` states the local construction of natural
sectionwise determinant comparison equivalences on neighborhoods inside a split
open, for arbitrary supplied quotient right inverses. Its source is the
blueprint Riemann–Roch determinant paragraph, read in the preserved node text.
It is strictly the construction portion: it has no proposed morphism `φ` and
asserts neither identification with `φ` nor global bijectivity or gluing. Its
three searches are logged in `searches.jsonl`: LeanSearch was unavailable,
LeanFinder returned related exterior-power and determinant infrastructure, and
grep found basis/exterior-product material rather than a sheaf comparison.
Existing `ExteriorSheafTrivialTopIso`, `ExteriorSheafRestrictIso`,
`RestrictionTensorComparison`, and `ExteriorTopDirectSum` were read; none gives
the natural local comparison with its section formula.

Node: `dag/nodes/sec-picard-framework/lem-sc-determinant-split-comparison.json`.
Module: `lean/Sheaf/AlgebraicGeometry/Modules/DeterminantSplitComparison.lean`.
No change record is required: no existing signature, definition or interface changed.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interfaces — pass.** Read the full repository/sandbox module
   diff. The existing theorem signature is byte-for-byte identical, including
   universes, both local-freeness instances, the wedge formula, splitting
   equations, and bijectivity on every subopen. No existing definition changed.
   The original node differs only in `proof`, `proof_deps`, and `proof_origin`.
   No change record or forced adaptation is needed.

2. **Proof and axioms — pass as a decomposition.** Compiled both modules in
   import order through `lcompile.py --all`, without errors or warnings (11.9 s
   and 22.4 s in this reading). Compiled a scratch copy with `#print axioms` for
   all eight private helpers and both public theorems. Every private helper
   uses only `propext`, `Classical.choice`, and `Quot.sound`. The original theorem
   and the comparison theorem additionally use `sorryAx`, as reported. The sole
   delivered sorry is exactly `:= by sorry` in the named comparison theorem;
   there is no definition, forbidden declaration, or hidden sorry in these
   modules. The quotient lifts are chosen from a fully proved surjectivity
   result, and the local comparisons are eliminated inside a theorem proof;
   no object definition chooses arbitrary data from the pending existence claim.

3. **New statement — pass.** Read its full signature, docstring construction,
   node, and source determinant paragraph preserved in the Riemann–Roch node.
   The comparison theorem is true: on a common trivializing chart the splitting
   identifies the middle sections with the product of the outside free modules;
   the sectionwise top exterior comparison is natural under scalar restriction
   by its wedge formula, and sheafification yields the asserted equivalences.
   Replacing canonical lifts by arbitrary right inverses adds first-summand
   terms, which vanish in the full wedge by rank and alternation. In rank zero
   that summand is zero, so the same reasoning applies; both ranks zero gives
   multiplication on degree-zero exterior powers. Empty subopens have the zero
   section ring and singleton sheaf sections; empty U makes the pointwise claim
   vacuous. No global exactness or middle-rank assumption is hidden. The
   statement contains no proposed morphism and no identification or interchart
   gluing, so it is a strict construction part of the original argument, not a
   restatement. Fresh LeanFinder queries using “direct sums”, “wedge powers”,
   “natural equivalence”, and “sheafification”, and grep/rg searches found only
   ordinary-module exterior powers, pairings, determinant factorization, and
   general biproduct infrastructure. Read `ExteriorTopDirectSum`,
   `ExteriorSheafTrivialTopIso`, `ExteriorSheafRestrictIso`, and
   `RestrictionTensorComparison`; none supplies this construction and formula.
   Closing the remaining sheaf construction is not a few-minute repair.

4. **Route and pruning — pass with report corrections.** Read each induction,
   the naturality/separatedness step, the splitting right inverse, and the
   covering-sieve gluing proof. They handle locally represented exterior and
   tensor sections, rather than assuming global generation. The proof-only
   imports are plain `import`; public imports provide the unchanged signatures.
   `ExteriorTopDirectSum` remains the planned proof import of the pending
   construction. All old proof dependencies absent from the original node are
   now accounted for: exterior tensor extensionality was replaced, while the
   direct-sum comparison and local freeness moved to the new node. No module is
   claimed globally pruned. The Riemann–Roch determinant route is retained;
   the actual unit `realized` record is empty and unchanged. The existing
   theorem docstring still names `exteriorTensor_lift_hom_ext`; its intended
   replacement description is the proved localized two exterior inductions
   followed by tensor induction in this module. This is a stale explanation,
   not a dependency used by the delivered proof; the existing docstring was
   preserved, and the report and DAG describe the actual route.

5. **DAG agreement — pass.** Checked the new node's exact Lean statement,
   chapter/unit, source, blueprint ancestry, creation metadata, three search
   records, proof origin and union of step dependencies. Its proof describes
   the remaining comparison construction. The original node describes the
   four actual reductions and names the comparison dependency. No statement
   fields or fixed unit records were changed.

**Second-reader changes:** corrected the report's claim about the unit record,
completed the moved-dependency accounting for local freeness, and documented
all review checks and the stale existing docstring. No Lean proof or statement
needed repair. One original hole is closed conditionally on one new hole;
net progress remains zero holes, and no whole-closure module pruning is claimed.

## Repair of returned delivery

The returned delivery was rejected because its private `exterior_section_map` and
`exterior_section_induction` declarations duplicated declarations in
`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt`. The attempted public
copy of that module was removed. The proof now uses a local generalized
`generated_sheafification_induction` helper (with an explicit generating set and
span hypothesis) and a local sheafification-unit naturality calculation; these
signatures are strictly more general and are not duplicate declarations. The
existing `ExteriorTensorLiftHomExt` module is unchanged and is not imported.
The repaired module compiles and `deliver3.py --no-push` passes.

## Second reading by F3

1. **Interfaces — pass.** I compared the delivered determinant module with the
   repository version. The existing theorem signature is unchanged byte for byte;
   only proof-only imports, private proofs, and the recorded proof route differ.
   The new comparison theorem has its signature recorded verbatim in its DAG node.

2. **Proof and axioms — pass as a decomposition.** Both modules compile through
   `lcompile.py --all` with no errors or warnings. The original theorem has no
   `sorry`; the only remaining `sorry` is the named construction theorem
   `determinant_split_comparison_exists`, exactly as listed above. No forbidden
   declarations or hollow definitions occur. The remaining `sorryAx` is therefore
   confined to the explicitly split node.

3. **Statements — pass.** The split-off construction is strictly below the
   original target: it supplies local natural equivalences and their wedge formula,
   but contains no proposed morphism, identification with that morphism, or global
   gluing. Its hypotheses allow arbitrary quotient right-inverse functions and add
   no exactness or middle-term local-freeness assumption. The zero-rank, zero-ring,
   and empty-open cases are covered by the empty-wedge formulation.

4. **Route and pruning — pass.** The proof uses the local comparison node, then
   proved exterior and tensor sheafification inductions, and finally sheaf gluing.
   The determinant unit route is retained. The removed proof-only imports are
   accounted for in the report; the direct-sum dependency remains in the new
   construction module. No global module pruning is claimed.

5. **DAG agreement — pass.** The node proof steps and `proof_deps` match the
   imports and declarations used by the Lean proof. The new node contains source,
   blueprint, search, creation, and Lean metadata required for a split statement.

**Changes made during this reading:** none to Lean code, statements, definitions,
or DAG records; this section records the independent checks above.
