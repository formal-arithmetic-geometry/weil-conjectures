## What changed

Proved `TopCat.Sheaf.constantSubsheaf_lower_image_stalks` without changing its signature.
Added the proved module `Sheaf.Topology.ConstantSubsheafSelectedStalkRange`, whose theorem
`TopCat.Sheaf.constantSubsheaf_selected_stalk_range` computes the range for any selected
subfamily, without mono, epi, bounds, or attained-divisor hypotheses.

The selected-range proof constructs canonical constant-stalk coordinates, identifies unit germs
using the proved extension-by-zero stalk theorem, and uses the quotient by the generated subgroup
to prove range containment. Every endomorphism of the integers preserves each subgroup; applying
this to an automorphism and its inverse handles the arbitrary coordinates in the statement.
The canonical-stalk coordinates and integer-homomorphism vanishing use the existing
proved private helpers `constantSubsheaf_canonical_stalks` and
`constantSubsheaf_integer_hom_zero`, imported directly through
`import all Sheaf.Topology.ConstantSubsheafStalkBound`. Their proofs are not copied.

The upper proof applies this calculation to both the low and full presentations. The attained
divisor is itself a low label whenever any low label is active, so both subgroups have the same
generator there. Injectivity and equality of ranges give stalkwise surjectivity of the image
inclusion. Exactness gives the cokernel assertion. Empty low range and injectivity give zero
image stalks outside V. Both DAG nodes record this actual argument.

Compiled both modules together in dependency order. The proofs include the empty family, empty
space, no active labels, and b = 0. For the new range theorem, zero labels and an arbitrary
selection are allowed. No arbitrary object is chosen from an unproved existence statement.

## Proved and sorry left

Closed the one original hole:
`TopCat.Sheaf.constantSubsheaf_lower_image_stalks`
(node `lem-sc-constant-subsheaf-lower-image-stalks`).

Also proved `TopCat.Sheaf.constantSubsheaf_selected_stalk_range`
(new node `lem-sc-constant-subsheaf-selected-stalk-range`).

Holes closed: 1. Holes added: 0. Sorries remaining in either delivered module: none.
This is a proof, not a decomposition into unproved statements.

## No longer needed

Removed the direct proof import `Sheaf.Topology.PresheafModuleStalkFunctor`: the argument uses
Mathlib's abelian sheaf stalk functor directly, not the ring-presheaf module stalk construction.
The old direct proof dependency `def-weil-pbc-module-stalk` is not needed for this calculation.
The original statement-dependency list is retained unchanged.

The direct import `Sheaf.Topology.AbelianOpenExtensionByZeroStalks` moves to the new proved range
module. Its node `lem-sc-topological-extension-by-zero-stalks` is still needed transitively and
is not pruned. All existing public imports are retained. No other old planned modules or nodes
are bypassed. The original proof uses no integer gcd or cyclic-subgroup classification theorem:
the supplied attained-divisor hypothesis directly identifies the generator.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no statement was changed. The DAG's proposed general positive
gcd calculation is unnecessary here: the attained-divisor hypothesis already yields an active
minimal generator. Canonical-stalk coordinates were available as a proved private helper in
ConstantSubsheafStalkBound and is now imported and used directly without adding a hole.

Read the source at https://stacks.math.columbia.edu/tag/0A38, especially the attained-gcd and
filtration paragraphs. LeanSearch returned Internal Server Error and is recorded as unavailable.
LeanFinder, Loogle, grep and local rg searches were run. Blueprint searches for the stalk-image
calculation and for 0A38 found no matching imported blueprint node.

## New nodes

`lem-sc-constant-subsheaf-selected-stalk-range`, in
`dag/nodes/sec-curve-estimates/lem-sc-constant-subsheaf-selected-stalk-range.json`, records the
proved selected-presentation range calculation. Its module is
`lean/Sheaf/Topology/ConstantSubsheafSelectedStalkRange.lean`. This is strictly a part of the
original argument: it neither bounds a generator nor concludes any image or cokernel is zero,
and does not assume the original mono, epi, positivity or gcd hypotheses. It has no sorry.
The unit's realized statement and route are preserved. There are no change records because
no existing statement or definition was changed.

## Earlier second reading (a previous round; superseded)

1. **No accidental statement changes.** Compared both delivered modules with the repository versions. The existing target theorem signature is byte-for-byte unchanged; the added theorem is a separate, strictly more general selected-range calculation. No definitions were altered.

2. **Proof and compilation.** Compiled both modules together with `lcompile.py --all`; both compile without errors. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The proofs use only ordinary Mathlib/library results and the stated categorical hypotheses.

3. **New statement review.** The selected-stalk-range theorem is true in edge cases (empty index type, empty selected family, zero labels, and empty space) and has no unnecessary mono, epi, positivity, bound, or attained-divisor hypotheses. It is not duplicated elsewhere in `lean/` or Mathlib; searches recorded in `searches.jsonl` found no matching result.

4. **Shortest route and pruning.** The target proof uses the new selected-range theorem, image-factorization epimorphisms, exact stalk cokernels, and elementary subgroup calculations. The unused direct proof import `Sheaf.Topology.PresheafModuleStalkFunctor` and obsolete direct dependency were removed. The unit route remains realized through the extension-by-zero stalk theorem and the selected range node.

5. **DAG agreement.** The item and new node records match the declarations and proof steps. The new node has source, proof, dependencies, searches, and Lean record required by stage 3. No target or existing statement was weakened.

Changes made in this second reading: added this review section only; no Lean statements or definitions were changed.

Repair of reviewer X-e4e39, G1: replaced the connected-colimit import with
`import all Sheaf.Topology.ConstantSubsheafStalkBound`, deleted both duplicated local
proof terms, and changed the two canonical-stalk calls and the integer-zero call to
the existing private helpers `constantSubsheaf_canonical_stalks` and
`constantSubsheaf_integer_hom_zero`. These helpers are imported and used directly,
rather than copied. Updated the new node's `proof_origin.note` accordingly.

## Earlier second reading (a previous round; superseded)

1. Compared the original module by diff and checked the existing theorem signature
   byte for byte: identical. The original node changes only proof, proof_deps and
   proof_origin. The other module and node are new. No existing definition, visibility,
   public import or statement changes; no change record is needed. Verdict: pass.
2. Independently compiled both delivered modules with lcompile.py --all, then compiled
   scratch copies with #print axioms for both public theorems. Each reports exactly
   propext, Classical.choice and Quot.sound, without sorryAx. Neither delivered file
   contains sorry or a forbidden declaration. After the G1 repair, canonical stalk
   coordinates use the existing private helper imported from ConstantSubsheafStalkBound;
   its proof uses colimit and sheafification isomorphisms. Extension stalk coordinates have
   their germ equation, determining the map. No data comes from unproved existence.
   Verdict: pass.
3. There are no statements left split off with sorry. Read the entire proved selected
   range theorem: its quotient argument gives containment and the unit germs give the
   reverse inclusion. Arbitrary integer coordinates preserve the subgroup by applying
   the endomorphism calculation in both directions. Empty selections and n = 0 give
   closure(empty) = zero; zero labels give zero generators; an empty space is vacuous.
   For the original statement b = 0 makes V empty by positivity. Repeated local and
   upstream searches found no matching public result. Independent LeanFinder query
   "range coproduct homomorphism subgroup generated by component images integer sheaf
   stalk" found algebraic coproduct range formulas, not this sheaf calculation; Loogle
   AddMonoidHom.range found only general subgroup facts. Verdict: pass.
4. Checked imports against the statements and proof terms: all public imports provide
   signature vocabulary; the ConstantSubsheafStalkBound import all, quotient, extension
   stalk, zero-object and zmultiples imports are proof imports. The existing private
   canonical-stalk and integer-zero helpers are imported and used, not copied. The attained active divisor gives both
   low and full generators directly, avoiding a gcd-classification detour. The old
   direct dependencies def-weil-pbc-constant-sheaf,
   def-sc-abelian-open-extension-by-zero and
   lem-sc-topological-extension-by-zero-stalks remain used transitively through the
   selected range theorem; def-weil-pbc-module-stalk is the obsolete proof dependency.
   Only PresheafModuleStalkFunctor is removed from the import closure contributed by
   this proof; no claim is made that it is globally unreachable. Read the unit's
   realized record and its blueprint text: no unit statement or step is bypassed.
   Re-read https://stacks.math.columbia.edu/tag/0A38, including the attained gcd and
   filtration paragraphs. Verdict: pass.
5. Checked both Lean signature records against their module text after whitespace
   normalization; both match. Each proof_deps is exactly the union of its steps' uses.
   The original node records the actual range, attained-divisor, surjectivity and
   zero-stalk arguments. The new node includes its source, full proof, searches,
   provenance, blueprint, chapter, unit and Lean record. Verdict: pass.

Changes in this second reading: the original independent review and dependency/pruning
accounting above are retained, with the helper-reuse descriptions corrected for G1.
This repair imports and uses the existing private helpers instead of copied local
proof terms; it also updates the new node provenance. No statements or definitions
were changed. After the G1 repair, `lcompile.py --all` compiled both delivered
modules successfully (10.6 s and 12.2 s). Checked that both duplicated local proofs
are absent, the three calls use the existing private helpers, all Lean lines are
at most 100 characters, neither module contains sorry, and the original theorem
signature is byte-for-byte unchanged. Original holes
closed: TopCat.Sheaf.constantSubsheaf_lower_image_stalks (1 of 1). Holes added: none.


## Second reading by B2

1. **Interfaces: pass.** Independently diffed the original module against the repository.
   Its existing theorem signature is byte-for-byte identical. Existing public imports,
   definitions and visibility are unchanged. The existing node changes exactly `proof`,
   `proof_deps` and `proof_origin`; no undeclared interface change or change record is needed.
2. **Proof: pass.** Compiled both modules in dependency order through `lcompile.py --all`.
   Compiled separate temporary copies with `#print axioms` for each public theorem: both
   report exactly `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx`. No delivered
   Lean file contains sorry or forbidden declarations. Read the reused canonical-stalk and
   integer-zero helpers in ConstantSubsheafStalkBound: their proofs are closed constructions.
   The coordinate isomorphisms come from colimits and sheafification; no arbitrary data is
   chosen from an unproved existence theorem. Temporary axiom-check copies were removed.
3. **Intermediate statements: pass.** No unproved statement is split off. Read the complete
   selected-range proof, including the germ equation, quotient containment argument,
   generator witnesses and coordinate-change invariance. Empty selections and n = 0 yield
   the zero subgroup; zero labels contribute zero; empty spaces are vacuous. In the upper
   theorem b = 0 makes V empty by positivity. Independent LeanFinder search for images of
   direct-sum maps returned general algebraic coproduct results, and Loogle closure/range
   search returned free-group formulas; neither duplicates this sheaf calculation. The
   independent grep search and local library searches found no matching public theorem.
   The upstream finite-sum coproduct lemma would require additional finite-sum glue and
   does not replace the germ calculation; the existing quotient argument is retained.
4. **Route and pruning: pass.** The attained active divisor supplies the generator directly;
   no subgroup-classification detour is needed. All proof-only imports are non-public.
   Existing private helpers are imported and called rather than duplicated. Checked all
   four original proof dependencies: constant sheaf, extension by zero and extension stalks
   remain used through the new range module; only def-weil-pbc-module-stalk is obsolete as
   a proof dependency. PresheafModuleStalkFunctor is removed as a direct import, without
   asserting that it becomes globally unreachable. The unit record realizes
   thm-sc-proper-cohomology and has no realized proof steps; neither is changed or bypassed.
   Its full statement was read from dag/units/sk-thm-curveestimate.json; the source blueprint
   text is absent locally. Independently read Stacks 0A38 at
   https://stacks.math.columbia.edu/tag/0A38, including its attained-gcd and filtration steps.
5. **DAG: pass.** Both Lean signature records match their declarations after whitespace
   normalization. Each proof_deps is exactly the union of the proof steps' uses. The
   original node records the selected/full ranges, attained divisor, cokernel and zero
   image-stalk arguments. The new node has source, proof, searches, creation provenance,
   blueprint, chapter, unit and Lean record, and accurately records direct helper reuse.

Changes made in this reading: appended this independent review and new search evidence only.
No Lean proof, statement, definition or node needed repair. Closed hole:
TopCat.Sheaf.constantSubsheaf_lower_image_stalks (1 of 1). Added holes: none.
The additional TopCat.Sheaf.constantSubsheaf_selected_stalk_range theorem is fully proved.
