## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes` with a complete
Lean proof from two strictly separate intermediate results. The existing theorem's
signature, visibility and docstring are unchanged. Its only added import is the
proof-only import of `PicardExternalCupLeftCechComparison`.

`PicardExternalCupLeftCechExact` constructs actual finite affine open families, the
scalar Cech functor, integer tensor-total functor and product-cover Cech functor.
Every definition has concrete data. Their zero-morphism preservation is proved.
The tensor functor extends both factor complexes from natural to integer degrees
before totalizing; negative total terms are proved zero in the assigned module.

`PicardExternalCupLeftCechComparison` states a natural transformation on the entire
left coefficient category and its homology comparison for a single quasi-coherent
coefficient and any normalized scalar-model map. It assumes no exact sequence.
The separate exactness theorem asserts only exactness of the two specified Cech
sequences, with no cup transformation or homology comparison.

The assigned proof obtains three normalized maps using the existing
`picardExternalCupCochain_exists`, obtains exactness independently, and constructs
`A`, `B` and `phi` by `S.map` and `S.mapNatTrans`. Three applications of the
single-coefficient comparison provide the six isomorphisms and all three equations.
The negative-term condition is proved directly: extension by zero has no negative
index, and every tensor-total summand in a negative degree has a zero factor.

The original node's proof, proof_deps and proof_origin now describe this Lean
argument. No existing definition, statement, visibility or public import changes.
The declaration-local unused-variable linter option suppresses warnings for the
existing existential proof binders hA and hB, without changing those binders.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_comparison_complexes`
(node `lem-sc-picard-external-cup-left-comparison-complexes`). Its proof is complete,
but this is a decomposition, not an unconditional proof: it uses the following two
new public theorems, each with exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_exact`
  (node `lem-sc-picard-external-cup-left-cech-exact`). It covers termwise exactness
  of explicitly specified complexes, without comparison maps.
- `AlgebraicGeometry.Scheme.Modules.picardExternalCup_left_cech_comparison`
  (node `lem-sc-picard-external-cup-left-cech-comparison`). It covers natural Cech
  cup and its single-coefficient homology transport, without exact sequences.

There are no sorries left in the assigned module, no private sorries, no holes in
any definitions, and no other holes added. One upper hole closed, two lower holes
added; the net hole count of this decomposition is minus one.

The private negative-extension and negative-tensor lemmas, two private
zero-morphism instances and two public zero-morphism instances are proved.
All three modules compiled together in import order without warnings through
`lcompile.py --all`.

## No longer needed

No original imports removed and no original dependency modules pruned.
The original lower geometric dependencies remain needed by the two new lemmas;
they have been distributed to their appropriate proof plans, not discarded.
The assigned node now directly needs only the existing normalized-cochain node
and the two new nodes. Its former geometric dependencies remain transitive.
No invertibility assertion, cohomological bound, connecting-map square or
five-lemma theorem is used or introduced.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly describes the mathematics. Its lower statements
provide affine sections, refinement, cup and comparison ingredients, but do not
assemble either the short exact Cech sequences or the natural scalar comparison.
The new modules state those missing assemblages separately and the assigned
module combines them with actual functorial Lean constructions.

Mathlib's signed tensor-total shape is supplied for integer cochain indices, so
both natural Cech factors are extended first. This agrees with natural
first-quadrant totalization; negative terms are checked by summand inclusions.

The local checkout does not contain `literature/stacks-project/varieties.tex`.
Read the cited proof online at https://stacks.math.columbia.edu/tag/0BED and the
cup compatibility at https://stacks.math.columbia.edu/tag/0FKV. The exactness and
naturality portions are precisely the diagram after equation-kunneth-on-cech;
the scalar-model bookkeeping is an agent-written expansion of that argument.

Checked the new statements against zero coefficients, empty schemes/covers,
natural degree zero, and negative degrees. Empty tuple products are zero objects;
field tensor preserves the zero/exact sequences. In degree zero the unique
nonzero tensor index is (0,0). The transformation is natural on all coefficients;
comparison isomorphisms are asserted only for quasi-coherent coefficients. Neither
lemma assumes a geometric Kunneth isomorphism. The unit record's realized lists
are empty; its cube-theorem route has not been bypassed or changed.

Searches: LeanSearch was unavailable (HTTP 500), recorded as unavailable.
LeanFinder found Mayer-Vietoris short complexes for exactness and generic tensor
inclusions/Dold-Kan maps for comparison, none giving these results. Logged grep
queries gave no matching Mathlib declaration. Repository searches and the whole
blueprint searches found no existing node stating either separated result.

## New nodes

`lem-sc-picard-external-cup-left-cech-exact`, in
`dag/nodes/sec-abelian-varieties/`, records both concrete Cech functors and their
short exactness. Its proof plan retains the original affine section/tensor
arguments, and its docstring supplies the complete argument and edge cases.

`lem-sc-picard-external-cup-left-cech-comparison`, in the same directory, records
natural cup and its scalar-model homology comparison for one coefficient. Its
proof plan retains refinement/cup compatibility, affine comparisons and tensor
Kunneth. The theorem quantifies over any normalized map, so the original theorem
can apply it to the three maps supplied by the existing existence result.

No change records or forced adaptations are needed: all existing signatures and
interfaces are preserved, and both additional modules are new.

## Second reading by U3

1. **Diff and interfaces.** Compared the delivered item module with the repository version. The target theorem signature, existing declarations, visibility, and definitions are byte-for-byte unchanged; only its proof and a proof-only import were added. The two auxiliary modules are new modules recorded by new DAG nodes.

2. **Compilation and proof audit.** Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds without warnings. The assigned theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The two split-off auxiliary theorems are the only remaining `sorry`s, each public, named, documented with its source and complete proof plan, and matched by a DAG node.

3. **Statements and split nodes.** Read both auxiliary statements against their Lean declarations and edge cases (zero coefficients, empty covers, degree zero, and negative degrees). They are true, strictly simpler than the original theorem, and do not restate it: one isolates exactness and the other isolates natural Cech comparison. Repository and Mathlib searches found no duplicate declarations.

4. **Pruning and route.** The proof uses the existing normalized-cochain result plus the two split nodes. No prior import or proof dependency can be removed without bypassing the unit route; the unit's realized route is unchanged. The added import in the item is proof-only.

5. **DAG agreement and delivery metadata.** The item node and both new nodes agree with the declarations, proof dependencies, sources, and `split` status. The report records one upper hole closed and two strictly simpler lower holes added, with no hollow definitions.

I changed only this report section after the first delivery dry run; no Lean statements or proofs were altered.
