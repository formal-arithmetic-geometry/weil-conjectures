## What changed

Both original theorems retain their signatures and now have complete Lean proofs.
`exists_mono_biproduct_of_constructible_stalk_detection` uses the new proof-only
import `Sheaf.AlgebraicGeometry.ConstructibleFiniteStalkTests`. It obtains finitely
many finite source stalks, forms the finite dependent sum of their nonzero elements,
chooses a detecting index for each element, and takes the finite image of that
choice. A zero image under the biproduct lift would give a zero image under the
selected component by `biproduct.lift_π`, functoriality, and preservation of zero.
This proves injectivity at the testing points and hence monicity.

`exists_mono_biproduct_of_constructible_stalk_injective` applies the detection
theorem: injectivity and preservation of zero imply detection of nonzero elements.

The geometric testing portion of the existing plan is isolated in one new module,
with its source, complete proof in words, and a matching DAG node. It states a
property of the source alone, independent of any family of maps; it does not assert
finite selection of components or a biproduct embedding. The original node's proof
and dependencies now reflect the Lean reduction. No definitions or existing
statements changed. The unit's partition/generic-kernel route is retained.

## Proved and sorry left

Proved, in the original module:

- `AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_stalk_detection`.
- `AlgebraicGeometry.Scheme.exists_mono_biproduct_of_constructible_stalk_injective`.

The only `sorry` in the delivery is
`AlgebraicGeometry.Scheme.exists_finite_stalk_tests_of_constructible`, in
`Sheaf.AlgebraicGeometry.ConstructibleFiniteStalkTests`, node
`lem-weil-pbc-constructible-finite-stalk-tests`.
Both modules compile locally without warnings. The final dry run performs the
server compile and preflight. These proofs still depend on that named open lemma.

Edge cases: the chosen dependent sum and its image may be empty. When all tested
stalks are zero, the injectivity argument is vacuous and the testing criterion
still applies. Empty X admits an empty set of testing points. Empty L forces each
nonzero tested stalk element to contradict the detection hypothesis, so the same
construction works. The target sheaves have no finiteness assumption, and the
index universe remains arbitrary.

## No longer needed

Removed direct proof-only imports from the original module:

- `Sheaf.AlgebraicGeometry.IrreducibleLisseStrata`.
- `Sheaf.AlgebraicGeometry.LisseGenericKernel`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.

These are retained through the finite-stalk-testing module; no nodes or modules
are pruned from the target closure. The four original geometric dependencies
(`lem-weil-pbc-irreducible-lisse-strata`, `lem-weil-pbc-lisse-generic-kernel`,
`prop-weil-pbc-geometric-stalks-exact`, and
`lemma-weil-pbc-geometric-stalk-conservative`) remain necessary through the new
finite-stalk-testing node. They were not pruned or restated.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The finite-stalk-testing node makes explicit two
pieces of glue implicit in the original plan: the natural inverse-image stalk
isomorphism (`lemma-openclosed-stalk-upperstar`, already Lean-closed) and the
inverse-image/forget comparison
(`lem-weil-pbc-etale-inverse-image-algebraic-structures`). The latter is used as a
generic tool to identify the underlying sheaf of the abelian restriction with the
set restriction supplied by stratification; it does not replace the unit route.
Factoring a geometric point through a stratum is justified via residue-field
isomorphisms for immersions, rather than merely by containment of its image.

The cited Stacks text is not populated in this clone. Read the official page
https://stacks.math.columbia.edu/tag/09Z6 and checked its parenthetical partition
alternative. The new node's source is the existing blueprint proof's steps 1, 3
and 4, made precise with the stated comparison lemmas. Its proof origin is marked
as an agent adaptation.

## New nodes

`lem-weil-pbc-constructible-finite-stalk-tests` states the finite geometric testing
portion of the partition argument, without the finite choice of family indices.
Its declaration is in
`lean/Sheaf/AlgebraicGeometry/ConstructibleFiniteStalkTests.lean`; its node is in
`dag/nodes/sec-smooth-purity/lem-weil-pbc-constructible-finite-stalk-tests.json`.
The named geometric dependencies are retained, and the two comparison tools are
explicitly recorded. Searches of the whole blueprint (`finite stalk`, `stalk
tests`) and library found no existing declaration of this criterion. LeanFinder
returned finite-type sheaf/local-generator statements, not this criterion;
Loogle did not recognize the source-library geometric-point identifier;
LeanSearch returned an Internal Server Error (recorded as unavailable); a Mathlib
source grep found no finite stalk testing criterion. No change records were needed.


## Second reading by T1

1. Compared the delivered original module with the repository using `diff` and
   checked each theorem header through `:=` byte for byte: both are unchanged.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   No definition, target statement, or public import of the original module changed.
   Verdict: pass; no change record is needed.

2. Compiled both modules in import order with `lcompile.py --all`: no errors or
   warnings. Reviewed the dependent sum, finite image, component projection, and
   zero-kernel injectivity argument, and the corollary's preservation-of-zero step.
   Scanned the delivered Lean files: the only `sorry` is the named testing theorem,
   with no forbidden declarations and no definitions containing `sorry`.
   Scratch copies with `#print axioms` for all three declarations show exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Verdict: pass as a partial proof; neither original theorem is axiom-closed yet.

3. Read the new statement, its full docstring, its node, and the declarations of
   its geometric dependencies. Its finite tests depend only on F and are generic
   points of finite irreducible lisse strata. Residue-field isomorphisms lift the
   geometric points; naturality identifies restricted maps; the inverse-image/
   forget comparison supplies the needed set local constancy and finite stalks.
   Generic-kernel detection on every stratum, followed by exactness and
   conservativity, proves the criterion. Checked empty X, zero source, singleton
   stratum, empty index family, and arbitrary targets. The criterion is a genuine
   geometric portion of the argument, not the original finite-selection statement
   renamed. New searches used fibre-functor/conservativity language: LeanFinder
   returned scheme-map injectivity results, Loogle did not recognize `Sheaf`, and
   Mathlib grep found joint faithfulness of all points but no finite testing result.
   Repository searches likewise found no duplicate. Verdict: pass. Closing the
   remaining lemma requires formalizing the stratum factorization and comparison
   argument; it is not a short tactic repair.

4. The proved finite choice and biproduct argument uses the direct finite testing
   reduction. No shorter existing result was found. Read the Stacks 09Z6 partition
   alternative and checked `dag/units/sk-prop-sf-cbc.json`: its `realized.statement`
   and `realized.steps` are empty, and no recorded unit realization is bypassed.
   The partition/generic-kernel route is retained. Corrected the removed-import
   list above. Added four plain imports to the still-open testing module for its
   planned stratification, generic-kernel, inverse-image/forget, and stalk
   comparison dependencies, so the queue's import closure retains that work.
   Its public imports are needed by its statement (`algClosurePoint` in particular).
   Verdict: pass; no node is pruned globally.

5. Checked that the old node's new proof steps describe the Lean finite dependent
   sum and component projection argument, with exactly the testing node as its
   non-elementary dependency. The new node has its source, self-contained statement,
   proof steps with the stated dependency union, agent proof origin, search records,
   split status, creation record, blueprint parent, unit/chapter, and verbatim Lean
   statement. Its dependencies agree with the docstring plan. Verdict: pass.

Changed only the new helper's proof-only imports and docstring (making the
naturality and two forget comparisons explicit), and corrected this report's
removed-import accounting. The original Lean proofs and all signatures were kept.
