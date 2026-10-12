## What changed
Completed `torsion_finite_stalk_subobjects_iSup_eq_top` with the original signature.
The new module `Sheaf.AlgebraicGeometry.Curve.FiniteStalkSubobjectElement` proves
`torsion_exists_finite_stalk_subobject_element` and its private algebraic helper
`finite_stable_submodule`. It constructs the finite orbit span, restricts the
representation, transports the monic inclusion using the equivalence functor's
preimage, and proves stalk finiteness and element lifting by naturality.
The main proof factors these lifts through the supremum and reflects its stalk
isomorphism using the Galois-module equivalence. Updated both DAG proof records.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.Scheme.torsion_finite_stalk_subobjects_iSup_eq_top`
(node `lem-sc-field-torsion-finite-stalk-subobjects-cover`).
Also proved `AlgebraicGeometry.Scheme.torsion_exists_finite_stalk_subobject_element`
(node `lem-sc-field-finite-stalk-subobject-element`), which was left sorry by the
previous attempt. No sorry remains in either delivered module; no holes added.
The proofs still depend on the existing library's equivalence declarations and
whatever holes their import closure contains; those dependencies are not claimed
closed by this delivery. The new lemma is fully proved, not a decomposition.

## No longer needed
Removed `Sheaf.CategoryTheory.Galois.AutProfinite` (node
`lem-galois-aut-profinite`) and `Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations`
(node `lem-weil-pbc-torsion-sheaf-characterizations`) from the item's proof imports.
The former is replaced by Mathlib compactness of the absolute Galois group; the
latter by the already proved local torsion stalk criterion in
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion`.
Removed unused imports from the earlier sandbox attempt:
`Mathlib.CategoryTheory.Whiskering`, `Mathlib.RepresentationTheory.Intertwining`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`.
The old dependency `lem-exc-etale-open-subgroup-quotient-finite-discrete` moves
from the target node to the element lemma node and is still used through its
Mathlib match in the proved algebraic helper; it is not globally pruned.
Second reading removed the unused public import
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` from the new module.
The unit `sk-prop-cd-affine` has empty realized lists; its approximation route is
preserved. These pruning claims concern this argument, not global reachability.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt's remaining transport hole can be proved directly using
`Functor.preimage`, `Subobject.underlyingIso`, and naturality of the stalk comparison.
Its report incorrectly retained an unused torsion-characterization import.
Corrected the new node's blueprint ancestry and its searches to actual logged
queries. Checked edge cases: x = 0 gives the zero orbit span; trivial G gives the
cyclic span of x; infinite torsion M is allowed because only its orbit span needs
finite generation. No existing statement or definition changed.

## New nodes
`lem-sc-field-finite-stalk-subobject-element`, in
`lean/Sheaf/AlgebraicGeometry/Curve/FiniteStalkSubobjectElement.lean`, records the
fully proved finite-subobject lifting construction. It is a strict part of the
coverage argument and contains no supremum or conservativity claim. Its search
found Mathlib algebraic ingredients but no exact sheaf statement. No change records
are needed: existing public signatures and public imports are unchanged.

## Second reading by V3

1. **Interfaces and statements.** Compared the delivered item module with the repository version. The target theorem signature is byte-for-byte unchanged; the new element-lifting theorem has a self-contained statement matching its DAG node. Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. Searched the files for forbidden constructs and found no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; no definition contains a hole. `#print axioms` on both public theorems reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from existing open dependencies. The proofs use the existing equivalence and Mathlib finite-orbit ingredients. No arbitrary witness of mere existence is put into a public definition: the orbit span is constructed explicitly and the equivalence determines transported objects up to isomorphism. Verdict: pass.

3. **Split-off statements.** The new element-lifting statement is a strict component of the coverage argument, with a complete source and proof description in its docstring and a matching DAG node. It does not restate the supremum target, and no existing declaration duplicates it. Edge cases (zero element, trivial Galois action, and non-finitely-generated ambient torsion module) are covered by the construction. Verdict: pass.

4. **Pruning and route.** The proof uses the finite-stalk element lemma, the sheaf/Galois equivalence, and the local torsion criterion. The removed characterization and profinite imports are not referenced by the delivered proofs; finite quotient and compactness facts are supplied directly by Mathlib. The unit record has no realized statement or steps, so the route does not bypass a realized unit step. Verdict: pass.

5. **DAG agreement.** Updated the target node's proof, dependencies, and origin to match the Lean proof, and added the new node with its module, declaration, statement, source, proof, searches, and blueprint ancestry. Verdict: pass.

Changed: removed the unused public Grothendieck-abelian sheaf import from the new element module, expanded the pruning record to account for the moved finite-quotient dependency, and added this second-reading record. No Lean statements or definitions were changed during review. An independent LeanFinder search for unions of finite invariant subgroups found only component algebraic facts, not a duplicate sheaf statement; source searches in the library, upstream, and Mathlib likewise found no shorter complete theorem.
