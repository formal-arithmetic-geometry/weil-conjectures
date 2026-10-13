## What changed

Completed `AlgebraicGeometry.finiteGaloisTensorDecomposition` without changing its
signature or any public import. A proved private helper
`AlgebraicGeometry.finiteGaloisTensorAlgEquiv` constructs the canonical algebra map
using the tensor universal property, proves surjectivity using Dedekind independence
and `span_flip_eq_top_iff_linearIndependent`, and proves injectivity using equality
of E-dimensions and the Galois degree formula. This replaces the primitive-element/CRT
route below the unit level.

For the geometric part, the proof applies the existing `finiteGaloisTensorCoproduct`,
constructs both projections and all automorphisms as site morphisms, and proves the
component inclusions are a monic, disjoint covering. The already proved source theorem
`Scheme.Etale.isIso_piLift_of_disjoint` supplies gluing. The `Types.Small.productIso`
comparison preserves the independent universes u and v; finite Q can be shrunk to v.
Functoriality and the component projection equations prove both restriction formulas.
The second projection uses q itself, not its inverse.

Proof imports added: `WeilConjectures.Mathlib.RingTheory.Etale.Field`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover`,
`Mathlib.LinearAlgebra.Dual.Lemmas`, and `Mathlib.CategoryTheory.Limits.Types.Products`.
The item's DAG proof, proof dependencies, and proof origin now describe this route.
No new modules, definitions, statements with sorry, or interface changes.

Search: Lean Finder for the finite-Galois tensor-product decomposition returned
Galois-group equivalences, but no tensor decomposition. Loogle `IsGalois, TensorProduct`
found no match. Local rg of Mathlib FieldTheory and the source library found
`linearIndependent_monoidHom`, `span_flip_eq_top_iff_linearIndependent`,
`Module.finrank_baseChange`, and the existing disjoint-cover theorem. The corresponding
existing nodes for disjoint-cover gluing and finite-separable etaleness are reused.

Validation: repeated single-file `lcompile.py` checks; the complete proof compiles
without warnings. The trivial extension is included: Q has one element, evaluation is
multiplication and the restriction equivalence is the singleton product. Positive
characteristic is included because Dedekind independence is valid over every field.
No primitive-element assumption or restriction on characteristic was introduced.
The unit `sk-prop-h2` and its realized statement/steps remain unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finiteGaloisTensorDecomposition`
(node `lem-exc-finite-galois-tensor-decomposition`). Its algebraic clause is proved
from Mathlib alone, and the combined theorem is proved from existing dependencies.
The private helper `AlgebraicGeometry.finiteGaloisTensorAlgEquiv` is also fully proved.

No sorry remains in the delivered module; zero holes were added or split off.
The proof still depends on the existing holed theorem
`AlgebraicGeometry.finiteGaloisTensorCoproduct`
(node `lem-exc-finite-galois-algebra-tensor-decomposition`), which is unchanged and
is the next geometric proof item. This delivery therefore does not claim a completely
sorry-free transitive axiom closure.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields`
  (`lem-exc-etale-coproduct-etale`): individual finite-separable etaleness followed by
  base change and composition suffices.
- `Sheaf.AlgebraicGeometry.Sites.FiniteEtaleCoproductSections`
  (`lem-exc-finite-galois-sheaf-sections-coproduct`): the proved source disjoint-cover
  theorem supplies gluing directly; site-colimit and overlap hypotheses are unnecessary.
- `Sheaf.RingTheory.PolynomialDistinctLinearCRT`
  (`lem-pc-polynomial-quotient-distinct-linear-crt`): the linear-independence route
  proves the canonical tensor map is bijective.

Additional old proof-dependency nodes no longer used by this argument:
- `lem-weil-pbc-finite-separable-extension-primitive-element`
  (Mathlib `Field.exists_primitive_element`).
- `lem-weil-pbc-minimal-polynomial-quotient-field-iso`
  (Mathlib `IntermediateField.adjoinRootEquivAdjoin`).
- `lem-weil-pbc-normal-extension-conjugate-by-automorphism`
  (Mathlib `minpoly.exists_algEquiv_of_root'`).

Their Mathlib modules can remain transitively available through the unchanged public
Galois import; this proof does not use these declarations. The retained dependencies
are the tensor universal property, the Galois degree formula, the affine tensor
coproduct consequence, finite-separable etaleness, and proved disjoint-cover gluing.
The removed Sheaf modules are no longer needed by this item; global reachability is
for the maintainer's queue to determine.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original node's lengthy
primitive-element/CRT proof plan was unnecessary: Dedekind independence plus finite
Galois dimension proves exactly its algebraic clause. The finite-coproduct sheaf node
also imposes site-colimit and empty-overlap hypotheses that need not be assembled
when applying the existing proved disjoint-cover theorem.

The existing declaration docstring describes the old valid plan; the updated DAG and
this report describe the actual proof. Stacks Tag 03SF is a general Galois-cover section,
not an explicit Lean-level proof of this tensor formula; the new algebraic argument is
marked agent-written and cites the actual Mathlib lemmas it uses. No source text was
invented and no target statement was changed.


## Second reading by A2

1. **Interface preservation: PASS.** Compared the sole delivered Lean module with
   the repository using `diff -u` and directly compared the existing theorem's
   complete signature: byte-for-byte identical. All public imports and the original
   docstring are unchanged. Only proof imports, a proved private helper, and the
   original proof body changed. No definition or change record is introduced.
2. **Proof and axioms: PASS.** Independently compiled the module with `lcompile.py`
   (4.1 seconds, no errors or warnings). A scratch copy with `#print axioms` shows
   only `propext`, `Classical.choice`, and `Quot.sound` for the private algebraic
   helper; the combined theorem additionally uses `sorryAx`, as expected from the
   unchanged `finiteGaloisTensorCoproduct`. Scanned the delivered source: no sorry,
   axiom, unsafe, opaque, implemented_by, extern, or kernel-check bypass. Read the
   coproduct and disjoint-cover dependencies. The coproduct isomorphism obtained
   from the open theorem is determined uniquely by its component projection
   equations (coproduct and pullback universal properties), so this is not arbitrary
   data chosen from mere existence. The actual forward maps of phi and beta are
   explicitly constructed, with bijectivity proved for each.
3. **Split statements and small cases: PASS / none.** No new holed statement or node
   is delivered. Checked the private helper's Dedekind-independence, spanning, and
   dimension argument over an arbitrary field. For E=L it specializes to the single
   identity coordinate and multiplication; there is no positive-characteristic or
   nontrivial-extension assumption. The automorphism group contains the identity,
   including in the singleton case. An additional launcher grep search with tensor
   equivalence/product terminology, and direct rg searches of Mathlib and both Lean
   roots, found no shorter ready-made Galois tensor equivalence to replace this proof.
4. **Route and pruning: PASS.** Every proof import supports an explicitly used
   declaration; no proof-only import is public. Compared old and new proof_deps:
   all six removed dependency nodes are listed under No longer needed, including
   all three removed Sheaf modules. The new algebraic route is below the unit
   level. The affine coproduct step and the sheaf restriction calculation remain;
   `dag/units/sk-prop-h2.json`, its statement, step, and realized record are untouched.
   Both component equations were checked: j(q) then p1 is identity, and j(q) then p2
   is Spec q. The categorical/type product comparison keeps u and v independent.
5. **DAG consistency: PASS.** Only proof, proof_deps, and proof_origin differ in the
   existing node. Checked all five retained dependencies against their Lean or
   Mathlib records. The union of proof-step uses equals proof_deps exactly. The
   source-by-source steps describe the actual Lean argument and identify the new
   algebraic argument as agent-written. No new-node requirements apply. Historical
   split_report/tool_uses still mention CRT; these are outside the fields permitted
   for this proof-only delivery, and the updated proof and pruning report supersede
   that historical route.

Second reading changed only this report, adding the independent review and axiom
results. No proof repair was necessary. One original hole is closed, zero holes
are added, and zero statements are split off; the existing geometric dependency
remains open as already reported.
