## What changed

Reduced `Module.exists_finitePresentation_module_diagram` without changing its signature,
visibility, or docstring. The proof now obtains an explicit finite free presentation, lifts
its matrix to a common ring stage, applies the quotient-diagram construction, restricts the
ring colimit along the final functor, and proves the additive universal property.

Added `Sheaf.RingTheory.BaseChangeDiagramElementwise`, with a complete proof of
`Module.baseChange_diagram_elementwise` from Mathlib. It identifies the module direct limit
of the stage rings with the given ring cocone, tensors that equivalence, and transports
representatives and eventual zero through the given comparison maps. The statement needs
neither finite generation nor transition semilinearity. Added
`Sheaf.RingTheory.FinitePresentationModuleBaseChangeDiagram` for the remaining construction
from an explicit lifted matrix. All added imports in the item are proof-only.

Private proved helpers `Module.matrix_lifts_to_stage` and
`Module.additive_diagram_isColimit` implement matrix coefficient descent and the additive
universal property, including unrelated index and group universes. All three modules compile
cleanly through lcompile.py. The Stacks 00QX and 00R1 pages were read directly; the local
literature checkout does not contain algebra.tex on this machine.

## Proved and sorry left

Closed the item's one hole: `Module.exists_finitePresentation_module_diagram`, node
`lem-weil-pbc-finite-presentation-module-diagram`. This is a decomposition, not a net hole
reduction: one upper hole closed and one construction hole added.

Proved the new `Module.baseChange_diagram_elementwise`, node
`lem-weil-pbc-base-change-diagram-elementwise`, with no sorry and solely standard axioms.
The private matrix-lifting and additive-colimit helpers are also fully proved.

The sole sorry left in this delivery is
`Module.exists_finitePresentation_baseChange_diagram`, node
`lem-weil-pbc-finite-presentation-base-change-diagram`. Its proof is exactly `by sorry`.
It constructs the quotient diagram and tensor comparisons from an already supplied finite
presentation and lifted matrix. It assumes no ring colimit or finite-presentation class and
concludes no additive colimit property. This is strictly the construction step, not a
renamed version of the item. The source and full proof in words are in its docstring and node.

Edge cases checked in the argument: empty rows or columns use the arbitrary initial index in
the Finset bound induction; zero modules and zero rings are not excluded; preorder indices
need not be antisymmetric; and universes u and v are unrestricted. Small stage models in the
remaining construction use countability of finite-type integer algebras, including their
finite powers and quotients. No object is defined by choosing an arbitrary witness from the
remaining theorem; its witnesses are only destructured inside the proof of a proposition.

## No longer needed

Removed the item's proof import `Sheaf.Paper.DirectedColimitBaseChangeElementwise`, node
`lem-weil-pbc-directed-colimit-base-change-elementwise`. The generalized elementwise proof
uses the given cocone directly, avoiding chosen-colimit ring equivalence transport.

The item no longer needs node `lem-weil-pbc-filtered-colimit-modules-criterion` or a module
import for the small-index filtered-colimit criterion: the additive universal property is
constructed directly. The original criterion's Mathlib universe restriction was already
identified in the item's docstring. This is a local dependency pruning; no claim is made that
other targets cease to reach those nodes.

The item now delegates `lem-weil-pbc-tensor-right-exact`,
`lem-weil-pbc-tensor-finite-product`, and `def-weil-finitely-generated-module` to the
construction node; these remain needed and are not pruned. Ring elementwise and finality
nodes remain used. The elementwise proof uses the existing Mathlib-leaf nodes
`lem-weil-pbc-tensor-commutes-with-colimits` and
`lem-weil-pbc-filtered-colimit-modules-elementwise`. All original public imports are retained
for interface stability.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature correction found. The parent DAG called the quotient diagram
and its small-model construction elementary; it is substantial Lean work and remains the
single isolated obligation. The given proof import was sufficient for tensor representatives
in the chosen ring colimit, but did not directly supply the transported diagram's elementwise
criteria. Those criteria are now proved, rather than left as a new hole.

The unit sk-thm-p1 and its realized statement and proof steps are unchanged. This refinement
is below the unit level. Blueprint searches for presentation matrix and colimit representative
returned no equivalent imported blueprint node. DAG searches found the parent and generic
tensor-colimit and module-elementwise tools, which are cited rather than duplicated.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and Mathlib source
searches found tools but no complete matrix-diagram theorem. The new nodes record these
searches and the checked signatures.

## New nodes

`lem-weil-pbc-finite-presentation-base-change-diagram` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-presentation-base-change-diagram.json`
is the remaining explicit lifted-matrix construction (one sorry), implemented in
`lean/Sheaf/RingTheory/FinitePresentationModuleBaseChangeDiagram.lean`.

`lem-weil-pbc-base-change-diagram-elementwise` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-base-change-diagram-elementwise.json`
is proved in `lean/Sheaf/RingTheory/BaseChangeDiagramElementwise.lean`. Its proof uses
Mathlib only and generalizes the elementwise tensor argument to arbitrary ring cocones and
compatible additive diagrams. No change record is needed: existing signatures, definitions,
visibility and public imports are unchanged, and there are no adapted modules.

## Second reading by J1

1. **Interface comparison: passes.** Compared all three delivered modules with the
   repository; the two helper modules are new. The existing theorem
   `Module.exists_finitePresentation_module_diagram` has a byte-for-byte identical
   signature, visibility and docstring. Its only changes are proof-only imports,
   two private proved helpers, and the proof body. No definition, target statement,
   or other group's module changes; no change record is needed.

2. **Proof and axioms: passes as a decomposition.** Compiled the three modules in
   import order through lcompile.py, then compiled scratch copies with explicit
   `#print axioms` for all five declarations. The matrix-lifting helper, additive
   universal-property helper and `Module.baseChange_diagram_elementwise` use only
   `propext`, `Classical.choice`, and `Quot.sound`. The construction theorem and
   its parent additionally use `sorryAx`, exactly as reported. The only source
   `sorry` is the named construction theorem, with its docstring proof and node.
   There are no axioms, unsafe/opaque declarations, implementation overrides, or
   data definitions. The existential construction is eliminated only within the
   proof of the parent proposition; it is not used to define an arbitrary object.
   Scratch source files were removed before delivery.

3. **Split statements and search: passes.** Read Stacks
   [00QX](https://stacks.math.columbia.edu/tag/00QX), specifically the paragraph
   defining stage modules as cokernels of the lifted matrix, and its non-local
   counterpart [00R1](https://stacks.math.columbia.edu/tag/00R1). The remaining
   construction assumes the actual finite free presentation and an actual lifted
   matrix, needs no colimit hypothesis, and proves no additive colimit assertion.
   It isolates the cokernel construction and tensor comparisons rather than
   renaming the item. Surjectivity and exactness identify the S-cokernel with M;
   hA supplies the matrix comparison. Finite-type integer algebras and their finite
   powers and quotients are countable, so transporting to Type v is legitimate
   even when u exceeds v. Empty rows, empty columns, zero rings/modules, singleton
   indices and non-antisymmetric preorders cause no exceptions. Read
   [00D6](https://stacks.math.columbia.edu/tag/00D6),
   [00D7](https://stacks.math.columbia.edu/tag/00D7) and
   [00DD](https://stacks.math.columbia.edu/tag/00DD) against the proved elementwise
   lemma. Its formulas supply exactly the needed tensor comparisons and cocone
   compatibility; transition semilinearity and finiteness are unnecessary.
   Independent LeanFinder search for base change of finite-matrix cokernels found
   presentation and categorical cokernel tools, not this diagram theorem. Loogle
   found `TensorProduct.quotientTensorEquiv` and its evaluation lemmas. Searched
   lean/Sheaf, upstream WeilConjectures, and Mathlib with cokernel, matrix and
   presentation terminology. `ModuleCat.finitePresentation_descent_directedColimit`
   is still sorry, assumes a partial order and a common universe, and does not
   supply the compatible small group diagram. The local-ring-system theorem has
   additional local hypotheses and is also open. Neither replaces this reduction.
   Closing the remaining construction requires building and transporting a whole
   quotient diagram, beyond a few-minute repair.

4. **Route and pruning: passes.** Parent step 1 uses Mathlib's finite presentation,
   ring representatives and finite directed bounds. Step 2 uses the new explicit
   construction. Step 3 uses finality to restrict the ring colimit and the proved
   tensor elementwise lemma. Step 4 builds the additive universal property from
   representatives and eventual zero, including cross-universe cocones. Its
   independence calculation uses a common stage and the difference of two
   representatives, and additivity follows after moving two representatives to a
   common stage. The elementwise proof constructs the module direct-limit-to-S
   equivalence using the ring elementwise node, tensors using the tensor-colimit
   node, and uses direct-limit representatives and zero_exact for the two clauses.
   Read these dependency statements and their Mathlib records; they supply the
   facts taken from them. No shorter complete proved library result was found.
   The old direct tensor-colimit import and module-colimit criterion are accounted
   for under No longer needed; tensor exactness, finite products, finite generation
   and finality remain dependencies through the construction. Read
   dag/units/sk-thm-p1.json: neither the item nor the two new nodes is a realized
   unit statement or step, and the realized route is unchanged.

5. **DAG agreement: passes after correction.** The two new nodes have self-contained
   statements matching their Lean signatures, source and proof steps, dependency
   unions, actual search records, creation and blueprint provenance, and Lean
   records. The parent changes only proof fields. Its proof_deps match the four
   implemented proof steps. Corrected proof_origin's step numbers to refer to the
   current four-step proof rather than the old five-step plan. No node statement,
   stmt_deps, unit record or definition changed.

Second-reading changes: corrected the new elementwise lemma's docstring to describe
its actual direct-limit equivalence proof instead of claiming it calls
`directedColimitBaseChangeElementwise`; narrowed its public limits import from
`Mathlib.CategoryTheory.Limits.Final` to `Mathlib.CategoryTheory.Limits.IsLimit`;
corrected the parent's DAG proof_origin step references; added this review. Existing
proofs and signatures were retained. All three modules recompiled cleanly after the
Lean changes. One original hole is reduced to one strictly smaller construction
hole: zero net hole reduction, not a completed proof of the original target.
