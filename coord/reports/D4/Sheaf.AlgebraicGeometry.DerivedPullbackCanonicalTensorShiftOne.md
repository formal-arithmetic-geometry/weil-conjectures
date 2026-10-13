## What changed

Completed `AlgebraicGeometry.derivedPullback_canonicalTensorShift_one` from two
strictly smaller geometric statements. The theorem's signature and existing
docstring are unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift` and
`Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity`.

Constructed `schemeCanonicalShiftUnitIso X K` explicitly as the canonical
first-variable tensor shift at the unit followed by the translated left unitor.
Constructed `derivedPullbackTensorUnitShiftIso f e K` explicitly from the inverse
source comparison, the supplied inverse tensorator, `e` tensor the identity,
and the target comparison. Neither definition chooses an existence witness or
contains a hole.

The original module now proves three private helpers: naturality of the unit
comparison, cancellation of the source tensor-associativity comparison, and the
inverse-tensorator square. The last helper is a genuine calculation: functoriality,
unit-comparison naturality, whisker interchange, oplax-monoidal associativity,
tensorator naturality, and naturality of the associator reduce the square to the
single-scheme tensor identity. It works at every derived object and does not use
properness, Noetherianity, or K-flatness. The main theorem obtains the exact shift
and its unit formula, expands composite shift structures, substitutes the formula,
and restricts this algebraic square to `Q(P)`.

Updated the parent DAG proof and proof dependencies to this calculation. New
statements retain the parent chapter and unit; the unit's Serre-duality route is
not changed. Read the unit and chapter records; the unit's `realized` lists are
empty and this item is not itself its statement or a realized unit step.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.derivedPullback_canonicalTensorShift_one`
(`lem-sc-derived-pullback-canonical-tensor-shift-one`). There is no `sorry` in
its module, including its private helpers.

Added two holes, both named public theorems with source and complete proof
outline in their docstrings, each in its own new module:

- `AlgebraicGeometry.exists_derivedPullback_tensorUnitShift`
  (`lem-sc-derived-pullback-tensor-unit-shift`): coherent exact pullback translation
  with an explicit formula obtained from an isomorphism on the translated unit;
  it does not assert any inverse-tensorator square.
- `AlgebraicGeometry.schemeCanonicalShiftUnitIso_tensor`
  (`lem-sc-scheme-canonical-shift-unit-associativity`): compatibility of the
  canonical translated-unit comparison with reassociation and tensoring by a
  fixed factor, on one scheme; no pullback or exactness assertion.

This is a decomposition (one upper hole closed, two lower holes added), not a
claim of a sorry-free proof of the geometric theory. The first remaining theorem
is the geometric exactness/construction part; the second is the canonical Koszul
associativity computation. All gluing between them and the original statement is
proved in Lean.

All four delivered Lean modules compile. The original signature is copied verbatim,
including universe parameters and the four leading `letI` bindings. The explicit
comparisons require no Noetherian or proper assumptions. Small cases checked for
the new formulas: the empty scheme gives the zero category; zero tensor factors
give the unique zero maps; the unit in degree zero and its translate in degree
minus one give the expected left-unit map; the tensor associativity identity has
no extra sign from shifting a second factor. The shifted unit sits in degree minus
one in the cochain convention.

## No longer needed

Imports removed: none. Every original import is part of the existing public
statement interface; both added proof imports are used. No existing module is
claimed to leave the target import closure.

No longer needed as a separate unproved step: the geometric calculation of the
inverse-tensorator square on K-flat representatives. It is now proved for every
object by `tensor_unit_shift_square`; its only geometric tensor ingredient is the
single-scheme associativity identity. There was no separate existing DAG node or
module for that step, so no existing node/module is listed as pruned.

The old parent `proof_deps` consisting solely of definitions was replaced by the
two new statements and the explicit comparison definition, together with canonical
tensor shifts. Original definition nodes stay in `stmt_deps`, and those required
by the remaining geometric construction stay below its node. Explicitly removed
from the parent's direct `proof_deps`: `def-pc-scheme`, `def-pc-derived-category`,
`def-pc-scheme-derived-tensor-structure`, `def-pc-kflat-complex`,
`def-pc-derived-pullback`, and `def-weil-proper-morphism`. They remain statement
or lower construction dependencies, so none is claimed pruned from the import
closure.

## Where the brief, the DAG or earlier work was wrong

The original node had one long proof step and cited definitions only. Its
exactness claim alone is already supplied by `exists_derivedPullback`, but that
statement does not relate its exact shift to the specified canonical tensor shifts
and supplied monoidal structure. The plan's construction and single-scheme
associativity calculation therefore need their own statements. The tensorator
square itself is formal once those are available, as the compiled proof shows.

Read Stacks Tags 08EU, 06YH and 06YJ. Tag 08EU uses exactness in its projection
formula argument; it does not state transport for an arbitrary supplied strong
monoidal structure. Tag 06YJ gives the geometric exact derived pullback. The
transport/construction is an agent expansion of the parent's existing plan, and
is explicitly marked as such in the new node. No assertion about the supplied
monoidal structure being a canonical model has been silently assumed.

Mathlib searches used LeanFinder, Loogle and grep, including tensor-shift and
associator queries. LeanSearch was attempted for both parts and returned Internal
Server Error; recorded as unavailable, not as a negative mathematical result.
Read the upstream derived tensor shift, shift-comparison, shift-unitor and étale
upper-star shift proofs. The latter concern a different sheaf category and its
specific tensor comparison; they do not state this theorem for a supplied monoidal
structure on module-sheaf pullback with independent localization universe.

## New nodes

`def-sc-scheme-canonical-shift-unit-iso`, in
`Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso`, records the real composite
`O_X[1] tensor K ≅ K[1]`. It is needed in the signatures of both remaining statements.

`lem-sc-derived-pullback-tensor-unit-shift`, in
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift`, records the exact coherent
pullback shift with its translated-unit formula. The accompanying comparison
isomorphism is constructed explicitly with `e` as a parameter, not chosen from this
unproved existence theorem.

`lem-sc-scheme-canonical-shift-unit-associativity`, in
`Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity`, isolates the
single-scheme tensor identity needed on both source and target. Its statement is
strictly a part of the algebraic square and contains no pullback.

No change record is required: no existing statement, definition or visibility was
changed, and no other existing module was adapted.

## Second reading by D4

1. **Statements and signatures.** Compared the delivered target module byte for byte with the repository version. The existing theorem signature and docstring are unchanged; the four new public declarations have signatures matching their DAG node records. Verdict: pass.

2. **Proof and axioms.** Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds. The target module has no `sorry`, axiom, unsafe, opaque, extern, or implemented_by. The scratch `#print axioms` probe reports only `propext`, `Classical.choice`, and `Quot.sound` for both explicit definitions. The target and the two intentionally split public theorems additionally depend on `sorryAx`, exactly as expected from the open statements. Verdict: pass, with those two documented holes open.

3. **Split-off statements.** Checked the two split statements against their docstrings, source tags, edge cases, and searches recorded in their node files. The exact pullback shift statement supplies the construction and coherence needed by the target; the single-scheme associativity statement isolates the remaining canonical tensor identity. Neither restates the target, and no existing library declaration duplicates them. Verdict: pass.

4. **Pruning and route.** The target proof uses the explicit canonical translated-unit definition, the exact translated-unit construction, and the single-scheme associativity lemma; its private calculation proves the tensorator square directly. Proof-only imports are plain `import`, and all added imports are used. The parent unit and chapter route remain recorded in the node. Verdict: pass.

5. **Nodes and Lean agreement.** Updated parent proof steps, dependencies, and origin to match the Lean calculation. New node metadata, declarations, docstrings, and source/proof records agree with the delivered modules. Verdict: pass.

Independent second-reader searches used LeanFinder query “tensor associator natural transformation compatible with shift in first variable derived category”, Loogle query `CategoryTheory.MonoidalCategory.tensorRightTensor`, and grep `tensorRightTensor.*CommShift|associator.*CommShift|CommShift.*associator`. The hits supply the ordinary tensor associator and shift naturality tools, not the canonical derived associativity identity. Also searched both Lean roots for translated-unit comparisons and inspected upstream `ShiftUnitor`, `ShiftComparison`, and the independent-universe tensor shift construction. The upstream results do not discharge either remaining statement with this localization universe and supplied monoidal structure.

Source verification: read Stacks Tags 06YH, 06YJ, and 08EU directly. These supply the derived tensor and geometric exactness background; transport for an arbitrary supplied monoidal structure remains the explicitly identified agent expansion, not a quoted Stacks theorem. The degree-one single-scheme equation has no second-variable shift, hence no additional interchange sign. At zero factors it reduces to the unique zero morphism; on the degree-zero unit the two composites are the first-variable shift followed by the same unitor.

Changed during second reading: added this review record and explicit removed-dependency accounting; no Lean proof or statement changes were needed.
