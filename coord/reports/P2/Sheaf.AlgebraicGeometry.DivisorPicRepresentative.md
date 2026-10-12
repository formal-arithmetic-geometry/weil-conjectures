## What changed

Proved `AlgebraicGeometry.Scheme.Divisor.nonempty_toPic_iso_module` in
`Sheaf.AlgebraicGeometry.DivisorPicRepresentative` without changing its signature or visibility.
A private proved helper extracts divisor-module invertibility from `Divisor.module_local`:
choose a closed point using `smooth_connected_curve_local_rings`, take a principal generator
of its DVR maximal ideal, and project the existing invertibility conclusion.

The main proof writes D=A-B with A and B effective. It rewrites the effective-divisor
comparison's point-ideal product into `Divisor.idealSheaf`, translates the two isomorphisms
into Picard class equalities, uses O(D) tensor O(B) isomorphic to O(A), and cancels [O(B)].
`Pic.eq_ofIsInvertible_iff` then gives the exact representative isomorphism in the statement.
The new proof-only import is `Sheaf.AlgebraicGeometry.DivisorModuleTensorAdd`.

Both modules compile together with lcompile.py, without warnings. The edge cases of the new
statement were checked mathematically: either divisor zero gives the monoidal unitor;
B=-A gives reciprocal uniformizer powers; empty opens have the unique zero section;
negative coefficients use integer powers; affine/nonproper curves need no properness.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Divisor.nonempty_toPic_iso_module`
(node `lem-sc-divisor-toPic-representative`). There is no sorry left in the item's module.
The private helper `module_invertible` is fully proved.

Added one hole:
`AlgebraicGeometry.Scheme.Divisor.nonempty_module_tensor_add_iso`
(node `lem-sc-divisor-module-tensor-add`), in the new module
`Sheaf.AlgebraicGeometry.DivisorModuleTensorAdd`. Its proof is exactly `by sorry` and its
docstring and node give the complete multiplication/local-uniformizer argument.
This is a decomposition (one hole closed, one added), not a net reduction of holes.
The new statement is only the tensor compatibility step: it mentions neither `toPic`,
point-ideal products nor chosen Picard representatives. The effective comparison,
invertibility extraction and class cancellation are real compiled proofs in the item.

Existing holes used but neither added nor modified are
`AlgebraicGeometry.Scheme.divisorLineBundle_agrees_sc`,
`AlgebraicGeometry.Scheme.Divisor.module_local`, and
`AlgebraicGeometry.Scheme.smooth_connected_curve_local_rings`.

## No longer needed

Removed direct proof imports `WeilConjectures.AlgebraicGeometry.PicardFunctor` and
`WeilConjectures.AlgebraicGeometry.Picard.Group`; both remain transitively available through
the unchanged public import of `WeilConjectures.AlgebraicGeometry.Curve.Picard`.
No original proof-dependency node or module can be pruned entirely: the effective comparison,
local divisor-module lemma, local-rings lemma and Picard definitions/group are all still used.
The plan's separate O(0) identification and inverse-module comparison are unnecessary for
this proof: cancellation with the effective negative part replaces both. These steps have
no separate original dependency node to remove. The unit's realized statement/steps are empty
and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's tensor-multiplication step is not supplied by `Divisor.module_local` alone:
that lemma gives local generators but no global tensor morphism or tensor isomorphism.
The new node isolates precisely this missing step. No existing statement is disputed or
changed, and no forced adaptation is needed.

LeanFinder and local/library searches found no existing explicit divisor-module tensor
comparison. LeanSearch returned an Internal Server Error; it is recorded as unavailable,
not as evidence of absence. The blueprint search `divisor tensor` returned no matching
blueprint nodes. The source blueprint files are not present in this machine's literature
checkout; the full multiplication argument is recorded in the existing item's node.
[Stacks Tag 02SL](https://stacks.math.columbia.edu/tag/02SL) was read and supports the
valuation-additivity step; it is not by itself the explicit divisor-module isomorphism.

## New nodes

`lem-sc-divisor-module-tensor-add`, at
`dag/nodes/sec-curve-estimates/lem-sc-divisor-module-tensor-add.json`, realizes multiplication
O(A) tensor O(B) isomorphic to O(A+B). Its module is
`lean/Sheaf/AlgebraicGeometry/DivisorModuleTensorAdd.lean`. The existing node
`lem-sc-divisor-toPic-representative` now records the actual effective-part cancellation proof.
No change record is required: all existing signatures and public imports are unchanged.

## Second reading by P2

1. PASS. Diffed the existing module against the repository and compared the complete
   `Divisor.nonempty_toPic_iso_module` signature byte for byte, through `:= by`.
   Its signature, visibility, and both public imports are unchanged. There are no changed
   definitions, target statements, or forced adaptations. The only new declaration in the
   existing module is a private proved helper. No change record is needed.
2. PASS as a decomposition. Compiled both delivered modules in import order with
   `lcompile.py --all`; no errors or warnings. Scanned both sources: the only `sorry` is
   `Divisor.nonempty_module_tensor_add_iso`, explicitly listed above; no forbidden
   declarations or implementation attributes, and no definition containing `sorry`.
   A scratch copy with `#print axioms` for the helper, the item, and the split theorem
   reported only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is
   expected from the explicitly open imported theorems and the new tensor lemma.
   Closed-point and isomorphism witnesses are used inside proposition proofs only;
   no data definition chooses an arbitrary witness from an unproved existence theorem.
3. PASS. Read the tensor lemma, its complete local multiplication docstring, its new node,
   and the actual signatures and constructions of DivisorModule, DivisorModuleLocal, and
   SmoothConnectedCurveLocalRings. Local equivalences are specified pointwise, so their
   naturality follows by uniqueness; the same uniformizer identifies multiplication with
   the unit multiplication. The neighbourhoods cover closed points and the generic point.
   Checked A=0, B=0, B=-A, negative coefficients, empty opens, and nonproper curves.
   The statement is the tensor step alone, not a renamed representative comparison.
   Independent searches used LeanFinder's query "Multiplication of fractional ideal
   sheaves gives tensor compatibility for Cartier divisor line bundles", Loogle's
   `FractionalIdeal, TensorProduct`, and grep for Cartier/Weil divisors and fractional-ideal
   tensor results in Mathlib AlgebraicGeometry, plus rg on Sheaf and WeilConjectures with
   `associatedModule`, `sectionModule`, and `moduleOfSmoothConnectedCurve`. The hits supply
   neither this explicit divisor-module comparison nor a short proof of it. Closing the
   tensor lemma requires constructing and gluing a sheaf morphism, not a few-minute repair.
4. PASS. The effective comparison and Picard cancellation give a real reduction; the
   invertibility helper extracts an existing clause instead of adding another hole.
   Public imports are needed by the signatures; the remaining direct proof imports supply
   the declarations used in the proof or the split lemma's documented argument. Checked
   the old proof_deps: none is dropped, and the new tensor node is added. The two removed
   direct imports and the unused zero/inverse comparisons are already reported above;
   no whole module is pruned. Read `dag/units/sk-def-pic.json`: its `realized.statement`
   and `realized.steps` are empty. No unit statement or mandated step is bypassed.
5. PASS. Diffed the existing node: only permitted proof/proof_deps/proof_origin fields
   changed. Verified both nodes' proof_deps equal the union of their steps' uses, checked
   declaration names and Lean statements against the modules, and checked the new node's
   source, complete argument, searches, creation record, blueprint provenance, chapter,
   unit, and Lean record. The new lemma has its own module and node.

Second reading changed only the item's proof docstring to describe the actual positive/
negative-part cancellation argument, replacing the obsolete separate zero/inverse route.
No Lean proof or statement needed repair. Added this independent review and fresh search
records. One item hole closed and one strictly smaller tensor step added: net zero holes.
