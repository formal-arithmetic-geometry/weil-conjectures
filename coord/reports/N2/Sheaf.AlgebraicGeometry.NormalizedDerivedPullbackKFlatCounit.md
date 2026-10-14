## What changed

Replaced the sorry in
`AlgebraicGeometry.exists_normalized_derivedPullback_kFlat_counit` by a complete
Lean proof from a comparison on the resolving class. The declaration's signature,
visibility, and docstring are unchanged. All original public imports remain.
The three additional proof imports are private:
`Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison`,
`Sheaf.CategoryTheory.NatTransFromResolvingClass`, and
`Sheaf.Algebra.Homology.KFlatResolution`.

The new, fully proved generic theorem
`CategoryTheory.exists_natTrans_from_resolvingClass` extends a natural family of
maps from a resolving class. Its target functor need not preserve quasi-isomorphisms.
The proof defines the extension by inverse source map, representative component,
and target map. Right Ore squares, a further resolution, and cancellation prove
naturality and exact agreement with the family on the resolving class.

The remaining geometric theorem constructs e jointly with an isomorphism family
on K-flat homotopy representatives and their translates by one. It does not take
an arbitrary e or assert a comparison at other homotopy objects. The original
module proves that the class resolves every object, applies the generic extension,
then rewrites both counit components in the shift equation. Thus descent,
invertibility of the extended comparison on K-flat objects, and transport of the
shift equation are proved, rather than moved to another sorry.

The supplied epsilon-zero and its invertibility hypothesis are not needed by this
route: the representative construction supplies its own comparison. Their binders
remain intact; the unused-variable linter is disabled only for this declaration.
No existing definition or statement was changed. No forced adaptations are needed.
The final three-module set compiles using lcompile.py, without warnings.

## Proved and sorry left

Hole closed in the item:
`AlgebraicGeometry.exists_normalized_derivedPullback_kFlat_counit`
(node `lem-sc-derived-pullback-kflat-counit-shift-adjustment-normalized`).
There are no sorries left in the item's module.

New theorem proved without sorry:
`CategoryTheory.exists_natTrans_from_resolvingClass`
(node `lem-sc-nattrans-from-resolving-class`).

One hole added, and the only sorry in the delivered files:
`AlgebraicGeometry.exists_normalized_kFlat_representative_comparison`
(node `lem-sc-normalized-kflat-representative-comparison`). It is the
representative-construction part of the original argument, including joint
normalization and naturality restricted to the resolving class. It contains no
extension to arbitrary homotopy objects. Its source, full proof plan, declaration,
and DAG record are supplied separately for the next worker.

Accounting: one upper hole closed, one lower hole added, net zero. This is a
**decomposition**, not a complete proof of the geometric normalization theorem.
The generic descent theorem and the combination proof are complete Lean proofs.

## No longer needed

No original import, original node, or original module is pruned. The following
old direct proof dependencies are replaced in the item's proof by the three
lemma dependencies recorded in its node:
`def-pc-derived-category`, `def-pc-derived-pullback`, `def-pc-kflat-complex`,
`def-pc-module-pullback`, `def-pc-scheme-derived-tensor-structure`,
`def-sc-scheme-canonical-shift-unit-iso`, and
`def-sc-scheme-canonical-tensor-shift`.
All seven remain proof dependencies of the new representative-comparison node,
and several also occur in the signatures; none is eliminated from the closure. The item's proof now uses
the representative-comparison node, the generic extension node, and the existing
K-flat-resolution node. It no longer attempts the geometric representative
construction inside the homotopy-category descent argument.

`Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated` was tested as a proof import
and removed: Mathlib already synthesizes the needed right-fraction instance.
The final module does not import it. The earlier rejected square modules and
nodes remain outside the delivery, in scratchpad only.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery quantified arbitrary e and epsilon and claimed their
compatibility. Its sign counterexample remains valid; that statement is neither
imported nor reused. The new existential statement chooses e and the restricted
comparison family together. It passes that sign test because changing e alone
is not allowed by its conclusion. There is no arbitrary witness chosen from an
unproved theorem in a definition: the sole new definition is the explicit Prop
`kFlatShiftRepresentative`.

The original node's proof dependencies are definitions. They provide no theorem
implementing the joint representative normalization; that is precisely the new
remaining hole. Stacks Tag 06YJ proves K-flat computation and independence of
choices, not coherence for an arbitrary supplied tensorator. The new node and
docstring explicitly attribute that additional coherence to the parent's agent
expansion. This delivery does not claim that 06YJ itself states the new theorem.

For the generic extension theorem, the right Ore square is oriented toward the
chosen resolution; its denominator maps to the source of the arbitrary arrow.
Resolving its common source makes all three family components available.
Only the source functor inverts the denominator. The target functor is never
assumed to preserve it, which is essential for termwise pullback on non-K-flat
objects. If the resolving class is all objects, the proof agrees with the original
family by taking an identity arrow. Zero objects and the empty scheme do not
require nonzero components or any cancellation other than by isomorphisms.
For the geometric representative statement, the zero-object case has unique maps;
for an identity morphism the same supplied tensorator must be used in the joint
normalization. No universal assertion for arbitrary shifted-unit maps is made.

The unit record `sk-thm-picard-duality` has empty realized entries. No unit route,
target statement, or unit record was changed. Blueprint searches for 'counit shift'
and 'resolving', Mathlib searches through msearch.py, and local searches found no
existing declaration of the new representative result or the generic extension
in the needed direction. The source pages 06YJ, 06YH, and 04VC were read.

## New nodes

`lem-sc-normalized-kflat-representative-comparison`, in
`dag/nodes/sec-picard-framework/`, states the joint comparison and coherence on
the K-flat resolving class before extending to all homotopy objects. Its module is
`Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison`. It also records
the explicit class predicate. This is the one new item with sorry.

`lem-sc-nattrans-from-resolving-class`, in the same chapter, records the general
right-fraction extension theorem proved in
`Sheaf.CategoryTheory.NatTransFromResolvingClass`. Its proof only uses the stated
right-fraction and resolution hypotheses. It adds no hole.

The existing normalized-counit node records the actual three-step Lean proof and
its actual proof dependencies. There are no change records or signature changes.


## Second reading by N2

1. **Interfaces — pass.** Compared all three delivered modules with the repository.
   The two helper modules are new. The existing theorem's signature is byte for
   byte identical, and its docstring and public imports are unchanged. The diff
   adds only three private proof imports, a declaration-local unused-variable
   linter setting, and the proof. No existing definition is changed, no target
   statement is changed, and no change record or forced adaptation is required.

2. **Kernel proof and holes — pass as a decomposition.** Compiled the complete
   three-module set in import order with lcompile.py, without errors or warnings.
   A scratch copy with explicit #print axioms checked the new predicate and both
   new theorems as well as the item. The predicate and generic extension theorem
   use only propext, Classical.choice and Quot.sound. The representative theorem
   and item additionally use sorryAx, as reported. There is exactly one syntactic
   sorry in the delivered modules, the named representative-comparison theorem.
   No axiom, unsafe, opaque, implemented_by, extern or hollow definition occurs.
   The generic extension constructs its components explicitly from resolutions;
   those resolutions come from an actual hypothesis, not an unproved arbitrary
   existence theorem. The only new definition is an explicit object predicate.

3. **Split statements — pass, one geometric obligation remains.** Read the
   representative statement clause by clause: its comparisons are isomorphisms,
   it requires naturality only within the indicated full class, and it chooses e
   and the family together. The resolving predicate explicitly includes both
   q(P) and q(P)[1], so transport of the displayed equation needs no unstated
   shift-closure lemma. It retains the geometric normalization problem but omits
   extension to all homotopy objects; the extension is a separate proved argument,
   not a renamed sorry. The named hole has a source, natural-language construction
   and its own matching node. Rechecked zero complexes and the empty scheme
   (unique maps), and the earlier sign test: replacing e alone is not allowed.
   For the identity morphism over a field with the usual tensorator, identities
   give the family and the shifted-unit comparison; there is no demand that an
   arbitrary shifted-unit comparison work. The supplied epsilon-zero is not
   used, consistently with its absence from the conclusion and the independent
   counit provided by the derived-pullback construction.
   The generic lemma also covers a class of all objects (identity resolutions),
   and an empty category (all obligations vacuous); an empty resolving class in
   a nonempty category cannot satisfy hres. Its Ore square is correctly oriented:
   after resolving the common source, the arrow a into the source of t lies in W.
   Only A(a), never B(a), is cancelled. Searches with alternative wording through
   msearch leanfinder, loogle and grep, plus rg in both library roots, found no
   matching existing result. Mathlib natTransExtension extends through a
   localization with both functors already factoring through it, so it does not
   replace this lemma with its unrestricted target functor.
   Read Stacks [06YJ](https://stacks.math.columbia.edu/tag/06YJ) and
   [04VC](https://stacks.math.columbia.edu/tag/04VC): they support the representative
   computation and right Ore descent respectively. Supplied-tensorator coherence
   is explicitly attributed to the agent expansion, not to a literal source
   theorem. It is the remaining unformalized geometric obligation, not a proved
   result of this delivery, and was not closed in this reading.

4. **Route and pruning — pass.** The proof resolves each homotopy object using
   exists_isKFlatResolution, applies the fully proved Ore extension, and rewrites
   both components of the shift equation using agreement with the family. The
   proof imports each new helper privately; its other new import supplies the
   resolution theorem. The original public imports support signatures. No unused
   proof import remains. The seven replaced old direct dependencies are now
   explicitly listed above; all remain in the representative node's dependency
   closure, so there is no module pruning. Read sk-thm-picard-duality's statement,
   step and realized fields: no unit route or realization is changed.

5. **DAG agreement — pass.** Each recorded Lean statement occurs verbatim in its
   module. The existing node changes only proof, proof_deps and proof_origin;
   its three dependencies match the representative comparison, resolution and
   generic extension calls. Both new nodes include source, complete proof plan,
   search records, provenance, creation metadata, chapter, unit, blueprint and
   Lean records. The generic node has no proof dependencies beyond Mathlib; the
   geometric node retains the seven original construction dependencies. No
   unsupported progress or pruning is claimed: one existing hole closed and one
   new hole added gives net zero.

Second-reading changes: clarified the seven replaced direct dependencies under
No longer needed and added this independent review. No Lean proof or signature
needed repair. The remaining geometric hole needs construction and coherence
work beyond a short review; the generic descent and its application are checked.
