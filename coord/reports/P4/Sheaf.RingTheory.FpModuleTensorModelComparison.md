## What changed

Reduced AlgebraicGeometry.exists_eventually_tensor_model_equiv in
Sheaf.RingTheory.FpModuleTensorModelComparison to the algebra and module parts of
its existing Stacks 02JO (3) argument. Its signature, universes, visibility and
public imports are unchanged. Its proof now constructs the final linear equivalence:
Mathlib Algebra.IsPushout.comp_iff identifies the prescribed algebra pushout,
Algebra.IsPushout.cancelBaseChange gives both tensor cancellation equivalences,
and LinearEquiv.restrictScalars and trans compose them with the descended
module equivalence. No flatness assumption or arbitrary object construction was added.

Added two public theorem modules, each with one named sorry and a complete proof
in its docstring, for the descent work that the existing interfaces do not combine:
Sheaf.RingTheory.TensorModelAlgebraDescent (algebras only), and
Sheaf.RingTheory.CompatibleModuleModelDescent (modules only). The first supplies
compatible Q coefficient maps and pushout squares on a tail; the second uses those
maps to descend an equivalence of module base changes, independently of P or A.
The original DAG node now follows the actual three-step Lean reduction.

All three modules compile cleanly through lcompile.py --all. The delivery dry run
checks their declarations and axiom probes. The original theorem rests on the two
explicitly recorded new holes; this is not a sorry-free proof of its dependency closure.

## Proved and sorry left

Hole closed (1): AlgebraicGeometry.exists_eventually_tensor_model_equiv,
node lem-pc-fp-module-tensor-model-comparison. No sorry remains in the assigned module.

Holes added (2):
- AlgebraicGeometry.exists_tensor_model_algebra_tail in
  Sheaf.RingTheory.TensorModelAlgebraDescent,
  node lem-pc-tensor-model-algebra-descent.
- AlgebraicGeometry.exists_eventually_compatible_module_equiv in
  Sheaf.RingTheory.CompatibleModuleModelDescent,
  node lem-pc-compatible-module-model-descent.

This is a decomposition: one upper hole closed and two strictly smaller holes added,
net minus one hole. The algebra theorem has no module parameters, module comparison,
or module finite-presentation hypotheses. The module theorem has no A, P, f, algebra
model equivalence or algebra finite-presentation hypotheses. Neither is a renamed
version of the original theorem. Their combination, scalar restriction and both
cancellations are fully proved in the assigned module.

## No longer needed

Removed the assigned module's direct proof imports:
- Sheaf.Algebra.FinitePresentationColimit,
  lem-pc-fp-module-map-descent-affine;
- Sheaf.Paper.DirectedColimitBaseChangeElementwise,
  lem-weil-pbc-directed-colimit-base-change-elementwise;
- Sheaf.RingTheory.ColimitCategoryFpAlgebras,
  lem-weil-pbc-colimit-category-fp-algebras.

They are replaced by the two new proof-only imports. These existing nodes remain
needed by the proof plans of the new statements and are not globally pruned.
Likewise the original direct proof dependencies def-weil-pbc-category-colimit,
lem-pc-fp-module-base-change, lem-weil-pbc-filtered-colimit-modules-criterion,
lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit,
lem-weil-pbc-finite-presentation-base-change-composition and
lem-weil-pbc-finite-presentation-over-finite-type-algebra are relocated into the
new nodes' statement/proof dependencies as appropriate. No module is claimed to
leave the targets' closure. No public import was removed or added.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The existing module-map descent theorem
uses PartialOrder indices, categorical colimit F and one universe. The assigned
statement uses a directed Preorder, a supplied colimit cocone and separate universes.
Its docstring already anticipates the poset-reflection bridge; the new module lemma
makes this bridge, tensor colimits and cancellation part of its named proof task.
The algebra-map descent interface uses the opposite tensor convention and lacks
the compatible family of coefficient maps needed for module descent. The new
algebra lemma supplies exactly that family, without adding a module task.

Checked the unit sk-thm-picard-semicon: neither this node nor the new nodes is a
realized unit statement or step, and the same 02JO algebra/module comparison route
is retained. No target, definition, existing statement or foreign held module changed.

The local literature checkout contains only its lists, so sources were read online:
https://stacks.math.columbia.edu/tag/02JO (last paragraph of the proof of (3)),
https://stacks.math.columbia.edu/tag/05N9 (2), (3), and
https://stacks.math.columbia.edu/tag/05N7 (2), (3).
Mathlib's IsTensorProduct.lean was read for pushout composition and cancellation.

Before the new statements were written, their boundary cases were checked in the
argument: k ensures a nonempty cofinal tail; zero rings and zero modules are allowed;
empty generator/relation sets only require a common upper bound; no tensor step
uses flatness or faithful flatness. A non-antisymmetric preorder is handled by its
poset reflection, and universe lifting gives a common universe for descent before
transporting the equivalences back. Compatibility of q with every transition and
coprojection is explicit, so module descent cannot accidentally use unrelated
Q-actions at different stages.

## New nodes

lem-pc-tensor-model-algebra-descent, module
Sheaf.RingTheory.TensorModelAlgebraDescent: precisely the algebra part of original
steps 1--3, including eventual invertibility and transition/colimit compatibility.
Its proof refers to existing elementwise tensor colimits, algebra factorization,
finite-presentation cancellation and algebra-map/equality descent. The separate
existing comparison-system modules were also read: their interfaces do not record
the Q coefficient maps and their canonical colimit compatibility needed here.

lem-pc-compatible-module-model-descent, module
Sheaf.RingTheory.CompatibleModuleModelDescent: the original module step for a fixed
compatible family q. It descends maps and inverse identities between two finitely
presented modules at a B stage, then extends the equivalence to later stages. It
uses existing affine module-map/equality descent and finite-presentation base change.

Both carry full signatures, sources, numbered proofs and searches. LeanSearch was
attempted for each and returned Internal Server Error (recorded as unavailable).
LeanFinder returned ring factorization, pushout and module-colimit component lemmas;
Loogle found tensor associators. Grep of Mathlib and both library roots found no exact
compatible-family theorem. Blueprint searches for tensor model and 05N7 found no
imported blueprint match. Searches by tags 05N7/05N9 found the existing map-descent
and comparison-system nodes, which were read before these task-specific bridges.
No change record is needed: existing interfaces are unchanged.

## Second reading by P4

1. **Interface: pass.** Compared the delivered item module with the repository using
   `diff`: the theorem statement, universes, namespace, visibility, and all existing
   declarations are unchanged byte-for-byte. The two additional modules contain only
   the new split-off declarations and their documented statements. No definition or
   target statement was changed, so no change record or forced adaptation is needed.
2. **Proof: pass.** Compiled all three modules with `lcompile.py --all`; compilation
   is clean. The assigned theorem has no `sorry`. The only remaining sorries are the
   two named split-off theorems listed above, each public and documented. There are no
   `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definitions.
   The assigned proof uses Mathlib pushout composition/cancellation and explicit
   scalar restriction; it does not choose data from an undetermined existence proof.
3. **Split statements: pass.** The algebra split removes all module parameters and
   states only eventual coefficient maps, compatibility, and pushout squares. The
   module split fixes a compatible coefficient family and states only eventual module
   equivalences. Both are strictly smaller than the original theorem, have sources,
   proof plans, searches, and matching DAG nodes, and are not duplicate declarations
   found in Mathlib or the library.
4. **Route and pruning: pass.** The original theorem now follows the two split nodes,
   then `Algebra.IsPushout.comp_iff`, `cancelBaseChange`, and restriction of scalars.
   The three former direct proof-only imports removed from the item are unused; their
   underlying nodes remain dependencies of the split statements. The unit route is
   unchanged because this item and both splits are below the realized unit.
5. **DAG and source review: pass.** The delivered node proofs and `proof_deps` match
   the imports and theorem applications in the Lean files. The Stacks 02JO (3), 05N7,
   and 05N9 route is retained, and edge cases (zero rings/modules, empty presentations,
   and preorder indices) are covered by the stated constructions without extra
   hypotheses.

The second reading found no repair beyond adding this section.
