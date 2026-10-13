## What changed

Replaced the sole sorry in `Sheaf.RingTheory.FinitePresentationComparisonSystem`
with a complete Lean proof from two strictly smaller construction statements.
All existing signatures, visibility, docstrings and public imports are unchanged.
The proof imports `ComparisonMapFiniteStage`, `ComparisonMapBaseChangeSystem`,
and Mathlib's `RingTheory.FiniteStability` privately.

`RingHom.exists_comparison_map_finite_stage` in the new module
`Sheaf.RingTheory.ComparisonMapFiniteStage` handles only descent to a single stage.
It accepts an arbitrary compatible limit ring map, not an equivalence, and does
not assume finite presentation of φ₀. It produces a P-linear canonical
coprojection and a single comparison map with its exact limit identity. It
asserts no diagrams, pushouts, colimits, or finite presentation of that map.

`RingHom.exists_comparison_map_base_change_system` in the new module
`Sheaf.RingTheory.ComparisonMapBaseChangeSystem` handles only extending an already
given single-stage map by base change and identifying its colimit. It assumes
neither finite presentation of P over Z, of Q over P, nor of φ₀. It asserts no
finite presentation of the comparison components. Its input specifies the
single-stage map and both required identities explicitly; it does not assume
the system it is asked to construct.

The original module proves filteredness of the upper tail directly. Its proved
private helper `RingHom.finitePresentation_tensorMap` constructs the base-change
isomorphism `(T ⊗[R] B) ⊗[B] C ≃+* T ⊗[R] C` by tensor commutation, congruence
and cancellation. It verifies that composing the left inclusion with this
isomorphism gives `id_T ⊗ φ`, so finite presentation follows from Mathlib base
change and invariance under ring equivalence, in arbitrary universes. For each
component of the system, the left-inclusion identity and
`RingHom.FinitePresentation.of_comp_finiteType` then prove finite presentation;
the proof conjugates back through d and c explicitly.

The original node's proof and proof dependencies now follow this Lean argument.
Both new statements have matching nodes, source citations, complete proofs in
words, and logged searches. The unit `sk-thm-p1` and its realized steps are
unchanged. There are no changes to existing definitions or statements and no
forced adaptations.

Validation: all three modules compile together in import order through
`lcompile.py --all`, without warnings. The delivery dry run printed OK after its axiom probes and preflight; the
independent second reading is the next reader’s task, and nothing was pushed. The local Stacks checkout is absent on this machine;
Tags 02JO and 05N9 were read online at their cited tag pages. No source file or
tool in the read-only repository was edited directly.

## Proved and sorry left

Closed: `RingHom.exists_finitePresentation_comparison_system`
(node `lem-weil-pbc-finite-presentation-comparison-system`). Its proof body has
no sorry. The private `RingHom.finitePresentation_tensorMap` is proved entirely
from Mathlib, with no new holes.

Added and still sorry:

- `RingHom.exists_comparison_map_finite_stage`
  (`lem-weil-pbc-comparison-map-finite-stage`), in
  `Sheaf.RingTheory.ComparisonMapFiniteStage`.
- `RingHom.exists_comparison_map_base_change_system`
  (`lem-weil-pbc-comparison-map-base-change-system`), in
  `Sheaf.RingTheory.ComparisonMapBaseChangeSystem`.

No sorry remains in the item's module. Each added sorry is exactly the entire
proof of its public named theorem. This is a decomposition: one upper hole
closed and two lower holes added, not a claim that the construction is now
sorry-free. The filteredness and all component finite-presentation arguments
are actually proved. No new data definition chooses a witness from an
unproved existence theorem.

Edge cases checked for the new statements: I may be a singleton, in which case
the construction stays at that stage; empty I is impossible because i₀ is
given. A directed preorder need not be antisymmetric, and the upper-tail proof
uses only directedness and transitivity. Zero rings and zero tensor rings are
allowed. Empty finite presentations cause no exceptional condition. For the
first lemma the limit map need not be bijective; descent uses only its two
inclusions and finite presentation of P and Q. In the second lemma P and Q may
have infinite presentations, since no finite-stage factorization is performed.

## No longer needed

No original import or module is pruned. The original direct dependencies
`lem-weil-pbc-directed-colimit-base-change-elementwise` and
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit` are no longer
direct dependencies of the item: the former is used by both new nodes and the
latter by the finite-stage node. They remain in the proof-dependency closure. The original public imports are
needed by the unchanged statement. All five original planned dependencies
remain needed, either for the two construction subarguments or for the proved
finite-presentation argument. The factorization dependency and the elementwise
colimit dependency move to the appropriate new nodes rather than being dropped.

No model-stage theorem or filtered-bijective-stage theorem is imported: these
are above this item and importing them would be circular. This delivery does
not bypass a realized unit statement or proof step.

## Where the brief, the DAG or earlier work was wrong

The stated plan's component lemmas give the algebraic ingredients, but their
signatures do not directly supply the categorical tensor diagrams, their
common-universe lifts, or the compatible simultaneous descent. Those are the
remaining glue constructions separated into the two new statements. The upper
theorem is genuinely proved from those parts and Mathlib; the entire conclusion
has not been renamed or repackaged as another sorry.

The source-library and Mathlib searches found no exact theorem for either new
statement. LeanFinder returned the existing finite-presentation factorization
lemmas for descent and tensor direct-limit lemmas for extension. Source grep
confirmed the component lemmas. Both LeanSearch queries returned Internal
Server Error, which is recorded as unavailable, not as no match. Blueprint
search for tensor comparison found only unrelated completed-Frobenius and
constant-sheaf tensor nodes, not either of these ring statements.

A scratchpad experiment constructs the canonical upper-tail tensor ring diagram
and cocone and proves that cocone colimiting from
`TensorProduct.directedColimitBaseChangeElementwise`, using
`Types.FilteredColimit.isColimitOf'` and explicit universe shrinking. This
experiment compiles, but it is not part of the delivered proof and is not
counted as a closed hole. It is available in `scratchpad/TensorDiagram.lean`
for the next worker; the outstanding part of descent is applying factorization
twice and transporting the descended algebra structure through the chosen
stage and the tensor maps.

## New nodes

`lem-weil-pbc-comparison-map-finite-stage` records only the finite-presentation
factorization portion: descend P, then Q, and combine the maps by tensor
universality. It belongs to the same chapter and unit as the item and inherits
its blueprint ancestor through the item. Its Lean theorem is in
`lean/Sheaf/RingTheory/ComparisonMapFiniteStage.lean`.

`lem-weil-pbc-comparison-map-base-change-system` records the universal-property
portion after a single stage has already been chosen: extend by tensor base
change, verify pushout transitions, and identify colimits and their comparison.
It belongs to the same chapter and unit and inherits the same blueprint
ancestor through the item. Its Lean theorem is in
`lean/Sheaf/RingTheory/ComparisonMapBaseChangeSystem.lean`.

No change record is needed: no existing public interface changed.


## Second reading by K1

1. **Interface — pass.** Compared the delivered `FinitePresentationComparisonSystem.lean`
   with the read-only repository using `diff -u`. The sole existing public declaration,
   `RingHom.exists_finitePresentation_comparison_system`, has byte-for-byte the same
   signature and docstring. Its hypotheses `hfp`, both finite-presentation instances,
   `aP`, `e`, and `he`, and all six conclusion clauses are unchanged. The only additions
   are three private imports, the proved private helper, and the replacement proof.
   There are no definition changes, interface change records, or forced adaptations.

2. **Proof and axioms — pass, conditional on the two listed holes.** Compiled all three
   delivered modules in import order using `lcompile.py --all`, with no errors or
   warnings. Independently compiled scratch copies with `#print axioms` for the private
   tensor-map helper and all three public theorems. The helper uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Each public theorem also uses `sorryAx`, as
   expected from the two construction holes. The only `sorry` tokens in delivered Lean
   are the entire proofs of the two named new theorems. There are no definitions,
   arbitrary witness choices in definitions, or forbidden declarations. The main proof
   applies the single-stage theorem with `e.toRingHom` and `he`, then supplies its exact
   witnesses to the extension theorem. It proves filteredness independently and uses
   `hcompat` to identify `g.comp b` with the base change of φ₀. Finite presentation of
   `b` and finite-type cancellation give that of `g`; conjugation by `d` and `c`
   gives that of the actual components. None of these steps adds a hypothesis.

3. **Split statements and sources — pass.** Read Stacks Tags
   [02JO](https://stacks.math.columbia.edu/tag/02JO), proof of (3),
   [00QO](https://stacks.math.columbia.edu/tag/00QO),
   [05N9](https://stacks.math.columbia.edu/tag/05N9), and
   [00DD](https://stacks.math.columbia.edu/tag/00DD).
   Checked each new Lean hypothesis and conclusion against its node. Finite-stage
   descent needs only finite presentation of P and Q: factor P into a B stage, give
   later C stages the induced P-structure, and factor the restriction of g to Q over
   P. The tensor universal property then gives ψ and both identities. It neither
   assumes nor constructs a system. Extension instead takes i, ψ and their identities
   as inputs and performs no factorization; arbitrary P,Q and φ₀ are allowed. At j,
   its formula is b tensor q ↦ φⱼ(b) times the transition image of ψ(1 tensor q).
   Balancing follows from hψ. Associativity identifies both later rings as base changes
   over Bⱼ, which proves pushouts. The limit identity identifies the colimit map with
   the given e. Thus neither hole is a restatement of the original theorem. Tested
   singleton I, non-antisymmetric directed preorders, zero rings, empty presentations,
   nonbijective g in descent, and infinitely presented Q in extension. Empty I is
   excluded by the input i₀. No injectivity of transition maps is required.

   Independent searches used LeanFinder for compatible descent and scalar-extension
   systems, Loogle for `Algebra.TensorProduct.map`, and grep for pushout/colimit and
   finite-presentation/tensor combinations, as logged by `msearch.py`. Read the resulting
   Mathlib factorization, base-change, and categorical tensor-pushout declarations.
   Searches of `lean/Sheaf/RingTheory`, upstream `WeilConjectures/RingTheory`, and the
   DAG found no exact replacement. `ColimitCategoryFpAlgebras` additionally assumes
   finitely presented stage algebras; `FinitePresentationModelStage` imports this item
   and cannot be used without a cycle. The remaining categorical constructions cannot
   be closed by a short application of these declarations.

4. **Route and pruning — pass.** Read `dag/units/sk-thm-p1.json`, including `realized`;
   the comparison item is below its realized statements and steps, and the delivery
   changes none of them. The three new imports are proof-only. Public imports provide
   the unchanged tensor, ring-colimit, finite-presentation, filteredness and pushout
   vocabulary. The report now explicitly names both old direct dependencies moved into
   the new nodes. All five old dependencies remain used in the combined argument;
   no module is pruned. One original hole is closed and two are added: net −1 holes
   closed, a decomposition rather than a sorry-free proof.

5. **DAG agreement — pass.** Compared the original item node with the sandbox node:
   only `proof`, `proof_deps`, and `proof_origin` differ. The three steps match finite
   descent, extension, and the actual finite-presentation argument. Read each cited
   dependency's Lean or Mathlib match: factorization supplies a compatible algebra map,
   the elementwise lemma supplies representatives and eventual vanishing, tensor
   universality supplies the maps and their equality tests, and base-change/composition
   supplies the finiteness argument. Both new nodes have matching verbatim Lean
   signatures, complete proofs, source places, logged searches, creation records,
   chapter/unit and blueprint ancestry. Their dependency lists equal the union of
   their proof steps; no edge goes back to the item.

Changes made in this reading: added source and blueprint tags to the two new module
comments; corrected their author group to K1; replaced the inapplicable general
finite-algebra citation by the precise factorization/tensor-colimit citations;
expanded the extension docstring with the actual component formula; rendered the new
node statements in TeX without changing their meanings; removed the unused
finite-presentation definition dependency from the extension node; and clarified
moved dependencies and net hole accounting in this report. No proof body or existing
signature was changed. Final dry run printed OK: all modules compiled, axiom probes passed, and preflight
accepted the delivery as CODEX because it adds nodes and public declarations. Also
verified verbatim node signatures, exact proof-dependency unions, and the 100-character
Lean line limit.
