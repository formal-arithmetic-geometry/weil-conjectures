## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_comparison_isIso`
with a complete Lean proof from one new local section lemma and the existing statements.
The signature is unchanged. First prove the unit comparison invertible by forgetting to
abelian sheaves and detecting it on the affine basis. Then prove
`β.app (R.obj F) ≫ R.map (α.app F) = 𝟙 _` by naturality of the adjunction Hom equivalence
and `homEquiv(counit) = id`. Scalar restriction does not change underlying maps, so the
identity holds as an A-module map. Cancel the invertible unit and evaluate on the affine
preimage cover to detect the counit as an isomorphism.

The quasi-coherence of the structure algebra is proved directly by qcqs pushforward of
the quasi-coherent unit module; no relative-spectrum equivalence is imported. The node
proof and dependencies now record this argument. Proof imports for affine pullback sections
and algebra change of rings move to the new local section module. Added proof imports:
`Sheaf.AlgebraicGeometry.AffineModuleTensorUnitSections`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`,
`Mathlib.Topology.Sheaves.SheafCondition.Sites`, and
`Mathlib.AlgebraicGeometry.Morphisms.Separated`.

Both modules compiled without errors or warnings through lcompile.py --all. The first
dry run required a change record for the declaration-scoped heartbeat option; the record
lists the unchanged signature and all transitive users. A tactic-local setting did not
raise the outer declaration budget.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_comparison_isIso`
(node `lem-weil-pbc-affine-module-tensor-comparison-isIso`).

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_unit_sections_bijective`
(node `lem-weil-pbc-affine-module-tensor-unit-sections`). Its proof is exactly `by sorry`.
There are no sorries in the item's module. This is a decomposition (one hole closed,
one strictly local hole added), not a claim of a sorry-free mathematical proof or positive
net hole reduction. Existing imported quasi-coherence and affine-cover theorems remain
as dependencies; their proofs were not changed.

The new statement concerns only one quasi-coherent algebra module and one affine open,
with no counit comparison α. It does not repackage the original conjunction: the original
module supplies the basis argument, quasi-coherence of RF, the adjunction identity,
cancellation, and the source-cover argument in actual Lean.

## No longer needed

The parent module no longer directly imports:
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`;
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings`.

The corresponding old direct proof dependencies are
`lem-weil-pbc-module-pullback-affine-sections` and
`lem-weil-pbc-quasi-coherent-algebra-change-of-rings`.
These are still needed in the new local section lemma, so neither is claimed as a module
pruned from the target closure. Their nodes leave the parent's direct proof dependencies
and occur beneath the new node instead. The original plan's separate counit-section tensor
calculation (step 4) is unnecessary: adjunction naturality and invertibility of β determine
it. No existing whole module is claimed pruned from the target closure. No unit statement
or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan marked the tensor balancing calculation elementary but its identification
with the actual sheafified comparison requires substantial canonical section bookkeeping.
The existing affine-section and change-of-rings statements do not themselves identify β;
this strictly local gap is now named. The source Tag 01SB explicitly omits the details of
the key algebra observation. Read its online primary-source statement and proof at
https://stacks.math.columbia.edu/tag/01SB; the local literature/stacks-project/morphisms.tex
file is absent on this machine. WANTED: Stacks Project morphisms.tex, Tag 01SB,
lemma-affine-equivalence-modules, for the new unit-section node. The expanded proof is
marked agent-written, not a quotation of unavailable local text.

The blueprint ancestor script returns None for this imported chain, although the parent
already records thm-weil-pbc-finite-etale-lifting as its ancestor. The new node preserves
that recorded ancestor and prepends the parent to the via chain. Searches for 01SB and
'affine modules' found no blueprint duplicate. Mathlib searches ran through msearch:
LeanSearch returned Internal Server Error; LeanFinder found generic pushforward section
and sheafification equivalences, not this affine unit calculation; grep found algebraic
tensor cancellation and basis detection, neither an exact match.

Edge cases checked for the local calculation: f=id gives the usual scalar-unit tensor
identity; the zero module and the empty affine open give zero section groups; arbitrary
(nonflat) D→C is allowed because the inverse uses balancing, not flatness. No nonempty,
finiteness, or flatness hypothesis is introduced.

## New nodes

`lem-weil-pbc-affine-module-tensor-unit-sections`, in
`dag/nodes/sec-proper-base-change/`, records the bijectivity of β on one affine base open.
Its module is `Sheaf.AlgebraicGeometry.AffineModuleTensorUnitSections`. It isolates the
canonical affine section identifications and the balanced inverse calculation, with the
source, actual three search results, full proof in words, and exact Lean signature. The
remaining worker must formalize those section identifications; no arbitrary witness data
has been chosen from an unproved existence theorem in this delivery. The change record
`coord/changes/affine-module-tensor-comparison-heartbeats.md` records the declaration-scoped
proof elaboration budget. No existing statement or definition changed.

## Second reading by X2

1. I diffed the existing module against the repository version and confirmed the other module
is new. The original comparison theorem's
signature is unchanged byte-for-byte; the only existing-declaration change is its proof and
an explicitly recorded declaration-scoped heartbeat option. The added theorem is a separate
strictly local affine-section reduction, with its own node and source.

2. Both modules compile through `lcompile.py --all` without warnings. The axiom probe reports
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` inherited from the listed open
proof dependencies. There are no `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions.
The sole remaining sorry is exactly
`affine_module_tensor_unit_sections_bijective`, and it is named in the report and DAG node.

3. I read Stacks Tag 01SB at https://stacks.math.columbia.edu/tag/01SB, including the
quasi-inverse, canonical unit, and final algebra identity. I searched the repository and
Mathlib-facing search tools for an existing affine tensor-unit
section theorem. The closest result is Mathlib's generic
`TensorProduct.cancelBaseChange`, which does not provide the sheaf section identifications;
no existing declaration duplicates the new statement. The new node's statement is a proper
part of the target: it concerns one beta section on one affine open and does not assert either
comparison family or the counit result.

4. The proof follows the recorded route. The beta part is detected on the affine basis and
uses the new section lemma. The counit part uses the adjunction triangle, naturality of the
Hom equivalence, quasi-coherence, and affine-cover detection. The tensor calculation in the
new node explicitly identifies the inverse on pure tensors as `c ⊗ (d ⊗ n) ↦ (cd)n`, checks
both balancing relations, and extends by tensor induction; its edge cases include the zero
module and empty affine open. No unit statement or realized unit step is bypassed.

5. I checked imports and DAG proof dependencies against the actual proof. The parent no longer
needs the former direct affine-section and change-of-rings imports because those are confined
to the new reduction module; the new module imports them directly. The unit route remains
recorded, and the added change record documents the only non-proof interface setting.

Changed during second reading: expanded the new lemma's docstring to specify the action of
`a ⊗ b` on both tensor factors and both balancing equalities explicitly. No Lean proof or
statement changes were necessary. Added this review section and verified the delivery checks.
