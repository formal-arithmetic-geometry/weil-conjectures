## What changed

Replaced the sole sorry in
`AlgebraicGeometry.finitePresentation_zero_map_affine_open_eventually` with a
compiled finite-generator argument. Its existing signature and both public imports
are unchanged. New proof imports are
`Sheaf.AlgebraicGeometry.AffineFiniteTypePullbackZeroTest`,
`Sheaf.AlgebraicGeometry.FinitePresentationSectionAffineOpenVanishing`,
`Mathlib.AlgebraicGeometry.Morphisms.Affine`, and `Mathlib.Data.Finset.Order`.

The proof makes the inverse image of U affine, chooses a finite testing family,
uses unit naturality to show that each image vanishes at the limit, applies
one-section descent, and takes a common upper bound. The finite test then proves
vanishing on every requested subopen. The first projection identity for
`baseChangeMap` identifies the opens without changing the statement.

The new finite-test module has a complete proof. It uses the already proved private
`finite_sections_of_finiteType` through
`import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`, obtains a finite
spanning set, shows that the kernel of the section map contains its span, and uses
`exists_tensorPullback_affine_sections` and tensor induction. A covering sieve of
affine subopens and separatedness give the result on arbitrary subopens.
Its proof-only imports expose no additional declarations to other modules.

The new one-section module states the remaining affine algebra descent, with a
complete source-based proof in its docstring and a matching DAG node. It accepts
supplied pullback/pushforward adjunctions, avoiding repeated elaboration of the
large canonical tensor construction. Uniqueness of adjoints identifies their
units with the canonical units by an invertible natural transformation, so the
zero condition is unchanged. No new definition or arbitrary chosen datum is added.

## Proved and sorry left

Hole closed in the assigned module:
`AlgebraicGeometry.finitePresentation_zero_map_affine_open_eventually`
(node `lem-pc-fp-zero-map-affine-open-eventually`). This is a decomposition, not a
sorry-free proof of the full target closure.

New theorem proved:
`AlgebraicGeometry.Scheme.Modules.exists_affine_finiteType_pullback_zero_test`
(node `lem-pc-affine-finite-type-pullback-zero-test`). It has no sorry in its body.
The pre-existing affine pullback comparison remains a proof dependency.

The only sorry left in the delivery is the named public theorem
`AlgebraicGeometry.finitePresentation_section_affine_open_eventually_zero`
(node `lem-pc-fp-section-affine-open-eventually-zero`). Its entire proof is
`:= by sorry`. It concerns one section, with a bound depending on that section;
it has neither a finite source module nor a morphism between two modules.
Combining its section-dependent bounds into a uniform bound for a morphism is
proved in the assigned module.

Counts: one original hole closed; one new hole added; net zero. No sorry remains
in the assigned module. All three modules have been compiled locally with
`lcompile.py`; the final delivery check is the required `deliver3.py --no-push`.

## No longer needed

No existing import was removed: the original public imports are needed by the
unchanged signature. No whole module is claimed as pruned. The new section module
imports only `PicardFunctor`, `TensorPullback`, and Mathlib's quasi-coherence
interface; it does not need the full `BaseChangeConventions` or the canonical
`TensorPullbackAdjunction` theorem in its statement.

The planned direct proof dependency
`lem-pc-module-pullback-identity-composition` is no longer needed by this route:
vanishing of each section is asserted at every sufficiently late stage, and the
main proof uses only unit naturality and the finite test. Neither new module uses
the identity/composition theorems. `Sheaf.AlgebraicGeometry.TensorPullback` itself
remains necessary for the tensor-pullback definition and its adjunction.

The original direct dependencies
`lem-weil-pbc-quasi-coherent-finite-type-affine` and
`lem-weil-pbc-module-pullback-affine-sections` are still needed below the new
statements; they have been moved to the appropriate new node rather than pruned.
`lem-pc-filtered-colimit-commrings-elementwise` is replaced as a direct dependency
by the existing proved `lem-weil-pbc-directed-colimit-base-change-elementwise`;
the latter still uses the same Mathlib elementwise ring-colimit results. The
finite-presentation matrix route is no longer needed.
`lem-weil-pbc-spec-colimit-limit` is no longer a direct dependency of the main
proof: affineness uses Mathlib's affine-morphism base-change instance, not the
Spec-colimit-limit theorem. It remains part of the one-section descent plan.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface change. The unit record
`dag/units/sk-thm-picard-semicon.json` has empty realization lists; no realized
unit statement or proof step was bypassed. The affine comparison and affine
finite-type criterion are generic tools already used by the assigned node's plan.

Affineness of the pullback projection needs an explicit local instance obtained
from `MorphismProperty.pullback_fst`; Mathlib does not synthesize it automatically.

The local repository does not contain `literature/stacks-project/limits.tex` or
`algebra.tex`. The cited canonical Stacks pages were read, and the corresponding
upstream TeX documents were fetched read-only into this item's scratchpad.
The first proof of Tag 01ZR refers to Algebra Tag 05N7. The existing proved
`TensorProduct.directedColimitBaseChangeElementwise` in
`Sheaf.Paper.DirectedColimitBaseChangeElementwise` supplies the tensor-element
step directly for preorder indices. The remaining node's proof now uses it instead
of the original finite-matrix construction, following
`lemma-module-map-property-in-colimit` (Tag 05LI). Its remaining work is the affine
ring-limit and unit/section comparisons. No unsourced theorem was introduced.

LeanSearch returned Internal Server Error and is recorded as unavailable.
LeanFinder, Loogle, Mathlib grep, and searches in both library roots were run;
there was no complete existing module-section descent theorem. The blueprint
searches for the two new statements returned no matching nodes. The blueprint
ancestor command returned None because `created.item` contains a module name;
the new nodes retain the explicit ancestor recorded on the assigned node,
`lem-pc-rf-perfect-base-change`, with the intermediate-node chain.

## New nodes

`lem-pc-affine-finite-type-pullback-zero-test`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-finite-type-pullback-zero-test.json`,
records the proved generic finite-section test. Its new module is
`Sheaf.AlgebraicGeometry.AffineFiniteTypePullbackZeroTest`. It involves no inverse
limit or eventual-stage conclusion and is strictly the finite-generation/sheaf
part of the original argument.

`lem-pc-fp-section-affine-open-eventually-zero`, in
`dag/nodes/sec-picard-framework/lem-pc-fp-section-affine-open-eventually-zero.json`,
records the one remaining hole. Its new module is
`Sheaf.AlgebraicGeometry.FinitePresentationSectionAffineOpenVanishing`. Its
statement handles a single target section; the main proof supplies the genuinely
additional finite-family and common-bound argument. Both nodes inherit the item's
chapter and unit, record actual searches, and cover empty opens, zero modules,
and singleton directed preorders in their proof descriptions.

No change record or forced adaptation is needed.

## Second reading by W4

1. Compared the delivered main module with the repository version. The target
signature is byte-for-byte unchanged; only proof imports and the proof body changed.
The two new modules and their node statements match their Lean declarations.
Verdict: pass.

2. Compiled all three delivered modules with `lcompile.py --all`. The main theorem
has no `sorry`; the only remaining `sorry` is the named one-section theorem, with a
matching split node. Explicit `#print axioms` checks show only `propext`,
`Classical.choice`, and `Quot.sound` for the finite test, and additionally
`sorryAx` for the main and one-section theorems, as expected.
No forbidden declarations or hollow definitions were found.
Verdict: pass.

3. Checked the finite-test and one-section statements against their source arguments
and edge cases (empty opens, zero modules, singleton directed preorders). The
finite-test statement is strictly the finite-generation reduction and the
one-section statement is strictly section-level; neither restates the target.
Verdict: pass.

4. Checked proof dependencies and imports. The proof follows the finite-generator,
unit-naturality, common-bound route, and removes no needed public import. The
identity/composition dependency and finite-matrix route are no longer used and are
reported above. Verdict: pass.

5. Checked the DAG nodes, declarations, proof origins, and unit record. The unit has
no realized route that is bypassed; node proofs and dependencies agree with the
Lean proof and the split-off theorem. Verdict: pass.

Changed during second reading: removed the unused direct
`lem-weil-pbc-spec-colimit-limit` dependency from the main node and corrected the
pruning report. No Lean statements or proofs required repair. Independent
LeanFinder, Loogle, Mathlib grep, and library searches found structure-sheaf
vanishing and tensor-element results, but no replacement for the split-off
module-section descent theorem.
