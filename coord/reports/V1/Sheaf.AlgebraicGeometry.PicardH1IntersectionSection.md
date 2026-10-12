## What changed

Replaced the entire proof of
`AlgebraicGeometry.Scheme.picard_h1_intersection_section`, preserving its signature and
public imports. The second reader also minimized the new module's public imports. Its proof now constructs the finite scheme-theoretic intersection by
induction, lifts the residue-field point through it, evaluates the Picard-locus universal
properties to obtain the descent hypotheses, applies a local section-lifting theorem,
and proves the ambient-open restriction and its universal factorization property.

The private, completely proved `finiteImmersionIntersection` helper uses Mathlib
pullbacks, their projection equations, and stability of immersions under base change
and composition. For the empty family it constructs S with its identity morphism.
Residue-field lifts use the completely proved source-library
`Scheme.exists_comp_eq_of_mem_range`, imported through
`WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`.

Added `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent`, containing the remaining
cohomological argument as one named public theorem with its source and full proof in
words. It assumes actual base descent of each target bundle and residue-field descent
of the original bundle. It concludes a section on an open of a given immersed base;
it has no Picard loci, no representing-intersection hypothesis, and no ambient-open
or universal-factorization conclusion. Thus it isolates steps 2--4 of the plan rather
than renaming the original statement. The original theorem supplies its descent
hypotheses and proves both geometric parts of the argument in Lean.

The module's previous proof imports are replaced by the new theorem's module and
the source-library point-lifting module. The perfect-direct-image and free-model inputs
stay in the new theorem's proof plan. Its minor step also uses the existing
`Module.finiteFreeMap_residue_localization` theorem; that module is imported there.
Updated the original DAG node to follow the compiled proof, and added the local
section-lifting node. No definition, existing signature, or target was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_h1_intersection_section`
(node `lem-sc-picard-h1-intersection-section`). No sorry remains in the item's module.
Its private finite-intersection helper is also completely proved.

Added one hole:
`AlgebraicGeometry.Scheme.picard_h1_local_section_of_base_descent`
(node `lem-sc-picard-h1-local-section-base-descent`) in the new module. Its proof is
exactly `:= by sorry`. This is a decomposition: one original hole closed, one strictly
smaller cohomological hole added, net zero holes. It is not a claim that the
cohomological lifting argument has been proved or that the result is axiom-closed.
The pre-existing holes in the imported perfect-complex inputs are unchanged.

The sandbox modules compile through lcompile.py. The induction checks n = 0 directly.
For the new statement, n = 0 forces the original H1 to vanish by hH; the rank-zero
minor case in its proof is therefore valid. Zero source rank needs no chosen minor.
No point is claimed on an empty immersed base: w is a hypothesis. Finite locally free
modules are not assumed rank one without justification; faithful flatness and descent
of invertibility establish this before the finite-free model argument.

## No longer needed

Removed from the item's direct proof imports:
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` and
`Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`, and the redundant direct
`Sheaf.AlgebraicGeometry.TensorPullback` import. Tensor pullback remains available
through the unchanged public statement imports.
The perfect-complex nodes `lem-pc-rf-perfect-base-change` and
`lem-sc-perfect-finite-free-residue-model` are no longer direct dependencies of the
original node, but remain needed by the new cohomological node and stay imported there.
They are not globally pruned. No module or node is claimed to leave the targets'
closure. The base-change conventions remain a public statement dependency of the existing module.
The second reader removed the new module's imports of PicardDiagonalLocallyClosed
and BaseChangeConventions, using the needed Mathlib geometric interfaces and
TensorPullbackAdjunction directly; the explicit Invertible import there was redundant
through Ample. These modules remain reachable elsewhere; none is globally pruned.
The source unit's route is retained; only the internal geometric/cohomological split
changes below it.

## Where the brief, the DAG or earlier work was wrong

The perfect-direct-image and finite-free-residue-model signatures alone do not supply
compatible chain maps between the fixed models, the degree-zero cohomology
identifications, or their relation to nonvanishing of the lifted section. The DAG's
step 4 marked the minor-and-generator-lifting argument elementary, but those
interfaces leave substantial cohomological glue. The new theorem explicitly owns
that remaining argument, including affine chain-map representation, the residue
comparisons, vanishing of the target differentials, and the section interpretation.

The local copies of `literature/stacks-project/more-morphisms.tex` and the unit's
blueprint source path named by the unit record are absent. The unit record was read;
the proof source was read at the official Stacks Project page
https://stacks.math.columbia.edu/tag/0BF2. This is the same Tag 0BF2 route, not a new
source or a replacement of the unit's argument. LeanFinder found only affine section
and spreading-out ingredients. Loogle found the immersion/pullback stability facts.
The Mathlib grep restricted to AlgebraicGeometry found no fibre-generator lifting
statement; repository grep found only the parent and this planned section-lifting item.
LeanSearch was unavailable with an Internal Server Error, recorded by msearch.py.

The earlier workers' dry runs failed because the delivery launcher imported a missing
`refuse_missing` from `tools/import_cycles.py`. This retry now succeeds through the
unmodified authorized launcher. No delivery-tool edit or workaround was attempted.

The resumed worker checked the original theorem signature byte for byte (unchanged),
the 100-character line limit (both modules pass), and the existing node changes
(only proof, proof_deps and proof_origin). The official Tag 0BF2 proof was reread,
including the chain-map and injective-minor argument. The authorized delivery dry run
compiled both modules and passed preflight, except for the second reading that the
independent reader must supply. Nothing was pushed.

## New nodes

`lem-sc-picard-h1-local-section-base-descent` is the cohomological step after replacing
the base by the intersection in Stacks Tag 0BF2. Its statement is independent of any
Picard loci and only produces a local section. Its proof records base-change and
residue-field transport, descent of invertibility and simultaneous trivialization,
perfect direct images, fixed finite-free models and chain maps, the injective minor
argument, and the identification of the zero-degree generator with a fibre-generating
section. The new module and node are in the sandbox under their usual Lean/DAG paths.
No change record or forced adaptation is needed.


## Second reading by V1

1. Interface check: PASS. Diffed both delivered modules and both node records against
   the repository. The existing theorem signature is byte-for-byte identical, its
   public imports unchanged, and there are no changed definitions or existing
   statements. The only changed existing node fields are proof, proof_deps, and
   proof_origin. The new module states its own section-lifting theorem.
2. Proof and axioms: PASS as a decomposition. Both modules compile using lcompile.py.
   The item has no sorry. The sole added sorry is exactly the named public theorem
   picard_h1_local_section_of_base_descent, with its complete proof docstring and node.
   Scratch-copy #print axioms checks give only propext, Classical.choice, Quot.sound
   for finiteImmersionIntersection, and those three plus sorryAx for the existing
   theorem and the new open theorem. No forbidden declarations or hollow data occur.
   The intersection is constructed by identity and actual pullbacks; no data are
   selected from the new unproved section theorem outside a propositional proof.
3. Split statement: PASS. Reread https://stacks.math.columbia.edu/tag/0BF2 and the
   imported perfect-model and minor statements. The new theorem is the cohomological
   argument on an already supplied immersed base, not the original intersection
   representation statement under another name. Its descent hypotheses follow by
   evaluating the original Picard-locus universal properties. Faithful flatness
   ensures that the finite locally free descended modules have rank one. For n=0,
   injectivity into the empty product forces H1 to vanish, so the degree-one source
   term is zero and no minor is needed. With W empty there is no w hypothesis; no
   unsupported nonempty point is produced. Over a field the hypothesis on L makes
   it trivial, so a fibre generator exists. Positive source rank with no targets
   cannot satisfy hH. Independent LeanFinder search for extension of a trivialization
   and Mathlib/repository searches using cohomology-lifting and fibre-triviality
   terms found no replacement. PicardH1LocalDescent is downstream of this item and
   cannot close the new theorem without a cycle. The remaining argument is too
   substantial to close in a few minutes.
4. Route and pruning: PASS after import repair. Read the unit record
   dag/units/sk-prop-av-cube.json, whose realized statement and step lists are empty;
   no realized route is bypassed or changed. The proof constructs the intersection,
   evaluates descent, invokes the isolated Tag 0BF2 cohomological step, and proves
   the ambient-open factorization equivalence. The old perfect-complex dependencies
   move to the new theorem, and def-pc-base-change stays a statement dependency.
   No longer needed lists every old direct dependency removed and explicitly claims
   no global pruning. Replaced the new module's unneeded Picard-locus and base-change
   wrapper imports by their actual statement interfaces; removed its redundant
   direct Invertible import. The existing module's public interface stays intact.
5. DAG agreement: PASS. The old node describes the induction, residue-field lift,
   Picard-property evaluation, local-section invocation and ambient-open lift that
   the Lean code executes. The new node has its source, statement dependencies,
   six-step proof and their dependency union, proof_origin, searches, split status,
   creation and blueprint records, chapter/unit, and verbatim Lean statement.

Second-reading changes: minimized the new module's imports and added this independent
review. No theorem signature, proof body, definition, or node statement changed.
The delivery closes one original hole and adds one strictly smaller hole: net zero,
with no axiom-closed proof or globally pruned module claimed.
