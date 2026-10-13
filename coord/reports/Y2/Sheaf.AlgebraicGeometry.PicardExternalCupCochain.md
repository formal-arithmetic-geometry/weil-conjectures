## What changed

Repair of the returned delivery: removed the private `inverseImage_linear` theorem,
which duplicated a private theorem in `Sheaf.AlgebraicGeometry.ExternalCupScalarBalance`.
That declaration is private, so importing its module cannot expose it. Instead the
pullback proof directly uses the existing public
`CategoryTheory.Adjunction.left_adjoint_linear` theorem, with a sectionwise linear
pushforward instance. Added its proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`.
There is no replacement theorem asserting the duplicated statement and no edit to
another group's module. The public interface and main proof are preserved.


Completed `AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_exists` in
`Sheaf.AlgebraicGeometry.PicardExternalCupCochain`, with every existing signature,
definition and visibility preserved. The earlier sandbox attempt supplied a compiling
private graded-homology lifting lemma but left the main theorem unfinished.

Used Mathlib’s bilinear Yoneda composition and the source library’s
`CategoryTheory.Adjunction.left_adjoint_linear`, with private helpers for
linear promotion of the additive scalar cohomology/Ext comparison, projection pullbacks,
and the cup pairing. Constructed the graded total-homology map using
`HomologicalComplex.tensor_kunneth_nat`, `TensorProduct.lift`, and `DirectSum.toModule`.
Lifted it to a cochain map and proved the exact normalization by the Kunneth cycle formula
and injectivity of `iCycles`. Negative graded maps are zero. No geometric Kunneth
invertibility, compactness, affine diagonal, finite dimension or nonempty scheme is used.

The existing proof-only import `Sheaf.Algebra.Homology.TensorKunnethNat` is used.
The second reading removed the redundant new imports
`Mathlib.LinearAlgebra.Basis.VectorSpace` and `Mathlib.Algebra.Module.Projective`,
which are already available through existing public imports.
All newly introduced helper instances are private and local.
Updated the existing node's proof and proof origin to record the implemented argument;
its proof dependency set is unchanged. No new modules or interface adaptations.

The first worker reported clean compilation in 49.9 seconds.
The second reading independently checks the revised module and its axioms below.
All delivered Lean lines have at most 100 characters. The generic linear-promotion
existence theorem is fully proved: no construction selects data from a new holed
existence theorem.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_exists`
(node `lem-sc-picard-external-cup-cochain`). All private helper declarations are proved.

Holes closed: 1. Holes added: 0. Sorries left in the delivered module: none.
This is a complete proof from the recorded existing dependencies, not a decomposition
into new holed statements. The existing scalar cohomology/Ext and tensor exactness
lemmas remain dependencies for subsequent stage-3 work.

## No longer needed

The duplicated private `inverseImage_linear` declaration is removed. Its sole call
site now applies the existing public adjunction theorem directly; there is no need
to import `Sheaf.AlgebraicGeometry.ExternalCupScalarBalance` or prove its private
helper again. This removes a duplicate helper, not an original DAG dependency.


No original imports, nodes or modules are pruned. The second reading removed two
redundant imports added by the first worker: `Mathlib.LinearAlgebra.Basis.VectorSpace`
and `Mathlib.Algebra.Module.Projective`. All three recorded proof-dependency nodes remain used:
`def-sc-field-linear-module-cohomology-operations`,
`lem-sc-picard-kunneth-resolution-model`, and
`lem-sc-qcoh-cech-total-tensor-nat-iso`. No original imports, nodes or modules are pruned.
The generic linear-algebra lifting is proved locally and needs no new dependency item.
The duplicated private `extCompose` definition was removed in favor of Mathlib’s
`CategoryTheory.Abelian.Ext.bilinearCompOfLinear`.

## Where the brief, the DAG or earlier work was wrong

The landing check correctly identified the earlier private `inverseImage_linear`
as a duplicate. The named matching theorem is private in its defining module;
therefore the repair reuses the underlying public adjunction theorem from the
source library instead. The earlier second-reading section below describes the
pre-return delivery and is retained as history for the next independent reader.


No statement or DAG error found. The second reader found Mathlib’s bilinear Ext
composition that the first worker had duplicated privately; the revised proof uses it. The earlier attempt's graded lifting helper was sound
and compiled, but its bilinearity scratch file did not compile and the main theorem had
not been completed. Directly building a concrete Ext linear equivalence was expensive:
the kernel unfolded the concrete Ext scalar action to compare multiplication by a scalar
with multiplication by its image under `RingHom.id`. Proving linear promotion for
abstract modules first, and specializing its proved existence and evaluation formulas,
keeps the derived-category action folded and lets the complete module compile within
the file limit. This is an implementation correction, with no changed definition or
statement and no extra axioms.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: pass.** Read the complete repository/sandbox diff and
   checked it with `stage3_delivery.diff_module`: no interface, statement,
   visibility, public-import, or existing-definition change. The types and bodies
   of `picardExternalTotal` and `IsPicardExternalCupCochain` are unchanged, as is
   the complete signature of `picardExternalCupCochain_exists`. In particular the
   field, arbitrary schemes over its spectrum, and both quasi-coherence
   hypotheses are retained. The conclusion still quantifies over every specified
   tensor cycle, with the same degree cast and externalCup normalization.
   No change record is required.
2. **Proof and axioms: pass.** Compiled the revised complete source in a scratch
   copy with explicit `#print axioms` for `picardExternalCupCochain_exists`,
   `lift_graded_homology`, and `externalCup_bilinear`: clean, 53.3 seconds.
   The lifting helper uses only `propext`, `Classical.choice`, and `Quot.sound`.
   The other two additionally use `sorryAx` through existing open dependencies.
   There is no delivered `sorry`, forbidden declaration, or hollow definition.
   The source projection extends homologyπ along the injective cycle inclusion;
   it kills differentials by `toCycles_comp_homologyπ`. The target section splits
   the surjective homologyπ, and its cycle inclusion kills outgoing differentials.
   Naturality and epi cancellation give the prescribed homology map. All newly
   chosen witnesses come from proved helpers, or comparisons characterized on
   every input/tensor generator; no arbitrary data is selected from mere unproved
   existence. The final arbitrary z is identified by injectivity of iCycles.
3. **Split statements and searches: pass.** No split-off statements, new modules,
   or new nodes. Read every private helper: scalar comparison promotion uses
   AddEquiv.toLinearEquiv, inverse image uses the linear right-adjoint criterion,
   and the two projection maps use the correct commutative-square orientation.
   Bilinearity is transported by exact-functor maps on Ext and Yoneda composition.
   Checked zero vector spaces, zero sheaves, empty schemes, degree zero (only
   (0,0)), and negative degrees (the assigned zero homology map): none requires
   a finite-dimensional, nonempty, or compactness hypothesis. Independent
   LeanFinder search for fullness of homology produced no replacement for the
   field-linear lifting argument. Loogle and source grep found Mathlib's
   `CategoryTheory.Abelian.Ext.bilinearCompOfLinear`, which replaces `extCompose`.
4. **Top-down route and pruning: pass after cleanup.** The proof constructs the
   homology pairing from the existing externalCup, applies the recorded natural
   Kunneth cycle formula, and then lifts to a cochain map. All three original
   proof dependencies remain genuinely used. `## No longer needed` records every
   removal. Removed the two redundant new Mathlib imports; their declarations
   are already public-transitive dependencies of the original imports. No
   original import or dependency node is removed. Read `sk-prop-av-cube.json`:
   its `realized` entries are empty in the baseline and remain untouched; this
   below-unit construction changes no unit statement or step, and bypasses none.
5. **DAG agreement: pass after cleanup.** Compared the node JSON with the
   repository: only `proof` and `proof_origin` change; `proof_deps` remains the
   union of the steps' uses. Read the three dependency nodes and checked their
   recorded Lean declarations against the imported source. The node's first
   step now names Mathlib's bilinear composition rather than a private duplicate;
   its other steps match the direct-sum map, degree cast, zero negative map,
   vector-space lifting, and cycle normalization in Lean. No new-node fields
   or statement changes arise.

Second-reading changes: removed the private duplicate `extCompose`, used
`Abelian.Ext.bilinearCompOfLinear` at its five call sites, removed the redundant
new VectorSpace and Projective imports, wrapped the resulting long line, and
updated the node's proof text and this report. Holes closed remain 1, holes added
0, split off 0. No mathematical repair or interface change was necessary.

## Second reading by Y2

1. **Interface: pass.** Independently read the entire source diff and ran
   `stage3_delivery.diff_module`: no changed existing signature, definition,
   visibility, or public import. Only the original theorem body, private proved
   helpers, and one proof-only import are added. No statement change or change
   record is needed.
2. **Proof: pass.** Independently compiled the delivered source cleanly in 46.4 s.
   A separate scratch copy with explicit `#print axioms` compiled in 54.7 s:
   `lift_graded_homology` uses only propext, Classical.choice and Quot.sound;
   the main theorem, externalCup_bilinear and pullbackLinear_exists additionally
   use sorryAx from existing imported open results. No delivered sorry, forbidden
   declaration or hollow definition occurs. Read the lifting proof: the source
   extension kills boundaries, the target section lands in cycles, and epi
   cancellation identifies the homology map. Witnesses of the newly proved
   existence helpers are justified by complete proofs. The imported Kunneth
   equivalence is characterized on tensor generators; its formula determines
   the map since homology projections are surjective and generators span.
3. **Split statements: pass, none.** No new holed statement or new node is added.
   Independently checked the linear comparison, pullback, cup and lifting helpers.
   Zero vector spaces/sheaves, empty schemes, degree zero and negative integer
   degrees introduce no missing assumption. A fresh Loogle search confirms the
   Mathlib bilinear Ext composition already used. Source grep confirms the public
   adjunction theorem used directly by the repaired pullback proof.
4. **Route and pruning: pass.** Read the proof from the normalization conclusion
   through the tensor cycle formula, direct-sum pairing and vector-space lifting.
   All original proof dependencies are genuinely used. No original import or node
   is dropped; the sole added import is proof-only. The unit sk-prop-av-cube has
   empty realized entries in the baseline; the delivery neither alters these nor
   bypasses a realized unit step. The report lists the earlier redundant helper
   and import removals. No further pruning or rewriting was justified.
5. **Nodes: pass.** The node diff changes only proof and proof_origin; its unchanged
   proof_deps is exactly the union of uses. The three implemented steps agree
   with the Lean code, including direct application of left_adjoint_linear,
   natural-degree transport, zero negative maps and cycle injectivity. No new
   node requirements arise.

Changes in this second reading: appended this independent review only; no Lean
or DAG repair was needed. Closed 1 original hole, added 0 holes, split off 0;
no original dependency was pruned. The main theorem remains conditional on the
existing open imported results, as its explicit axiom output records.
