## What changed

Completed the earlier attempt's Lean assembly in
`Sheaf.AlgebraicGeometry.PerfectJumpLoci`, with the signature and public imports of
`AlgebraicGeometry.Scheme.pseudoCoherent_jump_loci` unchanged. The proof constructs
local strict sublevel opens and constructible level sets from the finite-free homology
theorem, glues openness through open subtype inclusions, and proves base-change
invariance using a fibre-cohomology isomorphism and `Module.finrank_baseChange`.

The delivery includes two new modules, each containing one strictly intermediate
statement: `PseudoCoherentFiberFiniteFreeModel` supplies a bounded algebraic complex
computing just one fibre-cohomology degree on a neighbourhood; and
`DerivedFiberCohomologyBaseChange` identifies fibre cohomology with scalar extension.
Neither asserts semicontinuity or constructibility. Added their missing DAG records
and updated the parent's proof, proof dependencies and proof origin to agree with
its Lean proof. No definition, existing statement, target or public visibility changed.

Validation: all three sandbox modules compile in import order using `lcompile.py --all`.
The finite-free homology theorem in the current repository is already proved.
The existing perfect/minimal-residue-model lemmas require perfectness and only control
a stalk or its prescribed ranks; they do not give the affine uniform model needed here
for an arbitrary pseudo-coherent complex. The K-flat stalk comparison concerns one
point and does not itself supply either new statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.pseudoCoherent_jump_loci`
(node `lem-sc-perfect-jump-loci`). No sorry remains in the item module.

Added two holes, each a whole named public theorem with a source and complete
natural-language proof:

- `AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_finiteFree_model`
  (`lem-sc-pseudo-coherent-fiber-finite-free-model`), in
  `Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel`.
- `AlgebraicGeometry.Scheme.derivedFiberCohomology_baseChange_iso`
  (`lem-sc-derived-fiber-cohomology-base-change`), in
  `Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange`.

This is a decomposition: one upper hole closed and two lower holes added, net -1,
not an unconditional sorry-free proof. Existing dependency holes are not newly added.
There are no holes inside definitions and no definitions choosing arbitrary witnesses.
The model is eliminated inside a proposition proof only.

Checked edge cases: the empty scheme gives no local points; the zero complex and
degrees above its bound give a zero model; ranks zero use the difference of the
threshold-one and threshold-zero opens; integer thresholds allow negative degrees
without identifying them with natural degrees. Arbitrary base change need not be flat:
only the residue-field extension is flat. The cohomology isomorphism also covers
infinite-dimensional vector spaces, and Mathlib's finrank base-change lemma uses no
finite-dimensionality assumption over a field. No Noetherian hypothesis is used:
compactness comes from the finite-free minors calculation on the affine spectrum.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback` from the item. Its node
`lem-pc-flat-complex-derived-pullback` remains needed below the new local-model node,
and that module imports it. Thus this removes an immediate dependency only, not the
module from the transitive closure. The parent's direct dependency on
`def-pur-pseudo-coherent-complex` is replaced in its proof route by the local-model
node; the definition remains a statement dependency and a public import.

The second reader also removed the new base-change helper's private import of
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`, replacing its planned use with
K-flat resolution and K-flat pullback preservation. No claim is made that the
composition module is pruned from the targets' transitive closure.

No existing module or node is claimed pruned from the targets' transitive closure.
The finite-free homology module remains needed. The minimal perfect model, stable-free
lifting, and other perfect-model routes were not added: the argument needs no prescribed
term ranks, minimality or uniqueness of a representative. All newly added imports in
the item are used by its proof, including `Mathlib.LinearAlgebra.Dimension.Constructions`.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had the three Lean files but no node records or report, so it was
not a reviewable delivery. Its assembly compiles on the current compiled library; this
attempt checked its signatures, sources and edge cases and supplied the missing records.

The old proof plan's pseudo-coherence definition gives a sheaf complex, whereas the
finite-free homology theorem accepts an algebraic complex over a ring. The affine
restriction, scalar identifications and one-degree truncation are genuine missing glue,
now isolated in the first new statement. The bounded-above flat comparison alone also
does not state the arbitrary fibre-cohomology scalar-extension isomorphism, now isolated
in the second. The existing derived-pullback composition declaration packages a global
family of derived-category instances. The second reader replaced that dependency
with the K-flat resolution, pullback preservation, ordinary tensor-pullback composition
and recorded counits, which require only the local instances in the original theorem.

The source text `literature/stacks-project/perfect.tex` is not present on this machine;
the source was read at https://stacks.math.columbia.edu/tag/0BDI and
https://stacks.math.columbia.edu/tag/06YJ. LeanSearch was unavailable (Internal Server
Error), recorded in searches.jsonl; LeanFinder, Loogle and grep were available. Searches
of the imported blueprint and of both Lean roots found no exact replacement for the two
new statements. The cube unit's statement and steps are preserved.

## New nodes

`lem-sc-pseudo-coherent-fiber-finite-free-model`, in
`dag/nodes/sec-abelian-varieties/`, records the local bounded finite-free model computing
one fixed degree, following Tag 0BDI's affine reduction and stupid truncation. It keeps
pseudo-coherence and flat-complex derived pullback as its proof dependencies, and records
the earlier attempt's actual search queries and results. Its new module is
`lean/Sheaf/AlgebraicGeometry/PseudoCoherentFiberFiniteFreeModel.lean`.

`lem-sc-derived-fiber-cohomology-base-change`, in the same node directory, records
scalar extension of derived-fibre cohomology, following Tag 0BDI's first proof paragraph
and Tag 06YJ. It uses the composition comparison and the derived-fibre definition,
records the actual search queries, and has new module
`lean/Sheaf/AlgebraicGeometry/DerivedFiberCohomologyBaseChange.lean`.

Both nodes inherit chapter `sec-abelian-varieties` and unit `sk-prop-av-cube`, and point
back to `thm-sc-theorem-of-cube` through the jump-loci route. No change record is required:
no existing interface was changed and there are no forced adaptations.

## Second reading by U4

1. Interface: compared the entire item with the repository by diff and extracted the
   theorem signature before `:= by`; it is byte-for-byte identical. Only its proof
   and private proof imports changed. Both other modules are new and define no data.
   No existing target, definition, signature or public import was changed. PASS.
2. Kernel checks: compiled all three modules with lcompile.py in import order.
   Scratch copies with #print axioms for all three public declarations show only
   propext, Classical.choice, Quot.sound and sorryAx. The item's proof has no sorry;
   exactly the two reported named helper theorems have whole-proof sorries. No axiom,
   unsafe, opaque, extern, implemented_by, hollow definition or arbitrary data choice.
   PASS as a decomposition, not as an unconditional proof; net holes closed minus
   added is -1.
3. New statements: read Stacks Tags 0BDI and 06YJ and both docstring arguments.
   The local model computes only fixed H^i, truncating below i-1, rather than claiming
   E itself is bounded. The base-change isomorphism needs no pseudo-coherence: scalar
   extension between residue fields is exact even for unbounded complexes. Checked
   zero ranks, threshold zero, negative degrees, an upper bound below i-1, empty
   schemes, and nonflat g. Choosing the model occurs only inside a proposition proof.
   Repeated LeanFinder, Loogle and grep searches with affine sections and exact
   homology queries; inspected AffineFiniteFreeSheafComplexLift,
   AffinePseudoCoherentPrincipalSheafModel, KFlatStalkResidueCohomology,
   AffineTensorPullbackHomologyComparison and the perfect residue-model routes.
   None replaces either helper. The existing affine lift is a genuine reusable
   part and is now cited instead of reproved in the model plan. PASS.
4. Route and pruning: read all branches of the assembly. Local sublevel openness
   transfers through the chart, global openness through the open subtype inclusion;
   compact opens on PrimeSpectrum give constructible differences at r+1 and r,
   including r=0, without Noetherianity. Module.finrank_baseChange closes dimensions.
   The old immediate proof dependencies no longer used are exactly
   def-pur-pseudo-coherent-complex and lem-pc-flat-complex-derived-pullback, already
   listed above; both remain below the model helper. No transitive pruning claimed.
   Read dag/units/sk-prop-av-cube.json: its existing realized statement and step arrays
   are empty; this delivery does not alter them or bypass its general-cube route.
   All public imports in the new modules supply symbols of their signatures;
   added geometric/helper imports are private proof imports. PASS.
5. DAG: the item changes only proof, proof_deps and proof_origin. Each new node has
   its exact Lean signature, source, full proof plan, dependency union, searches,
   creation record, blueprint ancestry, chapter and unit. Repaired the local-model
   plan to use lem-pc-affine-finite-free-sheaf-complex-lift. Repaired the base-change
   plan to use local K-flat computations: the packaged composition theorem's global
   instance-family hypothesis cannot be supplied from this helper's local instances.
   The replacement uses K-flat resolution/pullback preservation and the ordinary
   tensor-pullback composition; it does not add a hypothesis. PASS.

Changes by this reader: updated the two helper docstrings, proof imports and DAG
plans to reuse the affine lift and to use local K-flat base-change computation;
recorded independent searches and this review. No theorem signature changed and
no additional hole was added or closed. The remaining geometric transport work
cannot be closed by a short direct application of the inspected declarations.
