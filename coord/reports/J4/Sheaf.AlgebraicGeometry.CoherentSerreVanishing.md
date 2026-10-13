## What changed

Replaced the first worker's restatement by a genuine geometric and arithmetic reduction in
`Sheaf.AlgebraicGeometry.CoherentSerreVanishing`. Its existing signature is unchanged. The
proof derives finite presentation from finite affine sections over Noetherian rings, obtains
an immersion from absolute ampleness, makes it closed using properness, transports the
positive tensor power to the usual pullback, and combines finitely many residue-class bounds
using tensor-power isomorphisms and functoriality of module cohomology.

Added `Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing`, containing the smaller
restricted-twist vanishing theorem. Removed the first worker's `CoherentSerreVanishingCore`,
its two malformed node files, duplicate core import, and unproved finite-presentation helper.
No definition, existing signature, target statement, or existing public import changed.
All new proof imports in the existing module are plain `import`.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_isZero_moduleCohomology_tensorPow_of_ample`
(node `lem-weil-pbc-coherent-serre-vanishing`). The original module now has no `sorry`.

Hole added and left:
`AlgebraicGeometry.Scheme.Modules.exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion`
(node `lem-weil-pbc-closed-immersion-serre-vanishing`). This is a decomposition, not an
axiom-free proof: one upper hole closed, one strictly smaller hole added, net zero holes.
The smaller hole contains projective-space vanishing and the closed-immersion cohomology and
projection-formula comparison. It contains neither the ample-embedding step nor the
residue-class argument, both now Lean proofs. Its docstring gives a complete proof in words.

The first worker's proposed holes `isFinitePresentation_of_isCoherent_localNoetherian` and
`exists_isZero_moduleCohomology_tensorPow_of_ample_core` are removed, not counted as closures
against the repository baseline. Finite presentation is now proved inside the original theorem.

Both modules compile locally without errors or non-sorry warnings. A scratch copy with
`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the
original theorem and the new hole. The scratch source was removed before delivery.

## No longer needed

Removed direct imports from the original module:
- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`
- `Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Serre`
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`

The first, second and fourth are retained as proof-plan imports of the new smaller theorem.
The remaining comparison, invertible-module and twist declarations are supplied transitively
by needed imports. No module is claimed to leave the full target closure. The first worker's
added public `Mathlib.AlgebraicGeometry.Noetherian` import was also removed; needed proof
imports supply the Noetherian facts.

Every old proof dependency omitted from the original node's new direct route:
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`: unused; only local Noetherianity is
  needed, without a separate quasi-compactness proof for Spec A.
- `def-pc-proj`, `lem-weil-pbc-finite-type-algebra-noetherian`,
  `lem-weil-pbc-closed-immersion-coherent-equivalence`,
  `lem-pc-closed-immersion-coherent-cohomology`,
  `lem-weil-pbc-affine-morphism-cohomology-edge`, and
  `lem-pc-projective-space-serre-vanishing`: moved to the new smaller node's proof plan.
- `pqf-def-coherent`: remains a statement dependency, without a separate proof step.

No unit realization or chapter route was pruned. The discarded first-worker core was an
undelivered restatement, not a pruned library module.

## Where the brief, the DAG or earlier work was wrong

The first worker's core gave the whole Serre assertion under different coherence hypotheses,
which is not a genuine reduction. The core node file duplicated the finite-presentation
node's ID and contents. Both lacked chapter/unit fields and searches, and neither hole had
the required complete proof docstring. Imports were duplicated, and a proof-only import
was public.

The dependency `lem-pc-projective-space-serre-vanishing` states vanishing over a Noetherian
ring, but its recorded Lean declaration
`AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist` only covers fields
and uses abelian-sheaf H rather than module-global-sections cohomology. The upstream
closed-immersion restricted-twist theorem likewise covers only fields and H. Neither proves
the ring-general module-cohomology theorem. This mismatch is recorded in the new hole's
proof plan instead of assuming a nonexistent specialization. Mathlib searches found no
replacement. LeanSearch was unavailable; LeanFinder, Loogle and source grep ran and are
recorded accurately.

## New nodes

`lem-weil-pbc-closed-immersion-serre-vanishing` carries vanishing for restricted twists on a
closed subscheme of projective space over a Noetherian ring, with source, complete proof plan,
searches, chapter, unit and verbatim Lean signature. Unlike the item's Tag 0B5T statement,
it assumes a specified closed immersion and twists pulled back from projective space;
it has no arbitrary ample module. Unlike `lem-pc-projective-space-serre-vanishing` (Tag 01YS),
it also includes the closed-immersion projection formula and affine cohomology comparison.
The upstream field-only counterpart is not a duplicate general theorem.
Sources read: [Stacks 01YS](https://stacks.math.columbia.edu/tag/01YS) and
[Stacks 0B5T](https://stacks.math.columbia.edu/tag/0B5T).
No change record is needed: existing interfaces and definitions are unchanged.

## Second reading by J4

1. Compared the original and delivered modules with diff and the declaration parser.
   Verdict: the existing signature is byte-for-byte unchanged; no definition or target
   statement changed. The only new public statement has its own new module.
2. Compiled both files with lcompile.py and inspected every proof and prohibited construct.
   Verdict: clean compilation, one named theorem hole, no sorry in data or definitions,
   and no axiom/unsafe/opaque/extern/implemented_by. Axiom printing gives only standard
   axioms and sorryAx. Geometric witnesses are local to the proof; no definition chooses
   an arbitrary object from an unproved existence theorem.
3. Checked the split against Tags 01YS and 0B5T. Verdict: true and strictly smaller. Checked
   zero F, empty X, the zero base ring, projective dimension zero, tensor exponent zero,
   and d=1. Small twists need not vanish: the bound can increase. The finite-presentation
   conversion now follows from finite affine sections over Noetherian rings without a
   new hole. Searches under restricted twists, closed immersion and Serre found no general
   existing replacement in Mathlib, upstream or Sheaf.
4. Read from the original theorem downward and tested redundant-import removal by compilation.
   Verdict: the original geometric route is retained and the residue step is explicit.
   Inspected dag/units/sk-thm-p1.json realized: this helper is not a realized unit statement
   or step, and none of those records changed. Every omitted old direct dependency is
   accounted for above; no full-closure module pruning is claimed.
5. Compared Lean with the node records and checked the unions of proof-step uses.
   Verdict: the original node records the actual reduction; the new node records exactly
   the remaining hole with all required metadata and real searches.

Second reading replaced the restatement by the closed-immersion and residue reduction,
proved the finite-presentation conversion, repaired nodes and report, and removed duplicate,
proof-only public and redundant imports. The result is explicitly a decomposition.
