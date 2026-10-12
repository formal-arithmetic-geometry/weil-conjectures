## What changed

Replaced the proof hole in `CochainComplex.exists_functorial_cyclePullback_core`
by a complete Lean assembly proof from an explicit recursive construction, proved reindexing laws, and one
smaller named pointwise-comparison obligation. The original statement and public imports are unchanged.
The two added imports are ordinary proof imports:
`Sheaf.Algebra.Homology.CyclePullbackLaws` and
`Sheaf.Algebra.Homology.CyclePullbackTowerComparison`.

Added `Sheaf.Algebra.Homology.CyclePullbackTower`. It performs the descending
recursion in the abelian functor category of the inclusion's domain. A stage stores
its degree, two term functors, differential, and augmentation. The successor's current
term is literally the pullback functor followed by T, with the prescribed projection
maps. Natural-number iteration supplies all stages. Proved integer degree and
next-term equalities transport this actual data to integer-indexed natural
transformations. No data comes from a theorem with an unproved existence conclusion;
all definitions, including every transport proof, are proved without sorry.

The core proof constructs the object complexes and their maps with
`CochainComplex.of` and `CochainComplex.ofHom`, proves the functor laws from those
of the term functors, and constructs the natural augmentation using the proved tower laws.
It proves membership in S and the bound directly from the construction, then uses
the pointwise tower comparison and rewrites both adjacent assembled differentials.
The four modules compile together through lcompile.py.

## Proved and sorry left

Closed the original hole:
`CochainComplex.exists_functorial_cyclePullback_core`
(node `lem-pc-functorial-cycle-pullback-core-stage3`). Its module contains no sorry.

Added exactly one hole, the whole proof of a public named theorem:

- `CochainComplex.CyclePullback.tower_comparison`
  (node `lem-pc-cycle-pullback-tower-comparison-stage3`, module
  CyclePullbackTowerComparison). This asserts pointwise projection comparisons only
  for the specific tower's term functors and adjacent natural transformations.

This is a decomposition, not a completed axiom-free proof: one upper hole closed,
one strictly smaller lower hole added, net holes closed minus added = 0.
The tower data and laws modules have no holes. The data module's named proved helpers
include tower_degree, tower_next, term_eq, degree_eq, term_isZero, term_mem,
step_square, and step_comm. In the laws module,
`CochainComplex.CyclePullback.tower_laws` is fully proved. Its private proved helpers
transport the local square and augmentation equations through the integer reindexing,
then handle the top-degree and zero-tail cases. This closes the initially proposed
law obligation before delivery; it is not left as another sorry.
The remaining obligation combines evaluation's kernel and pullback comparisons
with the proved transports. Its docstring has its source and complete proof in words.

## No longer needed

No original import, node, or module is pruned. The core node originally had empty
proof_deps; there were no stated auxiliary modules to remove. Its original three
public Mathlib imports remain because its statement uses their notions.
The candidate's unused pointwise-pullback proof import was removed from
CyclePullbackTowerComparison, and the tower imports ObjectProperty.Basic rather than
FullSubcategory because its definitions only need the property itself.

The previously rejected CyclePullbackAssembly and CyclePullbackComparison modules
and their nodes remain only in scratchpad/rejected-first-reading. They are not part
of this delivery and are not used anywhere in the repaired proof.

## Where the brief, the DAG or earlier work was wrong

The original core DAG plan had two non-elementary steps but no proof dependencies.
There are therefore no stated dependency lemmas from which its plan can simply be
applied. This delivery makes its recursive data concrete and isolates only the
remaining reindexing and pointwise-limit arguments, with matching new nodes.

The earlier comparison quantified over arbitrary bounded Q, so the constant-zero
functor with nonzero F in degree N refuted it. The repaired comparison quantifies
over the explicitly defined tower, and never over arbitrary Q. In that counterexample
with T=Id, the constructed degree-N term is the pullback against the zero next stage;
it is isomorphic to F.X N, rather than the zero object. This preserves the essential
construction invariant. The former assembly-without-comparisons theorem is unused.

Edge cases checked against the construction: zero target complexes; degree i=N
(the predecessor is the initial zero stage); i=N+1 and all higher degrees (literal
zero families); arbitrary negative bounds N (depth uses integer subtraction before
toNat); T=Id with nonzero F in degree N; and T the constant zero functor with zero pi.
No epimorphism, additivity, limit-preservation, or zero-preservation assumption on T
is introduced. Terms below the bound are actual objects T.obj X, so membership in S
uses hT directly and requires no unstated closure of S under isomorphisms.

Read Stacks Tag 05T7, part (1), at https://stacks.math.columbia.edu/tag/05T7.
Its descending construction is performed here in a functor category; its stronger
surjectivity and quasi-isomorphism assertions are not used. Mathlib searches through
msearch.py are recorded in searches.jsonl: LeanSearch was unavailable; LeanFinder
returned augmentation and CM5b constructors with different hypotheses; Loogle had
no relevant fixed-T construction; grep found the local kernel/pullback equations,
PreservesKernel.iso, and pullbackObjIso. Searches of both library roots found the
existing core and callers, but no alternate fixed-T construction. Blueprint search
for cycle pullback found no imported matching node. The unit's realized statement
and step lists are empty, and no recorded unit realization is bypassed.

## New nodes

`def-pc-cycle-pullback-tower-data-stage3`: the actual recursion and its proved
reindexing, local equations, and term-property helpers, in CyclePullbackTower.
Its Lean record lists the primary tower declaration and the supporting declarations.
It contains no sorry and makes no arbitrary existence choice.

`lem-pc-cycle-pullback-tower-laws-stage3`: the square-zero and augmentation equations
for that explicit recursion, in CyclePullbackLaws. Its complete Lean proof transports
the local step equations using equality morphisms, their composition law, and a
proved transport formula for the target differential. It handles i<N, i=N, and i>N
separately. There is no sorry in this module.

`lem-pc-cycle-pullback-tower-comparison-stage3`: evaluation identifies the explicit
successor term with T of the pointwise pullback, preserving both projection maps,
in CyclePullbackTowerComparison. Its natural-language proof specifies the kernel,
pullback, and functorial isomorphisms, naturality of pi, and the top-degree case.

The original core node's proof, proof_deps, and proof_origin now follow the actual
Lean assembly. Each new node's proof_deps is exactly the union of its steps' uses.
No existing definition, signature, visibility, or public import changes; there are
no change records or forced adaptations.

## Second reading by S3

1. I compared the delivered `CyclePullbackCore.lean` against the repository version. The
   existing theorem statement, declarations, and public imports are unchanged; the only
   interface additions are the explicitly listed new modules and their nodes.

2. I compiled all four delivered modules with `lcompile.py --all`. They compile without
   errors or warnings. The only remaining `sorry` is the named theorem
   `CochainComplex.CyclePullback.tower_comparison`; no definition contains `sorry`, and
   the delivered files contain no forbidden `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declaration.

3. I read each split-off statement and its node. `tower_laws` is fully proved;
   `tower_comparison` is a strictly smaller obligation about the explicitly constructed
   tower, with a source, proof plan, and matching declaration. The comparison does not
   quantify over arbitrary bounded complexes and therefore does not weaken the original
   theorem. The explicit tower definitions are concrete recursive constructions, not
   witnesses selected from an unproved existence result.

4. I checked the proof route and imports. The core proof uses the tower data, its laws,
   and the comparison exactly as recorded in its DAG proof. The three new modules import
   only their statement dependencies plus proof requirements; the original core imports
   needed by its public statement remain. No old proof dependency or module is unused.

5. I checked the DAG records and unit route. The four node records agree with the Lean
   declarations and proof dependencies, and the explicit construction preserves the
   unit's stated descending cycle-pullback route. Edge cases in the report (top degree,
   zero tail, negative bounds, and zero functors) are consistent with the definitions.

I changed only this report section after the first delivery check; no Lean declaration,
node statement, or import was changed during this second reading.
