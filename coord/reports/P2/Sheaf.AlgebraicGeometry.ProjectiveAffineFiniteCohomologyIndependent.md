## What changed

Proved the body of `AlgebraicGeometry.Scheme.Modules.finite_H_projective_affine_independent`
in `Sheaf.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent`, preserving its
signature and docstring. Added private, fully proved helpers for the opens-site Cech
encoding, the degree bound, and finiteness from an exact segment. The degree bound works
over arbitrary affine T and for empty N. A simultaneous descending induction proves
finiteness for every coherent module on projective space, then the same segment argument
handles the given closed embedding. No general proper-coherence result is used.

Added the proof import `Sheaf.AlgebraicGeometry.ProjectiveFiniteSourceCohomologySegment`
and imports of `Sheaf.AlgebraicGeometry.AlternatingCechComputes`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`,
and `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`.
The proof uses the existing transitive Mathlib finiteness infrastructure.
All imports needed only for proofs are non-public.

Updated the item's node proof and proof dependencies to match this route. Added one
node/module for the exact-segment construction. Both modules compile without warnings
using lcompile.py. The unit's projective-space / Cech / Chow route is preserved; the
unit record has empty realized lists, and no recorded realization was bypassed.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.Scheme.Modules.finite_H_projective_affine_independent`
(node `lem-pc-m1-projective-affine-finite-cohomology-independent`).
There are no sorries left in the item's module, including its private helpers.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exists_projective_finite_source_cohomology_segment`
(node `lem-pc-p2-projective-finite-source-cohomology-segment`), in its own new module.
Its whole proof is `by sorry`. Its docstring gives the closed pushforward, finite twist
presentation, coherent kernel, finite twist cohomology, exactness, and scalar-linearity
argument. It asserts no finiteness of the last cohomology term. This is a decomposition
(1 upper hole closed, 1 lower hole added), not a net proof-count improvement.

Edge cases checked mathematically: empty N gives empty P and Y and the zero segment;
one coordinate gives the affine case; q=0 uses the initial long-exact sequence segment;
the zero sheaf permits V=K=0. The compiled bound itself covers N empty without a case
split or a nonempty assumption. The proof needs only finiteness of the last map's image,
not surjectivity onto the last cohomology group.

## No longer needed

No existing imports were removed: the initial module had only statement imports.
The second reader removed the redundant newly added proof imports
`Mathlib.RingTheory.Noetherian.Basic` and `Mathlib.RingTheory.Finiteness.Finsupp`;
the retained imports already provide the used instances and `Module.Finite.of_exact`.
The proof no longer uses node `lem-pc-projective-space-coherent-finiteness` or the module
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` containing its declaration
`AlgebraicGeometry.ProjectiveSpace.finite_H`. The stronger projective-space result is
replaced by the actual bounded descending induction in the item's body.

The source cohomology-bound declaration in
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre` is not imported: its standard-cover
argument is implemented directly over T with the lower Cech declarations. The twist
quotient and twist-cohomology nodes are still needed by the remaining segment; they
are not claimed pruned. Node `lem-pc-closed-immersion-coherent-cohomology`, the other old direct
`proof_deps` entry, is removed from the item's direct dependencies but remains a
dependency of the split segment; it is not pruned.
No other modules are claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

Import-direction checks refuse both
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` and
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre`: both already reach this item, so
importing either here would close a cycle. Thus the two planned dependencies cannot
simply be applied through their aggregate modules. Moreover the recorded module
closed-pushforward cohomology comparison is stated over a field, whereas this item's
Gamma(T,O) need not be a field. The new segment retains the missing ring-linearity
rather than hiding it in a cast or assuming a field. The twist Cech comparison in
ProjectiveSpace.TwistSections is also field-specific, although the algebraic monomial
complex itself works over a commutative ring.

Read Stacks Tags 01YS and 01Y6 through their published pages; the local Stacks checkout
is absent on this machine. The exact segment is precisely the degree-local step of the
01YS descending induction, combined with finite closed pushforward from 01Y6. Searches
used msearch.py: LeanSearch was unavailable (HTTP internal error), LeanFinder returned
no appropriate segment, and grep found no candidate in Mathlib/AlgebraicGeometry.
The useful general algebra lemma is Mathlib's `Module.Finite.of_exact`.

## New nodes

`lem-pc-p2-projective-finite-source-cohomology-segment` states an exact segment with a
finite source and H^(q+1) of a coherent projective-space module as its final term.
It is strictly an induction step, not the original finiteness theorem under a new name:
it never asserts the middle or final group finite. The original theorem combines this
step with a proved upper degree bound, an actual descending induction, and the proved
Noetherian image/extension argument. The new module is
`lean/Sheaf/AlgebraicGeometry/ProjectiveFiniteSourceCohomologySegment.lean`.
No interface changes, forced adaptations, or change records.


## Second reading by P2

1. Compared the complete existing module with the repository using diff. Its only
existing theorem's signature and docstring are byte-for-byte unchanged. The changes
are private proved helpers, proof imports, and the theorem body. No existing public
definition or statement changed; no change record is needed. Verdict: pass.

2. Compiled both delivered modules in import order with lcompile.py, without errors
or warnings. Inspected every definition and proof: the only remaining sorry is the
named new segment theorem reported above. No axiom, unsafe, opaque, implemented_by,
extern, or hollow definition occurs. Scratch #print axioms checks for the target,
projective degree bound, and exact-segment helper give only propext, Classical.choice,
Quot.sound, and (for the first two) sorryAx from open dependencies. The algebra helper
has no sorryAx. The delivery tool additionally probes all declarations. Existential
witnesses are eliminated locally in a Prop proof; no public data definition chooses
an arbitrary object from the open existence theorem. Verdict: pass as decomposition.

3. Read the new theorem and node against
[Stacks 01YS](https://stacks.math.columbia.edu/tag/01YS), especially the finite-twist
quotient and its exact cohomology segment, and
[Stacks 01Y6](https://stacks.math.columbia.edu/tag/01Y6) for closed pushforward.
Over the Noetherian affine base the projective space is Noetherian, so finite
presentation and quasi-coherence give the required coherent kernel. The statement
requires exactness only at H^q(F), not surjectivity of the boundary. For empty N both
schemes are empty; for one coordinate the construction is over an affine scheme;
q=0 uses left exactness and its first boundary; F=0 allows the zero segment.
The final term has no asserted finiteness, making this strictly the degree-local
induction step rather than a restatement of the item. Its docstring supplies the
construction and scalar compatibility. Independent LeanFinder search used the query
"coherent projective sheaf finite presentation kernel long exact cohomology sequence
finite generated source"; grep used "Module.Finite.of_exact|rangeRestrict|
cohomologicalDimension|cech.*vanish", and rg inspected the projective, Serre,
finite-extension and coherent-vanishing modules in the library and upstream.
No reusable ring-general finite-source segment was found. Closing this remaining
geometric construction is substantial, not a short local repair. Verdict: pass.

4. Read the descending induction and bound from the target downward. The degree-r
alternating cochains vanish for r >= card N because a strictly increasing
Fin(r+1) -> N is impossible, also for N empty. The proof transports that vanishing
through the actual Cech comparisons, then descends simultaneously for all coherent
G and finally applies the segment for j. It uses the shortest available ring-general
route without the aggregate Projective/Serre imports that would introduce a cycle.
Checked sk-thm-picard-coherence: its route through projective-space finiteness and
Cech machinery is preserved, and its realized.statement and realized.steps[0] lists
are empty. Both old proof_deps entries are accounted for in No longer needed:
projective-space coherent finiteness is bypassed, while closed pushforward moves
into the segment and remains needed. Removed two redundant added Mathlib imports
and recompiled. Verdict: pass.

5. Compared the node records with Lean. The existing node changes only proof,
proof_deps and proof_origin; its signature record still agrees verbatim. The new
node has the complete signature, source, three search kinds, statement dependencies,
proof steps and their union, provenance, split status, creation, blueprint, chapter,
unit and lean records. Its proof dependencies are the geometric plan of the remaining
hole, including the ring-general comparison work described in the report; the
completed item's dependencies match its bound, algebra argument and segment use.
Verdict: pass.

Changes by this reader: removed the two redundant proof imports; clarified the
movement of the old closed-pushforward dependency and the retained transitive
Mathlib infrastructure in the report. No mathematical statement or proof body changed.
