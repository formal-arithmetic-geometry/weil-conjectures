## What changed

Proved the assembly of `AlgebraicGeometry.tate_selfTor_conormal_map` with its existing
signature and docstring unchanged. Its comparison morphism is constructed by quotient descent
from two explicit linear maps on a free module of concrete Koszul wedge-cycle generators.
The first map evaluates generators in the exterior conormal; the second evaluates them in
homology of a specified projective resolution. The quotient construction determines the map
uniquely, rather than selecting an arbitrary map from an unproved existence assertion.

Added three modules, each with one public theorem:

- `Sheaf.RingTheory.KoszulAugmentationLiftExists`: proves augmentation-preserving Koszul lifts
  using projectivity of exterior powers and inductive lifting through exactness.
- `Sheaf.RingTheory.KoszulConormalCyclePresentation`: defines actual wedge-cycle generators
  and their finite linear-combination presentation, and proves surjectivity. Its private
  helpers prove the wedge-boundary formula and that every quotient-tensored differential is zero.
- `Sheaf.RingTheory.KoszulConormalCycleRelations`: defines the explicit homology evaluation
  and states the remaining kernel inclusion, with source and complete proof in words.

The item's three added imports are proof-only: the first two dependency imports are
`Sheaf.RingTheory.KoszulAugmentationLiftExists` and
`Sheaf.RingTheory.KoszulConormalCycleRelations`; the third is
`Mathlib.LinearAlgebra.Isomorphisms`. The existing public import is unchanged. Updated the
item's node proof to match the quotient descent and resolution transport actually written.
No existing definition, statement, public import, or consumer module was changed.

The construction uses one resolution Q initially. For any resolution P the proof composes
its Koszul lifts with Mathlib's lift of the identity Q -> P, proves the augmentation equation,
and transports the wedge formula using `isoLeftDerivedObj_hom_naturality`. This is actual Lean
assembly, not an application of an existential comparison theorem under another name.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.tate_selfTor_conormal_map`
(node `new-r4-self-tor-conormal-comparison-tate-construction`) by decomposition.
No `sorry` remains in the item's module.

Also proved, without any direct or inherited `sorry`:

- `AlgebraicGeometry.koszul_augmentation_lift_exists`
  (`new-e1-koszul-augmentation-lift-exists`).
- `AlgebraicGeometry.koszulConormalCyclePresentation_surjective`
  (`new-e1-koszul-conormal-cycle-presentation`), including its private differential lemmas.

Added exactly one hole, the complete proof `:= by sorry` of
`AlgebraicGeometry.koszulConormalCycleEvaluation_ker`
(`new-e1-koszul-conormal-cycle-relations`). It is a kernel inclusion for explicit linear maps;
it has no derived-functor object or comparison-map existence conclusion. It isolates the
Tate product/conormal relations computation. Both free evaluation maps and all cycle data
are real constructions, with no `sorry` inside any definition.

This is a decomposition, not a fully sorry-free proof of the original theorem: one upper
hole closed, one lower hole added, net zero holes. All four delivered modules compile together
in dependency order through lcompile.py, with no compiler warnings. The formulas handle the
empty wedge (n=0), arbitrary non-generating tuples, I=0, I=A, and characteristic two. In the
surjectivity proof the empty tuple supplies the unit; no nontriviality, regularity, finite
presentation, or properness assumption was introduced.

## No longer needed

None. No existing import was removed. The original node had no proof dependencies to prune.
The remaining kernel lemma still follows the Tate product argument and comparison homotopies
from the source, while the lifting, spanning, descent, and arbitrary-resolution transport
are now proved. No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node marked both Tate-construction steps elementary and named no proof
dependencies. The actual construction of the strictly commutative homology product and its
conormal relations is substantial; it is now identified precisely as the kernel-inclusion
item. The final resolution transport needs no new hole: Mathlib already provides the
comparison lift and the naturality of its left-derived comparison isomorphism.

The search services returned no complete comparison construction. LeanSearch returned an
Internal Server Error; this was recorded as unavailable, with no mathematical verdict.
Loogle found the exterior spanning theorem, and LeanFinder found projective-resolution and
exterior-presentation tools. Direct source searches and inspection supplied the lifting API.
Sources were read at https://stacks.math.columbia.edu/tag/09PQ and
https://stacks.math.columbia.edu/tag/00LS. No statement is disputed.

## New nodes

`new-e1-koszul-augmentation-lift-exists` records the proved free-source comparison theorem
in `Sheaf.RingTheory.KoszulAugmentationLiftExists`; it needs no exactness of the Koszul source.

`new-e1-koszul-conormal-cycle-presentation` records the proved surjectivity theorem and its
companion generator type and explicit presentation map in
`Sheaf.RingTheory.KoszulConormalCyclePresentation`.

`new-e1-koszul-conormal-cycle-relations` records the remaining explicit kernel-inclusion
theorem and companion evaluation map in `Sheaf.RingTheory.KoszulConormalCycleRelations`.
Its source proof computes products in a Tate resolution and compares them to the specified
Koszul lifts using homotopy. Its declaration docstring gives the full argument and edge cases.

All three nodes inherit the item's chapter and unit. No change record is needed: existing
interfaces and definitions are unchanged, and only private proof imports were added to the item.

## Second reading by E1

1. Compared the delivered item module with the repository version. The target statement,
   `TateComparisonCertificate`, and all existing declarations are byte-for-byte unchanged;
   only proof-only imports and the proof body were added. The three added modules and their
   node files are new declarations, as reported above.
2. Compiled all four modules with `lcompile.py --all`; they compile without errors or warnings.
   There is exactly one intentional `sorry`, in `koszulConormalCycleEvaluation_ker`, and it
   is a named public theorem with a matching node and a complete source proof in its docstring.
   No definitions contain `sorry`, and no forbidden declarations occur. The proved declarations
   use only the permitted foundational axioms; the remaining kernel theorem is the sole open
   declaration and may expose `sorryAx` until completed.
3. Checked the three split-off statements against their constructions and edge cases. The
   augmentation lift is a concrete inductive projective lifting statement; the cycle
   presentation is an explicit surjective linear map; and the relation theorem is only a
   kernel inclusion for the displayed maps. None restates the target or weakens it. Their
   nodes carry matching Lean statements, sources, proof steps, and dependencies.
4. Checked the proof route and pruning. The target uses the three new nodes exactly as its
   quotient-descent construction does, and the unit route remains through the Tate comparison.
   No prior import or proof dependency became unused, so there is nothing to prune.
5. Checked the DAG and unit metadata against the Lean proof. The target node's proof and
   `proof_deps` name the three new declarations; each new node records its module and theorem;
   the unit/chapter fields are unchanged. No statement or definition change record is needed.

Changed only the proof-only imports, proof bodies, three new modules and matching node files,
and this report. The remaining kernel relation theorem is intentionally split off for later
work; no additional hole or interface change was introduced.
