## What changed

Proved `CochainComplex.isKProjective_of_filtered_free_step` in
`Sheaf.Algebra.Homology.FilteredFreeKProjectiveStep`, preserving its signature,
visibility, and existing docstring. Added two fully proved private helpers:
`single_projective` and `coproduct_projective`.

The single-complex helper applies Mathlib's bounded-above projective theorem,
with projectivity of the free term and of zero terms. The coproduct helper
constructs the homotopy components through degreewise coproduct universal
properties and verifies both homotopy equations on each inclusion. The final
proof uses the evaluated cokernel sequence, its given retractions, Mathlib's
degreewise-split distinguished triangle, and closure of the left orthogonal of
acyclic complexes under extensions. It follows all three steps of the original
plan. The unit record has no realized nodes attached to this item; no unit step
is bypassed.

Added proof-only imports of
`Mathlib.Algebra.Category.ModuleCat.Projective` and
`Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`. All original public
imports remain. Updated only the item's node's proof, proof_deps, and
proof_origin to record the actual Mathlib route; the bounded-above theorem is
already the Mathlib leaf `lem-sc-bounded-above-projective-kprojective`.

LeanFinder search for coproduct/extension K-projectivity returned the
bounded-above projective theorem but no extension theorem. Loogle search for
`CochainComplex.IsKProjective` returned its definition, iso/shift invariance,
and bounded-above projectivity. The logged grep search for
`IsKProjective|isKProjective` found those Mathlib declarations. Local rg searches
also checked both project roots and the degreewise-split/orthogonal APIs.

The final file compiles without warnings through lcompile.py. The argument
includes an empty index type, the zero ring, unequal universes, and arbitrary
unbounded degree functions. Choices select homotopies and witnesses from the
proved splitting hypothesis only; no data uses an unproved existence theorem.
The cited source was checked at [Stacks Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
and [Tag 09KJ](https://stacks.math.columbia.edu/tag/09KJ); the local literature
copy is absent on this machine.

## Proved and sorry left

Closed the only original hole:
`CochainComplex.isKProjective_of_filtered_free_step`
(node `lem-pc-filtered-free-kprojective-step`).

Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
Both private helpers are completely proved; this is a proof, not a decomposition.

## No longer needed

None of the original imports, nodes, or modules is pruned. A redundant
`Mathlib.Algebra.Homology.HomologicalComplexLimits` proof import was tried during
construction and removed: KProjective already exposes the necessary API.
No dependency on another sorried Sheaf module was introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The planned generator-by-generator
single-complex argument is supplied by Mathlib's bounded-above projectivity
lemma. The missing coproduct glue has now been written and kernel checked.
No new nodes or forced adaptations were needed.

## Second reading by S3

1. **Interface: pass.** I compared the whole delivered module with the repository
   using `diff -u`, and separately compared the existing theorem header byte for
   byte through its proof delimiter. The ring, both universe levels, complexes,
   chain map, K-projectivity hypothesis, retractions in every integer degree, and
   existential coproduct isomorphism are identical. The public visibility and
   existing docstrings are unchanged. Only two private proved helpers, two plain
   proof imports, and the theorem's proof were added. There are no definitions or
   change records. The node's statement and Lean record are unchanged.
2. **Proof: pass.** Local `lcompile.py` compiled the delivered file without warnings
   (1.5 seconds). In a scratch copy I printed axioms for `single_projective`,
   `coproduct_projective`, and `isKProjective_of_filtered_free_step`: each uses
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   A source scan finds no sorry or prohibited construct. In the coproduct helper,
   `hc` is the evaluated colimit, `fac` identifies each descended component, and
   both homotopy equations follow by its `hom_ext`; the differential identity uses
   the chain-map equation of each inclusion. In the main proof, evaluation of the
   cokernel sequence is exact and its last map is epic; the given left inverses
   supply its splittings. The triangle's middle object is the image of L. The
   left-orthogonal extension theorem therefore proves precisely the conclusion.
   The homotopies chosen here come from the K-projectivity hypotheses or the
   proved single-complex result, and the retractions come from `hsplit`; no data
   is chosen from an unproved theorem.
3. **Split statements: pass, none.** No holes or public statements were split off.
   Both private helpers are proved and strictly intermediate. The single helper
   uses strict support at d and projectivity of ULift A and of zero objects.
   The coproduct helper covers an empty index by the same colimit extensionality,
   and does not assume boundedness or nonemptiness. The zero ring and unequal
   universes are allowed by the original types. There is no hidden uniform degree
   bound in the coproduct proof. I read Mathlib's KProjective file (including its
   definition and bounded-above theorem), ran a fresh Loogle search for
   `CochainComplex.IsKProjective`, and searched Mathlib's homology sources and the
   project/upstream homology sources for K-projectivity. No existing coproduct or
   split-extension theorem giving a shorter direct proof was found.
4. **Route and pruning: pass.** I read [Stacks Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
   and [Tag 09KJ](https://stacks.math.columbia.edu/tag/09KJ), and Mathlib's
   degreewise-split triangle construction and distinguished-triangle criterion.
   The source's finite-filtration step is realized by the split triangle, free
   quotient vanishing, and extension closure; bounded-above projectivity shortens
   only the single-generator argument. The unit
   `dag/units/sk-thm-picard-duality.json` has empty `realized.statement` and an
   empty realized list for its sole step, so no realized unit node is bypassed.
   All five imports supply the abelian module category, its arbitrary coproducts,
   K-projectivity API, module projectivity, or split triangles. The added imports
   are plain proof imports. The old node has empty `proof_deps`, so there is no
   omitted old dependency to list under `No longer needed`; none is pruned.
5. **DAG: pass.** The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. Its three steps match the Lean: evaluated cokernel splittings,
   bounded-above single-complex projectivity followed by explicit coproduct
   homotopies, and left-orthogonal extension closure. I read the existing Mathlib
   leaf `lem-sc-bounded-above-projective-kprojective`: its matched declaration is
   exactly the theorem used by `single_projective`. The union of the steps' node
   uses is the recorded singleton `proof_deps`. No new nodes need validation.

Changes after this reading: added this independent review and its fresh search
and axiom evidence. No Lean or DAG repair was needed. Holes closed remain 1
(`CochainComplex.isKProjective_of_filtered_free_step`); holes added remain 0.
