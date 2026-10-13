## What changed

Proved `AlgebraicGeometry.Scheme.formallyUnramified_of_flat_depth_two_finite_extension`
without changing its statement or public imports. Added two proof-only imports:
`Sheaf.RingTheory.DepthLeSupportDimension` (already proved) and the new module
`Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood`.
The Lean proof implements the depth and dimension inequalities, the restriction
argument, the dimension-one boundary contradiction, application of the local
ramification criterion, and assembly by source locality.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.formallyUnramified_of_flat_depth_two_finite_extension`
(node `lem-sbc-flat-depth-two-finite-formally-unramified`).

Added one hole:
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_of_finite_flat_of_codimension_one`
(node `lem-sbc-finite-flat-codimension-one-etale-neighbourhood`). This is a
**decomposition**, with one hole closed and one added, not a net decrease of holes.
The new theorem is the local finite specialization of Stacks 0BJH. It mentions
neither U nor depth and does not restate the item's global extension theorem.
Its source and full discriminant proof are in its docstring and DAG node.
Both modules compile cleanly with lcompile.py in import order.

## No longer needed

Removed the redundant `Mathlib.AlgebraicGeometry.Properties` import from the new
local-criterion module during second reading. No old imports or proof-dependency
nodes were removed: the original node
had no stated proof dependencies. The new proof uses only the existing depth
bound and the local criterion; no target boundary-depth, smoothness, completion,
normality, or fibre-density lemmas are needed by this item.

## Where the brief, the DAG or earlier work was wrong

The original DAG step had `uses: []` despite using the depth bound and the local
ramification criterion. Those dependencies are now named and the assembly is
written in Lean. The mathematics agrees with Stacks 0BJH and the proof of
0EY6(3), read directly from their Stacks pages. No statement correction was needed.
The existing depth bound is a generic tool from sk-thm-p1: it is already proved,
and applying it to stalks does not replace any step of the spreading unit's route.
The unit record's realized fields are empty; this delivery preserves its
extension-in-depth-two route and does not edit that record.

## New nodes

`lem-sbc-finite-flat-codimension-one-etale-neighbourhood`, in the item's chapter
and unit, states the local finite specialization of Stacks 0BJH. Its positive
stalk-dimension condition excludes generic component points. Formal
unramifiedness on neighbourhoods is exactly unramifiedness at the indicated
points for this finite map. The source is locally Noetherian explicitly; the
item supplies that instance using finiteness. Empty sources give no point to
check. Dimension-zero points cannot satisfy positive dimension. For a ramified
finite flat map over a trait, the ramified closed point itself is a
dimension-one generalization, so the hypothesis fails as it should. For the
identity map every required neighbourhood exists. With U equal to L the main
proof uses only its first case, and for U empty its boundary inequalities are
handled without assuming any point exists.

Searches: LeanFinder and Loogle returned basic etale/formally-unramified
criteria, not this ramification theorem; Mathlib grep found unrelated number
field ramification facts. LeanSearch returned Internal Server Error and is
recorded as unavailable. Repository and whole-blueprint searches for 0BJH,
ramification-quasi-finite-flat, and unramified found no existing local criterion.
No change records or forced adaptations.

## Second reading by Y3

1. **Unchanged interfaces: pass.** Read the repository and sandbox files and
   their unified diff. The existing theorem signature is byte for byte identical,
   as are all four existing public imports and its docstring. The only changes
   to that module are two plain proof imports and the proof body. No definitions,
   target statements, or other modules are adapted; no change record is required.
2. **Proof and axioms: pass, conditional decomposition.** Both modules compile
   cleanly in import order with `lcompile.py`. A scratch copy with `#print axioms`
   for both declarations reports `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx` for both the main theorem and the new local criterion. The criterion is the sole remaining named theorem hole. There are no
   definitions or forbidden declarations in either delivered module. The chosen
   neighbourhoods occur only inside a proposition proof, never as definition data.
3. **New statement: pass.** Read [Stacks 0BJH](https://stacks.math.columbia.edu/tag/0BJH)
   and [0EY6(3)](https://stacks.math.columbia.edu/tag/0EY6) directly. Finiteness
   supplies quasi-finiteness and finite presentation; positive stalk dimension
   excludes generic component points. The supplied formally unramified opens
   express exactly unramifiedness at the dimension-one generalizations. Empty
   sources and dimension-zero points cannot instantiate the pointed hypotheses;
   for the identity map the whole source works; for a ramified trait map the
   closed point itself violates the dimension-one hypothesis. Nonreduced and
   identically-zero-discriminant cases are covered by
   [0BJG](https://stacks.math.columbia.edu/tag/0BJG), not by assuming a nonzero
   discriminant. New searches used the terms flat quasi-finite, height-one
   generalizations, branch locus and discriminant: LeanFinder returned etale
   locus results, Loogle returned flat/formally-unramified characterizations,
   and Mathlib grep returned no matching criterion. Repository and upstream
   searches likewise found no duplicate. Those characterizations do not prove
   unramifiedness here. Formalizing the discriminant criterion requires substantial
   missing geometry and is not a few-minute closure. The new statement is one
   local step, without U or depth, rather than a renaming of the global item.
4. **Route and pruning: pass.** Read the depth bound and the spreading unit
   record. The proof derives local dimension from depth, handles points over U,
   excludes dimension-one boundary points, applies the local criterion and
   assembles by source locality. Every step is present in Lean. Both proof-only
   imports are used. All existing public imports supply signature notions.
   The original `proof_deps` was empty, so there are no old nodes to prune.
   The unit's depth-two extension route and its empty `realized` fields are
   unchanged. The already proved depth bound is a generic tool, not a replacement
   of a unit step. Removed one redundant import from the new module.
5. **Nodes: pass.** Compared both JSON records with the declarations. The main
   node's four steps and dependency union match the Lean reduction. Its other
   fields are unchanged. The new node has its statement, source, complete
   natural-language argument, dependency union, proof origin, genuine search
   records, creation record, blueprint origin, chapter, unit and verbatim Lean
   signature. Its sole hole is declared by name above. The local proof now
   explicitly names etale localization 02LK, dimension equality 00ON and the
   locally principal locus lemma 0BJG in its docstring and node proof.

Second reading changed only the redundant import and the local criterion's
proof documentation and matching node proof. No signatures or proof terms were
changed. Counts remain one original hole closed and one new hole added: net zero,
a decomposition rather than a complete proof of the item.
