## What changed

Replaced the sorry in `AlgebraicGeometry.principalCech_finiteColumn_model` by a complete
proof using an explicitly constructed bicomplex. The existing declaration signature and
all three public imports are unchanged. Added one proof-only import,
`Sheaf.AlgebraicGeometry.PrincipalCechBicomplexComparison`.

`PrincipalCechColumns` constructs the finite row index, section-complex functors,
categorical product columns, erased-subset restrictions and the alternating horizontal
natural transformation. Cardinality transport and horizontal naturality are proved.
It also proves absent columns are zero and that finite products of section
quasi-isomorphisms are quasi-isomorphisms. The latter uses the additive homology functor's
finite-product comparison, not an additional unproved exactness assertion.

`PrincipalCechHorizontalSquare` isolates cancellation of two horizontal restrictions.
`PrincipalCechBicomplexComparison` constructs the bicomplex and its coefficient functor
from the explicit data and that named square-zero theorem. Its remaining theorem is only
the natural identification of its total with the existing principal Čech total functor.
No data is selected from an existence theorem; the bicomplex is `CochainComplex.of`
of actual product columns and actual restriction maps. The named square-zero theorem
is used only in a proof field.

The target proof supplies both bicomplexes and the map, proves four strict support bounds,
proves its column quasi-isomorphism implication, and applies `Arrow.isoOfNatIso` to the
natural comparison. All four delivered modules compile without warnings with lcompile.py.

Read the source via the official Stacks pages for Tags 08D1, 01FP and 08C2 (the checkout
contains only the literature lists). In particular, 08D1 explicitly has total differential
horizontal plus (-1)^p vertical, and 01FP spells out its restriction coordinates.
https://stacks.math.columbia.edu/tag/08D1
https://stacks.math.columbia.edu/tag/01FP
https://stacks.math.columbia.edu/tag/08C2

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.principalCech_finiteColumn_model`
(node `lem-sc-principal-cech-finite-column-model`): 1 of 1 original holes closed.
This is a decomposition, not a sorry-free proof of the mathematical theorem.

Two holes added, each in its own new module:

- `AlgebraicGeometry.principalCechHorizontal_square`
  (`lem-sc-principal-cech-horizontal-square`): cancellation of two actual horizontal maps.
- `AlgebraicGeometry.principalCechBicomplexComparison_exists`
  (`lem-sc-principal-cech-bicomplex-comparison`): natural total-coordinate comparison
  for the actual constructed bicomplex.

Neither new statement asserts finite support or preservation of quasi-isomorphisms.
Neither restates the original existential model theorem. Each is a separate step of its
argument, with an explicit construction fixed in advance. Net holes closed minus added
for this delivery is -1 before any closure/baseline effects.

Additional completely proved supporting declarations:
`principalCechRowIndex_erase_card`, `principalCechColumn_isZero`,
`principalCechColumn_quasiIso`; functor laws, restriction naturality, horizontal
naturality, and bicomplex-map compatibility are also completely proved.

Edge cases: r=0 has no nonempty subset in any row; r=1 has only its singleton in row 0.
All rows with p<0 or p>r-1 are empty by the proved cardinality argument. Empty geometric
intersections need no special hypothesis: their section objects and restrictions use the
existing section functor. No boundedness or K-injectivity is assumed or used. The signs
are integer scalar multiplication; under the A-module structure these are exactly the
powers of -1 in A used in the existing coordinate differential, including characteristic 2.

## No longer needed

No existing import was removed and no existing module is pruned. All three original
public imports are needed for the unchanged statement. The old proof dependency
`def-sp-double-complex-total` is replaced at the original theorem by the new explicit
construction and comparison nodes. The other old direct proof dependency,
`def-sc-principal-open-alternating-total`, is also replaced at the original theorem;
it remains a statement dependency and a dependency of the new column and comparison
nodes. The generic notion of total remains in statement
references and Mathlib.TotalComplex, so this is not a claim that the entire node or
module is globally unreachable. No first-quadrant hypothesis or filtration theorem is
used; only the generic Mathlib bicomplex total is needed.

Searches in WeilConjectures and Sheaf found no existing explicit principal Čech columns
or bicomplex. Mathlib's alternating-coface square theorem is for a supplied cosimplicial
object; this subset-indexed alternating construction has no such supplied object, so
it was not imported. Search queries and results are recorded in searches.jsonl.
LeanSearch was unavailable and is recorded as unavailable, never as evidence of absence.

## Where the brief, the DAG or earlier work was wrong

The original DAG's assertion that finite products have coordinatewise homology was
correct. It is now an actual Lean proof using the finite-product-preserving additive
homology functor. The original non-elementary construction and comparison steps cited
only definitions; the delivery makes those steps explicit and isolates their two remaining
proof obligations. No existing statement was changed, and no mathematical error or
disputed statement was found. The unit record has no realized step naming this node;
the same Čech double-complex route is retained.

## New nodes

`def-sc-principal-cech-columns`, in `PrincipalCechColumns`, gives the explicit product
column and horizontal restriction constructions. Its module has no sorry.

`lem-sc-principal-cech-horizontal-square`, in `PrincipalCechHorizontalSquare`, isolates
the paired-deletion cancellation proof. Its source and complete proof in words accompany
its named theorem. It depends on the explicit column construction.

`lem-sc-principal-cech-bicomplex-comparison`, in `PrincipalCechBicomplexComparison`,
constructs the actual bicomplex functor and states the natural total comparison. Its
proof groups subset coordinates by cardinality and checks the signed differential and
coefficient maps. It makes no claim about column quasi-isomorphisms or support bounds.

All three nodes are in sec-picard-framework, unit sk-thm-picard-duality, with the same
nearest blueprint ancestor lem-sc-finite-duality and precise parent proof places.
Blueprint searches for alternating Cech and double complex found generic existing
nodes, but none states these explicit principal-column constructions or the two lemmas.
No change record is needed: all existing signatures and visible imports are identical.

## Second reading by T2

1. Compared the existing module and node with the repository using diff. The only
   existing Lean changes are its proof and one plain proof import: its declaration
   signature, docstring, definitions and public imports are byte for byte unchanged.
   The three other modules and their nodes are new. No change record is required.
   Verdict: pass.
2. Read all four modules and compiled them in import order through lcompile.py.
   The only two sorries are the named theorems listed above, both with complete
   natural-language proofs and nodes. There are no forbidden declarations or hollow
   definitions. The bicomplex data consists of actual products and restrictions;
   its square-zero theorem supplies only a proof. Checked the declarations with
   #print axioms in a scratch module, and the delivery's full axiom probe also runs
   before pushing. Verdict: pass, conditional on the two explicitly recorded holes
   and the already open upstream statements, not a sorry-free target proof.
3. Checked the square-zero statement by pairing distinct deletions, including an
   empty twice-erased subset, and checked the comparison's coordinate inverse and
   degree formula. For r=0 both coordinate families are empty; for r=1 only row 0
   remains; for r=2 horizontal squares have empty source or target; for r=3 the two
   paths from a singleton to the triple have opposite signs. Negative and absent
   rows vanish. Characteristic 2 still gives cancellation. Neither hole restates
   the existential model: one concerns the fixed horizontal maps, the other the
   fixed functors, and neither supplies support or column quasi-isomorphisms.
   Repeated searches with different words through leanfinder, loogle and grep,
   and read AlternatingCechTotalComplex in the existing library. Its proved
   alternatingCechDifferential_square and alternatingCechDoubleFunctor use increasing
   tuples, ordinary section modules over the global section ring, and natural rows
   extended to integers. They do not state either new lemma for these categorical
   product columns over A and subset-cardinality indices. Reusing them would still
   require the tuple/subset, section-ring, and product-evaluation transports; no
   direct application closes either hole. Verdict: true and strictly smaller
   obligations, with no exact duplicate found.
4. Checked the four support clauses and the finite-product homology argument in
   the target proof. Read Mathlib ComplexShapeSigns and TotalComplex: horizontal
   sign is 1, vertical sign is Int.negOnePow p, as required by the specified total
   differential. Checked the same convention against Stacks Tags
   [08D1](https://stacks.math.columbia.edu/tag/08D1) and
   [01FP](https://stacks.math.columbia.edu/tag/01FP). The finite horizontal support
   permits arbitrary vertical degrees. The unit's realized fields are empty and
   are unchanged; this retains the stated double-complex route. No module is
   pruned. Verdict: pass after correcting import visibility and completing the
   list of replaced old direct proof dependencies.
5. Read all four nodes, checked their Lean declarations, proof steps, unions of
   uses, sources, blueprint ancestry and unit. The original node changes only
   proof, proof_deps and proof_origin; each new node has the required split,
   creation, search and Lean records. The two open lemmas have their own matching
   modules and docstrings. Verdict: pass.

Changed PrincipalCechBicomplexComparison to publicly import PrincipalCechColumns
and privately import PrincipalCechHorizontalSquare. Wrapped the named square-zero
argument in a tactic proof block, so Lean accepts the private proof import in the
exposed construction; this changes no data or statement. Completed the pruning
report for def-sc-principal-open-alternating-total and recorded the existing
tuple-indexed construction, which the first report had not discussed. No additional
hole was closed or added during the second reading: this remains a decomposition
of one original hole into two smaller ones, net -1 holes before closure effects.
