## What changed

Completed `AlgebraicGeometry.perfect_complex_descends` by compact-open induction using
Mathlib's `compact_open_induction_on`. The signature and existing docstring are unchanged.
The quasi-compact morphism to `Spec R_i` gives `CompactSpace Xi`; the empty case and affine
case come from `perfect_descent_affine_open`, and `perfect_descent_open_union` supplies the
step. Presenting the top open by the identity gives exactly the original pullback objects
and canonical comparison map, without transport through `Xi.topIso`.

Added three modules: `PerfectDescentOnOpen` defines the induction predicate with actual
fixed pullbacks and maps; `PerfectDescentAffineOpen` states the affine/empty case;
`PerfectDescentOpenUnion` states the conditional two-open induction step. Their node files
record the source argument and the parent's node now records the actual Lean induction.
These complete and repair the earlier sandbox attempt. All four modules compile cleanly.
No existing statement, definition, signature or public import was changed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.perfect_complex_descends`
(`lem-pc-perfect-complex-descent`). It is proved from two newly stated intermediate
results, so this is a **decomposition**, not a sorry-free proof of perfect descent.

Added exactly two holes, each with proof exactly `by sorry`:

- `AlgebraicGeometry.perfect_descent_affine_open`
  (`lem-pc-perfect-descent-affine-open`): the affine and empty-open base case.
- `AlgebraicGeometry.perfect_descent_open_union`
  (`lem-pc-perfect-descent-open-union`): the conditional gluing induction step.

There are no holes in the item's module or in `PerfectDescentOnOpen`, and no data is chosen
from an unproved existence theorem. One upper hole closed, two lower holes added: net -1,
with the actual finite-open induction fully proved in Lean.

Edge cases checked against the mathematical argument: the index is nonempty because an
index `i` is supplied; the empty open has only zero module sheaves and derived objects;
zero rings and empty affine schemes are allowed; empty, equal and disjoint opens satisfy
the gluing statement; intersections need only be quasi-compact, never affine. Descent on
the overlap is not an object-descent assumption: the existing morphism-descent theorem
lifts the identification of objects already descended on W and V. The predicate has no
assumption of finite presentation; that assumption occurs in the two lemmas proving it.

## No longer needed

Removed these direct proof imports from `PerfectComplexDescent`:

- `Sheaf.Algebra.Homology.AffinePerfectColimitDescent`
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`
- `Sheaf.AlgebraicGeometry.DerivedOpenGluing`
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`
- `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms`

Their corresponding nodes `lem-pc-affine-perfect-colimit-descent`,
`lem-pc-ringed-spaces-derived-adjoint`, `lem-sc-derived-open-gluing`,
`lem-pc-perfect-affine-bounded-projective` and `lem-pc-perfect-descend-morphisms` remain
needed within the two split cases. No module or mathematical node is pruned from the
transitive proof route. The parent no longer uses them directly; its proof dependencies
are the predicate and the two induction-case nodes. The existing public imports stay
because the unchanged statement uses them. The old direct proof dependencies
`def-pc-scheme` and `def-pc-perfect-complex` are also absent from the new parent
`proof_deps`: their definitions remain necessary in the statement and the case lemmas;
neither node is transitively pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG's affine and gluing cases are mathematically appropriate, but their
current interfaces do not directly express descent on open subschemes or the conditional
two-open induction step. The split nodes isolate these interface and gluing obligations;
the established source route is retained, including morphism descent, adjunction and
both the object and morphism clauses of derived open gluing. The unit record has no
realized nodes for this item; no unit statement or step is bypassed.

The earlier sandbox attempt had no node records or report and did not compile. Its
induction application needed an explicit predicate, compactness of Xi had not been
installed, and its final simplification was unsuitable for dependent chosen pullbacks.
The repaired proof obtains the specialized predicate, unfolds its let binding, and
applies it directly: identity composition is definitionally equal here. No transport
lemma or additional hole is needed.

Read the stated proof-dependency signatures and searched the library, Mathlib, LeanFinder
and Loogle. The search found the existing compact-open induction principle, not a
perfect-descent theorem or either new case lemma. Read Stacks Tag 09RF directly at
https://stacks.math.columbia.edu/tag/09RF and checked the affine representation, overlap
identification, adjoints and gluing-map clauses against its proof. The repository's cited
`literature/stacks-project/perfect.tex` is not installed on this machine.

## New nodes

`def-pc-perfect-descent-on-open`, in `PerfectDescentOnOpen`, defines essential surjectivity
on every open-immersion presentation of an open; all data are explicit expressions, with
no existentially chosen functor or unrelated base-change map. Source: Tag 09RF's predicate
on opens. This is a definition with no hole.

`lem-pc-perfect-descent-affine-open`, in `PerfectDescentAffineOpen`, is the affine/empty
base case. Source: Tag 09RF, using the existing affine perfect representation and finite
projective colimit descent. It has a source and full proof in words and is strictly the
base case of the argument, not arbitrary-scheme descent under another name.

`lem-pc-perfect-descent-open-union`, in `PerfectDescentOpenUnion`, is the conditional
induction step. Source: Tag 09RF's two-open gluing argument, with the existing Tag 09RE,
adjunction, open direct-image restriction and Tag 08DG nodes. Unlike the original theorem,
it assumes descent separately on two pieces and proves only their union. It supplies no
base cases. Blueprint searches for Tag 09RF found no duplicate blueprint node. All new
nodes inherit the parent's chapter, unit and blueprint ancestor. No change record is
needed: existing interfaces are unchanged.


## Second reading by K4

1. **Visible interfaces — pass.** Compared the sole existing delivered module against
   the repository with `diff`; extracted its theorem signature and verified byte-for-byte
   equality. Its original docstring, hypotheses, conclusion and four public imports are
   unchanged. Only its proof and plain proof imports change. The other three modules are
   new. The existing node differs only in `proof`, `proof_deps` and `proof_origin`.
   There are no forced adaptations, target changes, or changed existing definitions.

2. **Proof and trust — pass as a decomposition.** Compiled all four files through
   `lcompile.py`, without errors or warnings. Read every declaration and scanned all
   delivered Lean text for forbidden constructs. Exactly the two reported public case
   theorems have `:= by sorry`; the predicate has a concrete body and the parent has a
   real induction proof. Scratch copies with `#print axioms` check all four declarations;
   the predicate uses only standard axioms and the theorems additionally use `sorryAx`
   from open proof obligations. No new data is chosen from any unproved existence result.
   The compactness instance follows from quasi-compactness over affine `Spec`, and the
   specialization to the identity presentation proves precisely the original conclusion.

3. **Split statements — pass.** Read both complete docstring proofs, their nodes, and
   the existing affine representation, complex-colimit descent, morphism descent,
   adjunction, open direct-image restriction and object/morphism gluing interfaces.
   Independently read https://stacks.math.columbia.edu/tag/09RF. The affine lemma is
   restricted to affine or empty opens; the union lemma assumes descent on the two
   pieces, and neither is an unconditional restatement of arbitrary-scheme descent.
   A supplied index makes the directed tail nonempty, including singleton systems.
   Zero rings and empty sources are allowed. Empty/equal/disjoint pieces require no
   extra gluing assumptions; a non-affine overlap is only required to be quasi-compact,
   which follows from quasi-separatedness. The overlap identification is descended
   between already constructed stage objects, using full faithfulness rather than
   assuming object descent on the intersection. Perfectness ensures quasi-coherent
   cohomology for the affine representation, and bounded projective terms compute
   derived base change. Searched again using different wording via LeanFinder,
   Loogle and grep, and searched repository/upstream/Mathlib sources with `rg`.
   LeanFinder found affine-spectrum and categorical infrastructure, not either case;
   Loogle did not recognize the project perfectness identifier, so it supplies no
   positive evidence. Source searches found the existing ingredients, but no duplicate
   affine-open essential-surjectivity or conditional gluing theorem. Neither large
   interface obligation can be closed in a few minutes without further decomposition.

4. **Route, imports and pruning — pass after cleanup.** Mathlib's compact-open
   induction is the shortest outer induction found. Its base case and step are exactly
   the two new obligations. The five removed direct proof imports and all seven old
   proof dependencies are accounted for under `No longer needed`; none is claimed as
   transitively pruned. The split modules retain the planned proof dependencies with
   plain imports. Removed the unused finite-presentation import from the predicate
   module and put it in the two case modules whose hypotheses use it. Existing public
   imports are retained. Read `dag/units/sk-thm-picard-semicon.json`: its realized
   statement list and sole step list are empty, and the source's affine/morphism/gluing
   route is retained, so no realized unit step is bypassed.

5. **DAG correspondence — pass after notation repair.** Checked every node's declared
   module, declaration, signature, source, chapter/unit, blueprint ancestry, creation
   record and searches against the Lean. For all four nodes, `proof_deps` is exactly
   the union of step `uses`. The parent describes the actual Lean compact-open induction
   and identity specialization. Corrected the new predicate statement and affine-case
   proof description from reversed function notation `t=f∘s` to `t=s∘f`, matching
   Lean's `f ≫ s`. No existing mathematical node statement was changed.

Second-reading changes: import placement in the three new modules; composition notation
in two new node records; complete accounting of the two retained definition dependencies
in the pruning report; this review section. No proof, signature, definition body or hole
count changed: one original hole closed, two strictly smaller holes added, net -1.
