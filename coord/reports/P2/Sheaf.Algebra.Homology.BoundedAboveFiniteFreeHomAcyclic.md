## What changed

Replaced the sole sorry in
`Sheaf.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic` by a complete Lean
combination of two strictly separate steps of the existing proof plan. The proof
chooses the bounds, chooses a finite-free isomorphism in each degree, applies
finite-free internal-Hom exactness to each exact short complex `A.sc q`, and
applies the bounded exact-column totalization criterion. The original theorem
signature and public imports are unchanged.

Added `Sheaf.Algebra.Homology.FiniteFreeInternalHomExactSequence` and
`Sheaf.Algebra.Homology.BoundedHomExactColumns`, each with one named public sorry.
Their docstrings give explicit proofs in words, including local lifts, finite
cover refinements, the signs, and the bottom-degree obstruction. Updated the
original node's proof and proof dependencies and added corresponding new nodes.

All three modules compile in import order using lcompile.py. No definition is
introduced or changed, and no other library module is adapted.

## Proved and sorry left

Closed the original hole in
`CochainComplex.acyclic_homComplex_of_boundedAbove_finiteFree`
(node `lem-sc-bounded-above-finite-free-hom-acyclic`). This is a decomposition,
not a sorry-free proof of the mathematical result: its proof still rests on the
two newly stated intermediate theorems below. Holes closed: 1. Holes added: 2.
Net holes: -1.

- `CochainComplex.finiteFree_internalHom_exact_sequence`, node
  `lem-sc-finite-free-internal-hom-exact-sequence`, remains sorry. This is solely
  the termwise exactness argument for one finite free module and one exact short
  complex; it has no complexes, bounds, or totalization in its statement.
- `CochainComplex.acyclic_homComplex_of_bounded_exact_columns`, node
  `lem-sc-bounded-hom-exact-columns`, remains sorry. This is solely the finite
  descending totalization argument from exact internal-Hom columns; it assumes
  neither finite freeness nor acyclicity of the second complex.

Edge cases checked mathematically: rank zero makes the internal Homs zero;
exact short complexes need not have injective first or surjective second maps;
the totalization argument takes zero primitives when the diagonal interval is
empty; the bottom degree is forced by exactness with zero incoming object.
Independent site-object, site-morphism, and module universes are retained in
both new statements.

## No longer needed

Removed the original proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`, node
`lem-sc-finite-free-internal-hom-exact`, from this module's direct proof route.
The arbitrary-universe exact-sequence input replaces it. This does not claim
that the old module is globally unreachable: other users may still need it.
No other original imports, nodes, or modules were pruned.

The exploratory fixed-degree restatement was deleted from the sandbox and is
not delivered; it did not constitute a genuine reduction.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt contained only the original sorry and searches.
The finite-free exactness declaration named by the DAG uses a single universe
for site objects, site morphisms, rings, and module sections. The assigned item
has independent u, v, w and an internal-Hom output in max u v w. Applying the
existing declaration therefore does not cover the assigned signature. The new
termwise lemma retains the assigned universes and asks only for middle
exactness, the precise input of the descending argument.

The local literature file named in the node is absent on this machine. Read
[Stacks Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8), its predecessor
[Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7), and
[Hom complexes, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X) online.
0GM8 refers to 0GM7; neither prints the explicit descending argument in the
original node. The new nodes mark that detailed argument as agent-written,
following the original node's plan, rather than attributing its exact wording
to Stacks. No source or target statement has been weakened.

Searches were run with Lean Finder, Loogle, grep, and LeanSearch. LeanSearch
returned Internal Server Error and is recorded unavailable. The searches and
local source inspection found K-projective results for ordinary morphism Hom,
not the required internal Hom of arbitrary ringed-site module sheaves.
Blueprint searches for "hom acyclic" and "free exact" found no matching
imported blueprint statement. The unit record has no realized nodes for this
calculation; the existing finite-free/descending route stays unchanged.

## New nodes

`lem-sc-finite-free-internal-hom-exact-sequence` records the exact-sequence
finite-free input in arbitrary universes and its new Lean module. It is
strictly termwise and includes rank zero.

`lem-sc-bounded-hom-exact-columns` records the finite-diagonal descending
argument independently of the finite-free input and its new Lean module.

No change record is needed: every existing signature and visibility stays
identical, and the new imports in the assigned module are proof-only.

## Second reading by P2

1. **Visible declarations and statements.** I compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; only its proof and proof-only imports changed. The two added theorem signatures match their DAG `lean.statement` fields and introduce no altered existing declaration.

2. **Compilation and proof audit.** I compiled all three modules in import order with `lcompile.py --all`; compilation succeeds. The target theorem has no `sorry`. The only remaining `sorry`s are the two named split-off public theorems, each documented with a complete mathematical proof plan. No definitions contain `sorry`, and no forbidden `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration was added.

3. **Truth and strength of split statements.** `finiteFree_internalHom_exact_sequence` is the termwise finite-free exactness claim in arbitrary universes, allowing non-monic and non-epic source maps. `acyclic_homComplex_of_bounded_exact_columns` is the independent finite-diagonal descending totalization claim from exact internal-Hom columns. Both are strictly simpler than the target, retain the needed hypotheses, and cover rank-zero and empty-diagonal edge cases without strengthening or weakening the target.

4. **Route and pruning.** The target proof follows the unit route: choose the two bounds, establish every internal-Hom column by finite-free exactness, then apply bounded exact-column totalization. The old single-universe finite-free import is no longer used and is removed from the direct proof route; no other original import is unused. The unit record and realized route are unchanged.

5. **DAG agreement and sources.** The target node proof and dependencies name exactly the two lemmas used in Lean. Both new nodes have matching statements, declarations, proof descriptions, source references, and split status. Searches and repository inspection found no existing declaration duplicating either theorem.

I changed only the report by adding this second-reading record; no Lean source or node statement was changed during review.
