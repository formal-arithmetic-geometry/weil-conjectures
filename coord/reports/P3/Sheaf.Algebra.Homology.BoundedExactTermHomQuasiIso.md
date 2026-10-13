## What changed

Proved the body of CategoryTheory.quasiIso_homComplex_map_of_bounded_exact_terms
without changing its signature or visibility. The proof uses induction on a natural
interval width, shortening the source by Mathlib's real stupid truncation. Private,
fully proved helpers show that internal Hom from zero is zero, that it preserves
short exact sequences, and that exact-term Hom preservation transports along a
source isomorphism. The interval proof explicitly transfers bounds and exactness
to the smaller tail, and handles reversed bounds using (b-a).toNat.

Added proof-only imports of Sheaf.Algebra.Homology.SingleDegreeExactTermHomQuasiIso,
Sheaf.Algebra.Homology.StupidTailHomShortExact, and
WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns. The first new module states the
single-degree calculation. The second states only the existence of the natural
short exact Hom sequences and their arrow identifications. The original module
uses the proved upstream HomologicalComplex.HomologySequence.quasiIso_τ₂ for
the remaining two-out-of-three argument and transports quasi-isomorphisms through
arrow isomorphisms. The upstream lemma derives its conclusion from long exact
homology sequences and the five lemma.
No definitions, existing interfaces, or other group's modules were changed.

Compiled all three modules in import order using lcompile.py. All compile without
warnings. The original module contains no sorry, and each new module contains
exactly its one named public theorem with proof := by sorry.

## Proved and sorry left

Closed the one original hole:
CategoryTheory.quasiIso_homComplex_map_of_bounded_exact_terms
(node lem-pc-bounded-exact-term-hom-quasi-iso).

Added two holes, each strictly a part of the original argument:

- CategoryTheory.quasiIso_homComplex_map_of_single_degree_exact_term
  (node lem-pc-single-degree-exact-term-hom-quasi-iso), the one-degree base case,
  assuming exactness only for the sole possibly nonzero source term.
- CategoryTheory.exists_homComplex_stupid_tail_shortExact
  (node lem-pc-stupid-tail-hom-short-exact), the natural split-sequence construction.
  It does not assert any quasi-isomorphism and has no exactness or boundedness
  hypothesis on the source terms.

This delivery is a decomposition, not a completed axiom-free proof: one upper
hole closed and two lower holes added (net -1 before any closure pruning). There
are no other holes in the delivered files, no holes in definitions, and no data
selected from unproved existence statements in definitions.

## No longer needed

No original imports, planned nodes, or planned modules are pruned. The exact-functor
criterion and cohomology comparison remain dependencies of the new single-degree
node; long exact cohomology and the five lemma are used through the proved upstream
quasiIso_τ₂ lemma. The old direct proof dependencies
lem-sp-exact-functor-preserves-homology and
lem-weil-pbc-exact-functor-complex-cohomology move to the new single-degree
node; they remain transitively needed, rather than pruned. The Hom complex definition and quasi-isomorphism definition remain needed.
Removed experimental proof imports of Mathlib.Algebra.Homology.Embedding.CochainComplex
and a redundant direct Mathlib.Algebra.Homology.Embedding.StupidTrunc import;
they were not imports in the original delivered baseline. The first is unnecessary
because no canonical cohomological truncations are used; the second is provided by
the public statement import of StupidTailHomShortExact. Neither removes a baseline
module from the target closure. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's broad Mathlib dependencies suffice for exact functors and long exact
sequences but do not provide the concrete singleton Hom identification or the
natural short exact sequence for the chosen sheaf-valued Hom complex. The new
nodes isolate precisely these missing constructions. The planned finite induction
is now written explicitly in Lean, rather than marked as an elementary step that
would implicitly require unstated interfaces.

Mathlib search was run through msearch.py: LeanSearch was unavailable (Internal
Server Error); Loogle's QuasiIso, Functor query returned no hits; LeanFinder found
generic mapping-cone, homology-sequence, and exact-functor tools, with no matching
sheaf Hom construction. Grep of Mathlib and rg of both library roots found no
existing statement for either new lemma. Blueprint searches for stupid tail and
single degree found no duplicate. The unit's realized statement and step lists
are empty, and the prescribed finite-duality route is retained.

The literature directory on this machine contains only lists and import tools,
so the cited Stacks texts were read at their official online tags 0A8X, 08DM,
and 0117. The new proof sketches are marked as agent adaptations of the original
bounded Hom plan, rather than falsely attributed as verbatim Stacks proofs. Tag
08DM states the strictly perfect RHom calculation, not the general exact-term
criterion verbatim; the exact-term version uses the same Hom formula together
with the exact-functor criterion and finite split filtration.

Edge cases checked: the single-degree theorem permits its distinguished term to
be zero; the short exact tail construction permits unbounded sources and targets
and requires no exactness of infinite products; all-zero sources, negative degree
bounds, a=b, b<a, and a nonzero source differential from a to a+1 are covered by
the finite induction. The tail cutoff preserves the latter differential only
inside the tail, and its removal is exactly what the split Hom sequence handles.

## New nodes

lem-pc-single-degree-exact-term-hom-quasi-iso:
lean/Sheaf/Algebra/Homology/SingleDegreeExactTermHomQuasiIso.lean. Isolates step 1
of the parent argument, using product projections, additivity of postcomposition,
the exact-functor criterion and its natural homology comparison. No boundedness
of the second variable is added. Its sole exact-term hypothesis is at the
possibly nonzero degree. Source: Stacks 0A8X, 08DM, and 010N.

lem-pc-stupid-tail-hom-short-exact:
lean/Sheaf/Algebra/Homology/StupidTailHomShortExact.lean. Isolates step 2:
extension by zero and restriction of product factors, with their chain-map
identities and naturality in f. It supplies a morphism of short exact sequences
and three isomorphisms in the arrow category. The five-lemma consequence uses
the proved upstream quasiIso_τ₂ lemma, rather than a new hole. Source: Stacks
0A8X and the split-sequence input to 0117. No change records or forced adaptations.

## Second reading by P3

1. Interface comparison: PASS. Read the diff of the existing module against the
   repository. Its sole existing theorem signature is byte-for-byte identical
   through the result type; no existing definition or visibility changed.
   The two other modules are new public statements. There are no adaptations
   or statement-change records. The existing node changes only proof,
   proof_deps and proof_origin.
2. Proof and axioms: PASS as a decomposition. Compiled all three modules in
   import order with lcompile.py and compiled scratch copies with explicit
   #print axioms for all three public theorems. The only axioms reported are
   propext, Classical.choice, Quot.sound and sorryAx from the two declared
   remaining holes. The upstream quasiIso_τ₂ reports only the three standard
   axioms. No prohibited declarations, definition holes, or arbitrary witness
   constructions occur in this delivery. The short-exact existence theorem
   is eliminated only inside a proposition proof; no definition chooses its
   unspecified data.
3. Split statements: PASS. Independently checked both docstring arguments
   against the Hom product and differential formulas, including a zero sole
   term, negative k, unbounded complexes, and a nonzero differential P^k to
   P^(k+1). Extension at k has no incoming differential because P^(k-1)=0;
   restriction to the tail uses only p and p+1. Degreewise product splitting
   supplies exactness without any assertion that infinite products preserve
   epimorphisms. The single-degree lemma has just the one exact-term
   hypothesis; the tail lemma asserts no quasi-isomorphism. Both are strictly
   smaller parts of the original argument, with matching nodes and complete
   proof sketches. Independent LeanFinder, Loogle and grep searches used
   different queries; Mathlib HomComplexSingle concerns groups of cochains,
   not this internal sheaf Hom complex. Neither new statement duplicates an
   existing declaration. Closing either hole requires constructing the product
   identifications and chain maps, rather than a few-minute lemma application.
   Checked the cited official Stacks pages: [Hom formulas](https://stacks.math.columbia.edu/tag/0A8X),
   [strictly perfect calculation](https://stacks.math.columbia.edu/tag/08DM),
   [exact functors](https://stacks.math.columbia.edu/tag/010N), and
   [long exact sequence](https://stacks.math.columbia.edu/tag/0117).
   The generalized statements are correctly labelled agent adaptations.
4. Route and pruning: PASS after repair. Broader upstream grep found the
   already proved HomologicalComplex.HomologySequence.quasiIso_τ₂ in
   WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns. Replaced the
   duplicated private five-lemma helper with that lemma and replaced the
   direct proof-only HomologySequenceLemmas import with its upstream module.
   Other imports provide statement vocabulary, sheaf abelian/homology
   instances, the singleton, or the stupid tail; all added proof-only imports
   are plain imports. A compiler check confirmed that removing the tail
   module's abelian/filtered-colimit imports loses the HasZeroObject instance
   required by single and stupidTrunc; the limits import alone does not replace
   them, so they were retained. No baseline module or dependency is pruned: the exact
   functor nodes move to the single-degree node, while long exact cohomology
   and the five lemma remain used through the proved upstream lemma. The
   sk-thm-picard-duality realized statement/step lists are empty and the
   bounded-filtration step of finite duality is retained.
5. Nodes: PASS after repair. Checked each proof_deps equals the union of step
   uses, the new signatures match Lean verbatim, and all required new-node
   fields are present. Updated the parent's proof and proof_origin to describe
   the upstream two-out-of-three application. Its original statement and all
   interface metadata are unchanged. The new nodes still describe exactly
   the two remaining constructions.

Second reading changed the duplicated five-lemma proof to the proved upstream
quasiIso_τ₂ application, its proof-only import, the parent proof records and the
report. No theorem signature, definition, or remaining hole changed. The result
remains one original hole closed and two holes added, a decomposition with net -1.
