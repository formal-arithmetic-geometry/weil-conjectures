## Worker report

The delivery states `CategoryTheory.enriched_coend_homotopy_invariance` in
`Sheaf.CategoryTheory.EnrichedCoendHomotopyInvariance` and adds the missing
`CategoryTheory.enrichedCoend` construction in
`Sheaf.CategoryTheory.EnrichedCoend`.  The latter is the actual multicoequalizer
of the two enriched action maps, with `enrichedCoendIndex` recording the two
maps.  The theorem proof is `sorry`, as required at stage 2.

The theorem first chooses the Kan--Quillen model-category data whose fibrations
and cofibrations are Mathlib's simplicial-set structures and whose weak
 equivalences are `SSet.Enhanced.IsWeakHomotopyEquivalence`.  For a small
simplicial category `A`, it has two cellular characterization clauses: one for
`A` and one for `Aᵒᵖ`.  Each quantifies an enriched diagram enrichment `E`, a
simplicial tensor/cotensor `T`, its projective model structure `P`, and a diagram
`F`; the existential `hI` supplies the initial object inherited from the model
category.  `enrichedProjectiveCellCharacterization` renders cofibrancy as
`@IsCofibrant ... hI F` and the conclusion as an arrow-retract of a transfinite
composition of pushouts of the free boundary maps.  The free maps are exactly
`(P.free_diagram b).map (SSet.boundary k).ι`, with explicit endpoint transports.

The first invariance clause binds right enriched modules `V,V'`, a left module
`H`, and an enriched map `f : V ⟶ V'`; its hypothesis is objectwise weak
homotopy equivalence using the component map obtained from
`(eHomEquiv SSet).symm (ForgetEnrichment.homTo SSet ...)`.  Its conclusion gives
an induced map `g` of coends, states its value on every coproduct summand using
`Multicoequalizer.π`, and states that `g` is a weak homotopy equivalence.  The
second clause binds a right module `V`, left modules `H,H'`, and `f : H ⟶ H'`,
with the same objectwise hypothesis and the analogous summand equation and weak
homotopy conclusion.  No fibrancy or cofibrancy assumption is placed on the
varying module, and no Kan condition is placed on `A`.

The new definition module renders the coend formula as follows.  Its left
multispan summand at `(a,b)` is
`(V.obj (op b) ⊗ sHom a b) ⊗ H.obj a`, and its right summand at `a` is
`V.obj (op a) ⊗ H.obj a`.  The first action map is the uncurrying of
`V.map (op b) (op a)` tensored with the identity on `H.obj a`; the second action
map uses the associator, the simplicial-set braiding, and the uncurrying of
`H.map a b`.  The definition is therefore the displayed
`V(b) × A(a,b) × H(a) ⇉ V(a) × H(a)` coequalizer, with products represented by
Mathlib's cartesian tensor on simplicial sets.

The recorded dependency declarations used are:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, declarations
  `SSet.Enhanced.IsWeakHomotopyEquivalence` and the simplicial-set conventions;
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`, declarations
  `CategoryTheory.SimplicialDiagramEnrichment`,
  `CategoryTheory.ProjectiveSimplicialModelStructure`,
  `CategoryTheory.SimplicialTensorCotensor`, and its `free_diagram` field;
- `Sheaf.CategoryTheory.EnrichedCoend`, declarations
  `CategoryTheory.enrichedCoendIndex` and `CategoryTheory.enrichedCoend`;
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, the stated Kan--Quillen
  model data and `SSet.KanQuillen.weakEquivalenceStructure` (used privately as a
  proof-plan import).

Edge cases checked were the empty index category (the coproducts and
multicoequalizer are still defined), an empty simplicial set, zero-dimensional
boundary cells `k = 0`, the empty family of cells, zero objects, and the
opposite-category variance.  The cellular property allows a transfinite chain
of length zero and arrow retracts.  The two action maps retain the identity and
associativity data of the enriched functors, so the coend is defined without a
nonemptiness or local-Kan assumption.

Searches for an existing coend declaration were made with `msearch.py` LeanFinder
(semantic queries for an enriched simplicial coend and for a projectively
cofibrant weight), Loogle (`"coend" "EnrichedFunctor" "SSet"` and
`"coend" "cofibrant"`), whole-tree grep of Mathlib, `WeilConjectures`, and
`lean/Sheaf`, and `rg` for `coend`, `Coend`, and `enrichedCoend`.  The results
were generic multicoequalizers, bar constructions, and ordinary model-category
cofibrant-object facts; none states this balanced enriched simplicial coend.
The target's existing searches independently found no matching homotopy
invariance theorem.  Consequently the new definition node
`def-coef-enriched-coend` is required and is cited by the item.

## Second reading by NJ

I reread the target JSON, the source place A.3.3.2/A.3.3.5, both modules, and
the new definition node.  The first two theorem clauses match the node's
`B=A` and `B=A^{op}` cellular alternatives; the free maps include every
`b` and every `k ≥ 0`, and the explicit endpoint equalities only transport the
same free boundary arrow.  The coend definition has exactly the two displayed
action maps and uses the same objects `V(b)`, `A(a,b)`, and `H(a)`.  Each
invariance clause has precisely one objectwise weak-equivalence hypothesis and
one canonical summand equation followed by weak homotopy equivalence.  No local
Kan, variable-module cofibrancy, or fibrancy hypothesis was introduced.  The
opposite variance in the second clause is represented by `Aᵒᵖ` in the first
cellular clause and by the explicit `op a` in the coend summands.  I found no
mismatch requiring a change.

## New nodes

`def-coef-enriched-coend` is a new definition node because the searches found
no existing declaration of the balanced enriched simplicial coend.  Its source
is HTT Appendix A.3.3.5, printed p. 871.  The module defines the multispan
index and its multicoequalizer with real data; no theorem is postponed in that
module.  The item cites this node in `stmt_deps`.

## Maintainer review fix

The delivered invariance clauses had no hypothesis that `H` (first clause) or
`V` (second clause) is projectively cofibrant. The node assumes it ("If $H$ is
projectively cofibrant ...", "If $V$ is projectively cofibrant ..."). Without it
the statement is false: take $A=BG$ for a nontrivial discrete group $G$ and $H$
the point. Then $V\otimes_A H=V/G$, and the weak equivalence $EG\to *$ gives
$BG\to *$. The fix adds `CategoryTheory.EnrichedProjectivelyCofibrant m F`:
`F`, viewed as an object of `E.Diagrams`, is cofibrant in an enriched projective
structure `P` of lem-coef-simplicial-projective-model-calculus over the
Kan–Quillen `m`. Every such `P` has the objectwise trivial fibrations, and the
`represents`/`projection` fields identify the arrows of `E.Diagrams` with the
enriched transformations, so this does not depend on the choice of `E`, `T`, `P`.
The fix adds this hypothesis to the first clause for `H` and to the second
clause for `V`. Nothing else changed.
