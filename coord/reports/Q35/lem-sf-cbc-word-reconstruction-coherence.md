## Worker report

The module `Sheaf.CategoryTheory.WordReconstructionCoherence` states
`CategoryTheory.WordReconstruction.word_reconstruction_coherence`, with exactly one
postponed theorem proof, `sorry`. All helper data are explicit constructions from Mathlib.
The source is fix-lem-exchanges Proof Step 5; I read its current
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/fix-lem-exchanges.proof.md`,
including the composition compatibility and independence paragraph, and all eight proof
steps of this extracted categorical node. No statement correction is needed.

Hypothesis correspondence:

- The arbitrary index set is `S : Type i`, and its directed generating edges are
  `[Quiver.{e} S]`. No finiteness or nonemptiness condition is imposed on either.
- The categories are `D : S → Type u`, `T : S → Type u'`, with
  `[∀ s, Category.{v} (D s)]` and `[∀ s, Category.{v'} (T s)]`. Object and morphism
  universes on the two sides are independent and explicitly declared.
- A full subcategory is encoded by its object predicate `E : ∀ s, D s → Prop`.
  All ambient morphisms are retained. Since the comparisons are natural on all of D,
  invertibility of their components at `E s x` is exactly the assertion that their
  restrictions to this full subcategory are natural isomorphisms. No closure under
  isomorphism or other extra property of E is assumed.
- Reduction and reconstruction are `R : ∀ s, D s ⥤ T s` and
  `L : ∀ s, T s ⥤ D s`. The supplied unit is
  `η : ∀ s, 𝟭 (D s) ⟶ R s ⋙ L s`; `hη` is precisely its invertibility on E.
  These are arbitrary functors and a natural transformation; there is no adjunction
  or faithfulness assumption.
- `F` and `G` give the two functors for each edge. `hF` says exactly
  `E s x → E t ((F f).obj x)`.
- `qEdge` is the given natural transformation `F f ⋙ R t ⟶ R s ⋙ G f`;
  `hq` is its componentwise invertibility on E. Its construction is not assumed.
- Mathlib's `Functor` already supplies preservation of identities and compositions;
  `NatTrans` supplies naturality for every ambient morphism. Thus none of the
  category, functor or naturality laws needs a duplicate custom structure.

Conclusion correspondence, in theorem order:

1. `Quiver.Path` is the finite composable edge word. `wordFunctor` evaluates `.nil`
   as the identity and `.cons W f` as `wordFunctor F W ⋙ F f`, fixing the recursive
   parenthesization required in the node, and likewise for G.
2. The existential `q` has the required natural-transformation type at every word.
   `IsWordComparison` spells out the identity empty map, prescribed singleton map,
   and the displayed one-edge recursion. Mathlib writes first-then composition:
   `whiskerLeft F_W q_f ≫ whiskerRight q_W G_f` is the node's
   `(G_f q_W) ∘ (q_f F_W)`.
3. The next conjunct quantifies over every other family satisfying just these
   defining equations and concludes `@q' = @q`. The explicit `@` ensures equality
   of the entire family, including the implicit endpoints, with no unresolved indices.
4. The next conjunct, for each W and `E s x`, simultaneously asserts preservation
   `E t ((wordFunctor F W).obj x)`, invertibility of `(q W).app x`, and invertibility
   of the reconstructed component. As noted above, this is exactly restricted
   natural invertibility, not invertibility on the whole ambient category.
5. `reconstruct` is the actual natural transformation
   `whiskerLeft A (η t) ≫ whiskerRight q (L t)`, so its component is
   `η_t(A x) ≫ L_t.map (q.app x)`. This is the specified a_W or a_E.
6. The concatenation conjunct uses Mathlib `W.comp V`, with W first and V second.
   `wordCompIso F W V` and `wordCompIso G W V` insert precisely the canonical
   reassociations and unitors. Thus
   `q(WV) ≫ R_s(d)` equals `R_r(c) ≫ (q_V F_W) ≫ (G_V q_W)` in diagrammatic
   order, which is the node's displayed concatenation equality after identification.
7. The next conjunct is the whole natural-transformation equality `a_empty = η s`.
8. `Expression.empty`, `.edge`, and `.comp` encode every binary expression, with
   empty identity factors allowed at arbitrary finite depth. `Expression.flatten`
   reads its ordered edge word; `.functor` retains its actual parentheses and units.
   `Expression.comparison` starts from the given edge and identity maps and uses
   exactly the node's binary recursion. `Expression.flattenIso` builds c_E/d_E
   recursively out of `wordCompIso`, associators, unitors, and their whiskerings.
9. The last conjunct quantifies over every expression A. Its first equality is
   `q_W ≫ (d_E R_s) = R_t(c_E) ≫ q_E`; its second is
   `a_W ≫ L_t(d_E R_s) = c_E ≫ a_E`. These are exactly both displayed equations,
   expressed in Mathlib's diagrammatic order. They are equalities of transformations
   on all of D_s and carry no predicate E restriction.
10. Every W with the same ordered edges as A is covered by substituting the equality
    `W = A.flatten`. All canonical associators and unitors used here have identity
    components, so the recursively specified flattenings are precisely the canonical
    ones in the node. These two equations give independence of parentheses and
    inserted empty factors; no separate extra axiom or strengthened conclusion occurs.

The nine helper declarations listed in `lean.declarations` implement notation already
introduced by this node: word evaluation, its concatenation identification, binary
expression syntax and its evaluations, the defining equations, and reconstruction.
They are owning-node helpers as explicitly authorized in the brief, rather than
additional independent mathematical prerequisite nodes. No auxiliary theorem or
existence choice supplies their data. There are no new nodes or dependency repairs.

Dependency declarations read and used:

- `def-nagata-category`: `CategoryTheory.Category` from
  `Mathlib.CategoryTheory.Category.Basic`, including `CategoryStruct` and all laws.
  It is a Mathlib leaf; its `mathlib_match` is the usable binding, so no lean repair.
- Proof leaf `lem-amb-natural-transformation-whisker-exchange`:
  `CategoryTheory.Functor.whiskerLeft_comp_whiskerRight` from
  `Mathlib.CategoryTheory.Whiskering`, read with its complete signature. This module
  is a public import because its whiskerings are also used by the statement helpers.
- Mathlib `Quiver.Path`, `Quiver.Hom.toPath`, `Quiver.Path.comp` are reused for
  words; `Functor.associator`, `.leftUnitor`, `.rightUnitor`, `isoWhiskerLeft`,
  and `isoWhiskerRight` supply all canonical identifications.

Edge checks, performed by unfolding the definitions and checking the categorical types:
empty S (all families and assertions empty); no edges (only empty paths, but arbitrarily
nested empty expressions still covered); empty E (invertibility requirements vacuous,
while both coherence equations still hold on all of D); empty D or T whenever the supplied
functors exist; empty W/V on either side of concatenation; a singleton (left unitor and
preservation of identities recover qEdge); three edges in both binary bracketings;
an empty factor on either side or nested inside any binary expression; identity R/L
and identity η; and nonfaithful reduction/reconstruction. No excluded edge case or
false statement was found. The implicit source of `wordFunctor` is fixed outside its
recursive endpoint binder, so this is structural path recursion and its `.cons`
equation reduces during elaboration.

Searches for an existing exact statement:

- `msearch.py leanfinder`: "A family of natural transformations intertwining indexed
  functors extends uniquely to composable words, compatibly with reassociation and
  identity factors". Eight results, chiefly `ComposableArrows.homMk` and
  `NatTrans.ofSequence`, concern diagrams in one category, not the indexed
  reduction/reconstruction and both flattening equations here.
- `msearch.py loogle`: `CategoryTheory.Functor.associator, CategoryTheory.NatTrans`:
  zero results.
- `msearch.py grep`: `liftNatTrans|pathComposition|associator_hom_app` in
  Mathlib/CategoryTheory: 25 hits. Read `Paths.liftNatTrans` and `Paths.liftNatIso`
  in `PathCategory/MorphismProperty.lean`; these extend object-component squares
  for functors from a path category into a fixed category. They are not this theorem.
- `msearch.py leansearch`: "Natural transformations between indexed functor composites
  extend uniquely from generating arrows to paths and commute with reassociation and
  a reconstruction unit". Eight results including `Paths.liftNatTrans`,
  `Sigma.natTrans`, and `NatTrans.pi'`; none supplies the stated construction and
  coherence for the supplied R, L and η.
- `rg` in project `lean/WeilConjectures`, `lean/Sheaf`, and `dag/nodes` searched
  `word.reconstruction|WordReconstruction|reconstruction.coherence|flattening` and
  binary expressions/parenthesization. Also searched the item id in upstream Lean,
  and the new full names in upstream name records, Mathlib, and both Lean trees.
  No duplicate generic statement or declaration exists. The parent's existing
  `SfCbcWord`/`SfCbcExpression` are specifically indexed by schemes and their
  geometric operations; they cannot express this arbitrary indexed categorical
  prerequisite. `ExactDerivedTransformationPasting.Word` instead has exact
  functors and derived categories, also a different notion.

Validation: `scompile.py Q35 lem-sf-cbc-word-reconstruction-coherence` compiled the
module both as sandbox and at its library module path, in 2.0 s and 1.8 s respectively,
with no errors or warnings. Every universe and variable is explicitly bound;
`set_option autoImplicit false` is in the file. Every line is at most 100 characters.
The natural-language proof docstring follows all eight DAG proof steps.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
