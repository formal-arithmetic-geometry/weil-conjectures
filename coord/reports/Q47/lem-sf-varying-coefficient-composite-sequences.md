## Worker report

This delivery states `lem-sf-varying-coefficient-composite-sequences` in
`Sheaf.CategoryTheory.VaryingCoefficientCompositeSequences`, namespace
`CategoryTheory.CoefficientSequence`. The main theorem is `composite_spec`.
The live stage-1 review by Q154 is retained without modification: it reviewed a
natural-language split, not an existing Lean statement. The previous worker's
stage-1 live-wins objection therefore does not prevent this stage-2 assignment.
The sandbox initially contained only dispatcher marker files, no Lean or node.
No repair note exists for this item.

The node itself introduces its sequence categories and functors. Their data are
written explicitly in this owning module, following the same-notion helper rule;
there is no independent missing notion requiring a new definition node.
`Sequence`, `Hom`, `homId`, `homComp`, `sequenceCategory`, `mapObj`, `mapHom`,
`mapFunctor`, `paste`, and `toInverseSystem` contain real data. All postponed
proofs are public named theorems recorded in `lean.declarations`, with docstrings
specifying their sources and the corresponding steps of this same DAG node.
Every theorem proof is exactly `by sorry`. No data is chosen from existence.

Hypothesis and clause correspondence:

1. Positive levels n >= 1 are represented by `n : ℕ`, with Lean index n
   representing paper level n+1, exactly as in `def-weil-inverse-system`.
   `A : ℕ → Type uA`, `B : ℕ → Type uB`, `C : ℕ → Type uC`, and their
   separate `[∀ n, Category.{vA/vB/vC} ...]` instances supply the three
   families. Their object and morphism universes are independent. There is
   no fixed ambient category, linear structure, derived lift, or exactness.
2. `S`, `T`, `U : ∀ n, ... n ⥤ ... (n+1)` are exactly the successive
   coefficient functors S^A, S^B, S^C. No invertibility is imposed on them.
3. `Sequence A S` has `obj n : A n` and
   `transition n : obj (n+1) ⟶ (S n).obj (obj n)`. `Hom.app` gives a_n;
   `Hom.comm` says `h_n ≫ S_n.map(a_n) = a_(n+1) ≫ h'_n`, exactly
   S_n(a_n) h_n = h'_n a_(n+1) in conventional composition order.
   `homId.app` and `homComp.app` are the specified componentwise identity
   and composition. `identity_comm`, `composition_comm`, `homId_comp`,
   `homComp_id`, `homComp_assoc` postpone exactly Step 1's checks; the
   `sequenceCategory` instance uses those proofs and explicit operations.
4. The dependency's fixed-category convention is actually used:
   `toInverseSystem` specializes to constant categories and identity S,
   and calls `Functor.ofOpSequence H.transition`. This constructs the
   recorded Mathlib inverse system, rather than redefining that notion.
5. `J : ∀ n, A n ⥤ B n`, `D : ∀ n, B n ⥤ C n` give the level functors.
   `e : ∀ n, S n ⋙ J (n+1) ≅ J n ⋙ T n` is exactly
   J_(n+1) S^A_n ≅ S^B_n J_n. Similarly
   `c : ∀ n, T n ⋙ D (n+1) ≅ D n ⋙ U n` is the specified comparison
   for D. These are supplied natural isomorphisms, not arbitrary maps.
6. `mapFunctor J e` and `mapFunctor D c` are the asserted widehat J and
   widehat D. Their object data are `mapObj.obj n := (J n).obj (H.obj n)`;
   transitions are `(J (n+1)).map (H.transition n) ≫ (e n).hom.app (H.obj n)`;
   maps have components `(J n).map (a.app n)`. Substituting D,c gives exactly
   the analogous formulas. `map_comm`, `mapHom_id`, `mapHom_comp` are the
   proof-only Step 2 obligations. In particular the functor itself is not
   an opaque choice from an existential assertion.
7. The composite's level is definitionally `(D n).obj ((J n).obj (H.obj n))`.
   The first conjunct of `composite_spec` gives precisely v_n, in Lean
   left-to-right composition: `D(J(h_n)) ≫ D(e_n(H_n)) ≫ c_n(J_n(H_n))`.
   Parenthesization matches the associative formula in the node.
8. The second conjunct quantifies over every `H`, `L`, and
   `α : L ⟶ (mapFunctor J e).obj H`. There is no isomorphism hypothesis on
   α. It states `u_n ≫ U_n.map(D_n.map(α_n)) = D_(n+1).map(α_(n+1)) ≫ v_n`.
   Here u_n is explicitly `D_(n+1).map(L.transition n) ≫ c_n(L_n)`.
   Thus this is exactly S^C_n(b_n) composed with u_n equals v_n composed
   with b_(n+1), with the factored v_n retained in full.
9. `paste J D e c n` is the specified natural isomorphism for D_n J_n,
   constructed by whiskering e and c and inserting functor associators.
   `paste_app` records its component as `D(e_n(H)) ≫ c_n(J_n(H))`, rather
   than leaving the comparison unspecified. The third conjunct is actual
   functor equality `mapFunctor J e ⋙ mapFunctor D c =
   mapFunctor (fun n ↦ J n ⋙ D n) (paste J D e c)`, so it includes objects,
   transitions, and morphisms, as requested in Step 4.
10. The final three conjuncts say that widehat J, widehat D, and their
    composite preserve componentwise invertible morphisms. Each quantifies
    over a family satisfying `∀ n, IsIso (a.app n)` and concludes the same
    for every mapped component. `isIso_of_components` states Step 5's
    inverse-family argument inside the actual sequence category, so these
    are also isomorphisms there. No componentwise-isomorphism assumption
    is inserted into the preceding arbitrary-alpha square.

Dependency declarations read and used:

- `def-weil-inverse-system`: the Mathlib leaf and its recorded
  `Mathlib.CategoryTheory.Functor.OfSequence` were opened. The full
  `CategoryTheory.Functor.ofOpSequence` definition and docstring, and
  `CategoryTheory.NatTrans.ofOpSequence` signature/docstring were read.
  `toInverseSystem` uses the former directly. The latter is the recorded
  constant-category morphism convention; the varying-category square is
  necessarily the explicit square in this node's own statement.
- `Mathlib.CategoryTheory.Whiskering` supplies
  `CategoryTheory.Functor.isoWhiskerLeft` and `isoWhiskerRight` for `paste`;
  `Functor.associator` from `Functor.Category` supplies its canonical
  associators. Their definitions and docstrings were read.
- There are no other statement dependencies or proof-only imports: the
  sole proof dependency is the same inverse-system node, already imported.

Sources checked: `literature/stacks-project/categories.tex`, the full
Definition `definition-system-over-poset` (0030), `definition-functor`
(001B), and `definition-transformation-functors` (001I). They supply the
conventions, as the node explicitly says; the varying-category calculation
is the agent-formulated proof in this node, not a theorem attributed to
Stacks. The module and each declaration document this distinction.

Edge cases checked before writing:

- The first positive level is Lean n=0, and its transition is the arrow
  from paper level 2 to S_1(H_1). No level-zero coefficient or extra
  transition is required by this reindexing.
- Empty level categories give the legitimate empty sequence category;
  there is no `Nonempty`, chosen object, or nonvacuity hypothesis.
- Constant categories and identity coefficient functors reduce to the
  recorded ordinary inverse-system convention by `toInverseSystem`.
- Terminal categories, identities, and zero objects (when present) are
  admitted without additional structure or restrictions.
- Arbitrary noninvertible α is retained. The final iso assertions have
  their own explicit antecedents only.
- No abelian, additive, finite, bounded, or derived assumptions occur.
  All six category universes are independent, including object/hom sizes.
- The pasted comparison uses the supplied isomorphisms and their canonical
  whiskering. Actual functor equality is appropriate: both sides have
  identical object and arrow data and equal transition data by map_comp,
  paste_app, unit laws, and proof irrelevance.

Searches (2026-10-22):

- `msearch.py ... leanfinder` with “Functors on inverse sequences with
  varying categories and natural isomorphisms between transition functors
  compose using the pasted comparison”: 8 results, including
  `ComposableArrows.map'_inv_eq_inv_map'`, `Functor.OfSequence.map_comp`,
  `Functor.OfSequence.map_comp_assoc`, and small-object iteration maps.
  These concern fixed-category diagrams or different constructions;
  none states the varying-level sequence construction with its pasted
  coefficient comparisons and explicit arbitrary-alpha square.
- `msearch.py ... loogle 'Dialgebra, Comma, Functor.ofOpSequence'` reported
  unknown identifier Dialgebra, so a successful replacement query was
  made: `loogle '"ofOpSequence"'` returned 5 results, namely
  `Functor.ofOpSequence`, its object/successor-map lemmas, and
  `NatTrans.ofOpSequence` and its app lemma. They give the dependency's
  fixed-category convention and do not give this varying-category theorem.
- `msearch.py ... grep 'semilinear.*(sequence|tower)|Dialgebra|varying.*categor'
  CategoryTheory`: zero hits in the search service's Mathlib subtree.
- Direct `rg` of local Mathlib CategoryTheory for Dialgebra/dialgebra and
  sequence/tower structures found no relevant construction. The full
  `Functor.OfSequence` declarations were read directly.
- Direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  varying-coefficient terminology, VaryingSequence, and the item ID found
  specialized ring/sheaf tower modules, not this general categorical
  theorem. The exact item ID has no occurrence in `lean/WeilConjectures`.
  Searches for the new namespace and declarations found no existing name.
  The node's existing stage-1 searches independently record the same
  distinction from Grothendieck.map and fixed-category OfSequence.

No statement correction, new dependency, or dependency repair was needed.
There is no STATEMENT-DISPUTED flag. The item JSON changes only `lean`;
the stage-1 statement, split, sources, and independent review are retained.

Validation: the delivered module compiled separately via `scompile.py`
against the live published library. Both the sandbox and actual library
module-name compile passed cleanly (3.6 s and 2.5 s), with no errors or
unexpected warnings. The initial namespace error on the whiskering names
was repaired by using `Functor.isoWhiskerLeft/Right` from the read source.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
