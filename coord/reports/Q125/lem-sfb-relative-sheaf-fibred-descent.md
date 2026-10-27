## Worker report

The module `Sheaf.CategoryTheory.RelativeSheafFibredDescent` states
`CategoryTheory.isModuliStack_of_faithful_relative_sheaf`, with `sorry` as its whole proof.
Its three real helper definitions express the relative sheaf hypothesis in representatives;
they belong to the relative presheaf already introduced in the item's own statement.
There are no new independent notions or dependency repairs. No statement or dependency
list changed. Source read: literature/stacks-project/stacks.tex, Tag 0CKJ,
lemma-relative-sheaf-over-stack-is-stack, lines 1334–1395, both descent paragraphs.
The latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof were also read;
this remains the inherited supporting moduli/descent input, with no change to the unit.

Hypothesis-by-hypothesis and clause-by-clause translation:

- The scheme S is `{S : Scheme.{u}}`; its schemes are `Over S`.
- The size convention is metatheoretic, as its recorded lean.convention says. We use
  explicit u, v₁, w₁, v₂, w₂, with no relation imposed between the total-category sizes.
  The site has exactly the universes inherited from `Scheme.{u}` and `Over S`.
- F and G are `BasedCategory.{v₁,w₁} (Over S)` and
  `BasedCategory.{v₂,w₂} (Over S)`; q is their `BasedFunctor`, so it commutes with
  projection, rather than being an arbitrary functor.
- `hF : IsFibredInGroupoids F` states the lifting and unique cartesian-factorization
  conditions. `hG : IsModuliStack G` includes `IsFibredInGroupoids G`, so both
  groupoids and the target étale stack hypothesis are present, without redundant assumptions.
- Every q_T is faithful: `hq : ∀ T : Over S, (moduliFiberMap q T).Faithful`.
  This uses the actual functor on fibres, not faithfulness of an unrelated functor.
- For every T and y in G(T), the relative representatives are
  `FibredRelativeSection q y h`, for every `h : V ⟶ G.p.obj y`. Taking y in
  the total category with base `G.p.obj y` is equivalent to quantifying over T
  and y in its fibre, since a fibre object includes its base equality.
- A representative consists of x over V, its base equality, and an actual
  `comparison : q.obj x ⟶ y` with `G.p.IsHomLift h comparison`.
  To compare with the displayed pair, choose any cartesian lift b : h*y → y.
  Its universal property factors comparison uniquely as ψ ≫ b, with ψ vertical.
  Every vertical arrow in a CFG is invertible. Thus φ=ψ⁻¹ gives exactly the
  node's φ : h*y ≅ q(x). Conversely φ gives comparison=φ.inv ≫ b.
  No arbitrary comparison or choice from an existence axiom is substituted for this map.
  The encoded total arrow avoids choosing a cleavage in the Lean data.
- Isomorphism of representatives and restrictions are
  `FibredRelativeSection.Restricts a r s`: existence of c over a with
  `q.map c ≫ s.comparison = r.comparison`. When a is the identity this says
  q(c)φ=φ' after inverting the preceding ψ's. When a is a general base map,
  cartesian factorization in F identifies it with a vertical isomorphism from
  r to the pullback of s; functoriality identifies the comparison. It therefore
  says equality after restriction of the relative classes, with the correct orientation.
- `hrelative : HasEtaleSheafRelativeClasses q` quantifies over every slice object h,
  every covering sieve R in `(Scheme.etaleTopology.over S) V`, and a relative
  representative for every arrow of R. The matching condition is existence of
  the above arrow for every arrow of `R.arrows.category`. This is equality of
  the two restricted classes, not a chosen compatible family of arrows; no
  cocycle condition on choices is imposed. The conclusion supplies a representative
  s, restriction equality for every member, and uniqueness versus any t up to a
  vertical isomorphism. Thus it is unique gluing of classes, exactly sheafness.
  The covering-sieve criterion is equivalent to the jointly surjective étale-family
  criterion for this topology. Classical selection of representatives converts between
  families of quotient classes and families of representatives. A chain in the quotient
  collapses to a single vertical isomorphism by composition and inverses.
- The conclusion `IsModuliStack F` is the dependency's stack predicate: CFG plus
  effectiveness and unique gluing on every étale covering sieve. Its colimiting
  cocone formulation includes descent for arrows and objects as its docstring explains.
- No representability, algebraic-space diagonal, atlas, or restriction on automorphisms
  occurs among the binders. No extra genus, characteristic, or finite-type hypothesis occurs.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  their full definitions were read in Scheme.lean. They are re-exported by the public import.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `CategoryTheory.moduliFiberMap`,
  `CategoryTheory.IsModuliStack`. Their complete signatures, bodies, and docstrings
  were read. Their underlying `BasedCategory`, `BasedFunctor`, `Functor.Fiber`, and
  `Functor.IsHomLift` definitions were also read in Mathlib. The only proof dependency
  is this same node and module, already imported publicly for the statement.
- `def-weil-size-convention` has `lean.convention: true` and no declaration or module;
  its full record was read, and sizes are bound explicitly instead.

Edge cases checked mathematically:

- Empty S, empty V and the empty covering sieve: there is no nonemptiness assumption.
  For the empty cover, the relative sheaf condition requires a global relative class
  and uniqueness, precisely the sheaf condition's terminal value at the empty scheme.
- Empty fibres: the representative type can be empty. Matching data are not fabricated;
  the sheaf condition detects an empty global fibre when compatible local classes exist.
- q=id: relative classes over y are singletons by the cartesian universal property,
  even when y has nontrivial automorphisms. Faithfulness is automatic in this case.
- Discrete groupoids: the condition reduces to gluing relative sections of a map of
  presheaves of sets, with the target a sheaf.
- Nontrivial automorphisms: no skeletal/discrete replacement of F or G is made.
  Only relative classes forget automorphisms, as the node requires. Faithfulness
  is essential for recovering coherent object descent from equality of these classes.
- Different object/morphism universes for F and G: retained independently; matching
  families range over the full scheme sieve category, with no auxiliary small index bound.

Searches (all using the prescribed msearch wrapper for Q125 and this item):

- leanfinder, `A faithful morphism of fibred groupoids over a stack whose relative
  isomorphism class presheaves are sheaves is a stack`: eight hits, including
  Pseudofunctor.IsStack, IsStackFor, IsPrestack and IsStack.of_isStackFor; no exact theorem.
- loogle, `"IsStack", "Faithful"`: zero hits.
- grep, `relativeSheaf|relative_sheaf|[Ff]aithful.*[Ss]tack|[Ss]tack.*[Ff]aithful`:
  eight hits, six on general category/stack descent and two unrelated algebra hits;
  no relative-class descent theorem. The IsStack source was opened and read.
- leansearch, `A faithful functor of categories fibred in groupoids to a stack with
  relative sheaves of isomorphism classes has stack source`: eight hits, including
  IsStack.mk and fullyFaithfulToDescentData. These assume prestack or stack descent
  rather than deducing it from faithful relative classes.
- rg with the same relative-sheaf/faithful-stack expression on lean/WeilConjectures
  and lean/Sheaf: no exact theorem. The prescribed grep for the item id on
  lean/WeilConjectures found nothing. The unrelated full-faithfulness results do
  not supply relative classes. rg for each of the four delivered declaration names
  in Mathlib, lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found
  no existing declaration. DAG search for relative-class presheaves/relative-sheaf
  found this node and its representable special-case consumer, not a separate
  definition of this item's relative pairs. The existing CFG/stack notions are reused.

Validation: scompile.py compiled this module in sandbox and library module modes
against the published server build, without errors or unexpected warnings. Only the
main theorem is postponed; its docstring gives the four complete natural-language
steps of the DAG proof. No STATEMENT-DISPUTED flag or source discrepancy.

## Second reading by Q125

Author's separate self-check; the dispatcher prohibits starting other agents, and
independent mathematical review is by the maintainer. Reopened the node and delivered
file and compared each clause as above. In particular, checked the direction of
comparison (inverse of φ), vertical invertibility under hF/hG, fibrewise rather than
total faithfulness, all slice objects h, every covering sieve, existence rather than
a coherent selection of transition arrows, and uniqueness of the global class rather
than uniqueness of its representative. Checked that no chosen pullback functor,
representability, atlas, genus or characteristic restriction is inserted. All three
helpers have real bodies and source/blueprint docstrings; the sole theorem has sorry
as its whole proof. No mismatch required a node correction or dependency repair.
