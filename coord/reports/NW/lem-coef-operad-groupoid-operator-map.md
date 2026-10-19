## Worker report

The module `Sheaf.CategoryTheory.OperadGroupoidOperatorMap` states
`CategoryTheory.OperadGroupoidOperatorMap.operad_groupoid_operator_map`.
Its only postponed proof is that theorem. All helper definitions contain actual data;
no object or operation is chosen from its existence proof. The original node is unchanged
except for its `lean` record. No new nodes or dependency repairs are needed.

Source read: Gepner–Haugseng, [arXiv:1312.3178v4, §4.2](https://arxiv.org/html/1312.3178v4#S4.SS2),
Definitions 4.2.4 and 4.2.6, Remark 4.2.5, together with all nine proof steps of the node.
The two endpoints of each color and the direction of inversion agree with that source.

The hypothesis and clause correspondence is as follows:

- Small fibrant strict simplicial groupoid: `(G : SimplicialGroupoid.{u})`
  and `(hG : G.IsFibrant)`. `G` uses the existing constant small object type,
  simplicial inverses, and strict degreewise inverse laws; fibrancy means local Kan.
  No connectedness, nonemptiness, or restriction on mapping sets is imposed.
- Infinity-category and universe conventions: the same `SSet.{u}`, `SCat.{u}`,
  coherent nerve and simplex base as the dependency interfaces. The theorem's
  `N : CoherentNerveComparisonStatement.{u}` and `O : SimplicialOperatorNerve.Statement N`
  are presentation data supplied by the already stated comparison and operator-nerve
  existence theorems, not additional mathematical hypotheses on G. The conclusion holds
  for every such presentation. No unrelated ambient universe is identified with u.
- Colors `Ob(G) × Ob(G)`: `PairModel.color` is an equivalence from the actual pair type
  onto `PairModel.multicategory.Color`. This changes labels only.
- The displayed product: `PairModel.factors n c d r` is an equivalence from the operation's
  r-simplices to `Factors G c d r`. At gap i, `gapSource` is `d.1` for i=0 and the previous
  input's second endpoint otherwise; `gapTarget` is the next input's first endpoint,
  except that the final gap ends at `d.2`. Thus the n+1 factors are exactly `G(y_i,x_i)`.
  `PairModel.naturality` states coordinatewise naturality for every simplex operator,
  so these are equivalences of simplicial sets, not merely degreewise cardinalities.
- Substitution concatenates paths and composes glued endpoints: `word` writes each
  operation as an ordered alternating list of its actual typed arrows and indexed holes.
  `PairModel.substitution` expands each hole i by `word (factors ... (q i))`, then requires
  contraction to the actual substituted operation's word. `contractStep` composes only
  adjacent, composable arrows at a common endpoint, in their given order and in an
  arbitrary unchanged context. `Contracts` is Mathlib's reflexive transitive closure
  of that rule. A final operation word has precisely one arrow in every gap, so every
  maximal run of adjacent actual arrows has been composed. This is exactly the path
  substitution of proof Step 2, including arbitrary strings of nullary inner operations.
  Hole labels in the comparison are the actual flattened input colors, in their order.
- Unary unit: `unit_first` and `unit_last` specify identity arrows on the first and second
  endpoints respectively. The operations form an associative unital simplicial
  multicategory because `multicategory` has the existing `SimplicialMulticategory.Data`
  type, including all its naturality, unit, and three-level associativity axioms.
  `locallyKan` requires the existing `SimplicialMulticategory.IsLocallyKan` predicate
  on every operation space, including arity zero.
- The actual simplicial functor: `FunctorModel.functor` is a morphism in `SCat`, from
  `O.strings.obj G.carrier` to `(O.operators P.multicategory).category`.
  Thus it preserves enriched identities, composition, and every simplicial operator;
  these are not separate assumed formulas for an arbitrary simplicial map.
- Object formula: `FunctorModel.objects` uses `pairs` and `coloredPairs`, sending every
  string to all its adjacent pairs, in order and with the same length.
- Map over the opposite of φ: `FunctorModel.mappings` says `g.1 = f.1` in every degree.
  Both `stringHom` and `operatorHom` are the dependency's exact coproduct/product formulas.
  Heterogeneous equalities transport only along the established object and base-label
  equalities, following the dependency API. Every mapping simplex is covered.
- Positive block: for each output i, `0 < blockLength f.1 i` implies that raw gap zero
  is the inverse of `f.2 i.castSucc`, the last gap is `f.2 i.succ`, and every gap j with
  `0 < j.val < blockLength f.1 i` is the identity at the corresponding input-string
  vertex. `blockIndex` supplies the existing consecutive-block indexing.
- Zero block: when `blockLength f.1 i = 0`, its sole factor is
  `nullary e (f.2 i.castSucc) (f.2 i.succ)`. This is the left inverse followed by the
  right component, exactly `u_i u_(i-1)^(-1)` in the paper's composition convention.
  Monotonicity and zero length identify the two source vertices; `e` records that
  equality and `Eq.mp` performs only its necessary endpoint transport. The formula is
  required for every witness e. Such a witness always exists in this case; this does
  not assume a chosen source equality or omit any collapsed block.
- Empty output: the quantifier `i : Fin w.1` is empty when m=0. The existing
  `operatorHom` then has exactly one empty operation tuple for each specified base map;
  the base equality still holds. Therefore the formula includes the unique arrow to
  the empty list over each given base map.
- Coherent nerve and inert edges: `FunctorModel.inert` uses exactly the existing
  `IsLaxMonoidalInfinityFunctor` predicate. Its first clause is equality of simplicial
  maps over `monoidalSimplexBase`; its second preserves `IsMonoidalInertEdge`, whose
  definition requires cocartesianness over an inert interval map. No assertion that an
  arbitrary nerve preserves cocartesian edges is used.

The hypothesis and conclusion transporting binders (`g`, `t`, and their HEq premises)
are the standard dependency API's presentation of equality transport. They are inhabited
by the actual functor image and the actual substitution output after the displayed
object/base equalities; they do not make any formula vacuous. The product equivalences
and word contractions determine the specified substitution and functor maps rather than
merely constraining their existence on selected examples.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SimplicialGroupoidModels`,
  `CategoryTheory.CoherentNerve.simplicial_groupoid_models`; its public interface supplies
  the strict `SimplicialGroupoid`, `inv`, and `IsFibrant` definitions from
  `Sheaf.CategoryTheory.SimplicialGroupoid`.
- `Sheaf.CategoryTheory.SimplicialOperatorNerve`,
  `CategoryTheory.SimplicialOperatorNerve.simplicial_operator_nerve`, `Statement`,
  `String`, `Word`, `stringHom`, `operatorHom`, `blockLength`, `blockIndex`,
  `StringModel` and `OperatorModel`; the public `SimplicialMulticategory.Data`,
  `flatten` and `IsLocallyKan` interfaces are reused.
- `Sheaf.CategoryTheory.CompleteAlgebroid`,
  `SSet.Enhanced.Algebroid.completeCategory` and its public infinity-category conventions;
  no second version of its algebroid constructions is introduced.
- `Sheaf.CategoryTheory.OperadicAlgebraPresentability`,
  `SSet.Enhanced.Nonsymmetric.operadic_algebra_presentability`; its public operadic base
  conventions and `IsLaxMonoidalInfinityFunctor` / `IsMonoidalInertEdge` are reused.
- Proof imports: `Sheaf.CategoryTheory.CoherentNerveComparison`,
  `CategoryTheory.CoherentNerveComparisonStatement`, `coherent_nerve_comparison` and
  `CoherentNerve.nerveFunctor`; and
  `Sheaf.CategoryTheory.InfinityCocartesianMappingCriterion`,
  `SSet.Enhanced.infinity_cocartesian_mapping_criterion`.

Edge cases checked against the definitions: the empty groupoid (no colors or strings,
but the operator category still has its empty list); disconnected groupoids and empty
mapping spaces (no operation is fabricated); arity zero (one gap, no holes); empty
outer substitution (its one arrow remains unchanged); any or all inner arities zero
(all adjoining arrows contract, without deleting their composites); unary identity;
length-zero strings and empty targets; repeated ordinal indices; positive blocks of
length one (no internal factors); arbitrary higher mapping simplices; inert intervals
of length zero. A noncommutative one-object groupoid verifies the order of inversion
and the nullary composite. Distinct isomorphic objects verify both endpoint transports.
No statement fault or disputed clause was found.

Searches performed before writing (all through the prescribed search wrapper):

- LeanFinder: `simplicial groupoid pair color operad string category inversion identity
  operator functor` — eight hits concerning ordinary groupoid inversion, simplex reversal,
  and the free simplex category; none states the pair-color operad or its operator map.
- Loogle: `SimplicialGroupoid, SimplicialMulticategory` — zero hits, unknown identifier
  `SimplicialGroupoid` in the Mathlib search service.
- Mathlib grep: `Groupoid.*Operad|operad.*groupoid|pairColor|groupoidOperator` — zero hits.
- LeanSearch: `simplicial groupoid pair colored multicategory inversion operator functor`
  — eight hits on ordinary groupoid inverses and simplicial-object opposite equivalences;
  no match for the construction.
- Direct rg of upstream `WeilConjectures` and project `lean/Sheaf` for the item ID,
  `groupoidOperator`, `pairColor`, `GroupoidOperator` — no hits. The separately run
  `grep -rn` for the literal item ID in upstream `WeilConjectures` also found no hits.
- Full proposed declaration names and gap helpers searched in `dag/lean_names_upstream.json`,
  Mathlib's CategoryTheory, upstream `WeilConjectures`, and project `lean/Sheaf` — no match;
  the only `PairModel` substring hits concern unrelated lisse coefficient pairs.

Validation: the prescribed scompile wrapper compiled the complete file cleanly, first
as a sandbox module and then under its actual library module path. All universes and
binders are explicit, with autoImplicit disabled. There are no proof helpers with
postponed data, and the one named theorem has the complete nine-step proof in its docstring.
The delivery dry run compiled the exact module and passed server preflight (OK).

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
