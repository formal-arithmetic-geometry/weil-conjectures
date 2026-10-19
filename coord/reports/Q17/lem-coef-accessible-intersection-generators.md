## Worker report

`lean/Sheaf/CategoryTheory/AccessibleIntersectionGenerators.lean` states
`CategoryTheory.exists_small_generators_intersection`, with its only proof `sorry`.
It states the node unchanged, following Lurie, Higher Topos Theory, Lemma A.2.6.9,
printed pp. 821–823, and the accessible-subcategory convention in Definition A.2.6.2.
The online source was opened at https://people.math.harvard.edu/~lurie/papers/HTT.pdf.
No definition, additional theorem, dependency repair, or new node is needed.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The universe U is `w`; `A : Type u` leaves the object universe unrestricted.
  `[Category.{v} A] [LocallySmall.{w} A]` gives U-small Hom sets even when their
  original representation lives in `v`. The three universe levels are explicit.
- `hAloc` asserts a `kap : Cardinal.{w}`, `Fact kap.IsRegular`, and
  `IsCardinalLocallyPresentable A kap`. Mathlib's regularity includes infinitude.
  This local-presentability class includes `HasColimitsOfSize.{w,w} A` and a small
  family of kap-presentable objects whose kap-filtered colimits give every object.
  Presentability means exactly preservation by the covariant Hom functor.
- `IsCardinalFiltered` is Mathlib's cocone condition for test categories whose
  arrow type has cardinality less than the regular cardinal. Thus it includes the
  empty test diagram and requires the indexing category to be nonempty.
- `Arrow A` has morphisms of A as objects and commuting squares as morphisms.
  Mathlib's `RetractArrow` (used by `IsStableUnderRetracts`) is a retract in this
  arrow category, with splitting equation `s ≫ r = 𝟙 _`.
- `C W C₀ : MorphismProperty A` gives the two arrow classes and the specified
  small generating subset. `IsSmall.{w} C₀` is smallness of its actual arrow set,
  not just of its isomorphism classes. `hCgen` is `C₀ ≤ C`.
- Clause (i): `hCiso`, `hCpush`, `hCtrans`, and `hCretract` give isomorphisms,
  pushouts, U-small continuous transfinite compositions, and arrow retracts in C.
  `hCmin` says that C is contained in every weakly saturated class containing C₀.
  Together these are exactly that C is the weakly saturated closure of C₀.
  Supplying C₀ as a parameter unpacks the small-set witness in the node.
- Clause (ii): the four `hCW*` hypotheses impose exactly the same four closure
  conditions on `C ⊓ W`, the intersection.
- Clause (iii), repleteness: `hWreplete : W.RespectsIso` means invariance under
  isomorphisms in `Arrow A` (equivalently pre/postcomposition by isomorphisms).
- Clause (iii), accessibility: `hWaccess` supplies a regular `lam : Cardinal.{w}`
  and a small `S : MorphismProperty A` with `S ≤ W`. Its first quantified clause
  takes ANY lam-filtered diagram `F : J ⥤ Arrow A` with all `F.obj j` in W and
  requires its ambient arrow-colimit in W. Its second clause presents every
  `f ∈ W` as such a colimit of arrows in S, up to `Nonempty (colimit F ≅ Arrow.mk f)`.
  All indexing object and morphism types are U-small. Existence of the colimits
  follows from local presentability and the pointwise arrow-colimit construction;
  the `[HasColimit F]` arguments specify a chosen ambient colimit. No presentability
  condition on the chosen S is imposed, matching HTT Definition A.2.6.2.
- Clause (iv): `hWtot` lists all three implications from pairs among `W f`, `W g`,
  and `W (f ≫ g)`. Lean composition `f ≫ g` is the node's `g ∘ f`.
- Conclusion: `∃ J : MorphismProperty A, IsSmall.{w} J ∧ J ≤ C ⊓ W ∧ ...`
  supplies the requested U-small subset. The final universal quantification over P
  says that EVERY weakly saturated class containing J contains `C ⊓ W`.
  Since `C ⊓ W` is itself weakly saturated and contains J, this is exactly equality
  of its weakly saturated closure with `C ⊓ W`. J itself is NOT required to be
  weakly saturated, replete, or to contain all identities.

Dependency declarations read and used:

- `def-weil-size-convention` has a metatheoretic convention record and no Lean
  definiendum. Explicit universes and locally small Hom sets implement it here.
- `def-weil-pbc-category-colimit` records `CategoryTheory.Limits.colimit` in
  `Mathlib.CategoryTheory.Limits.HasLimits`, together with `Cocone`, `IsColimit`,
  `colimit.desc`, and `CategoryTheory.IsFiltered`. The recorded chosen colimit is
  used directly, and its module is publicly imported.
- Other statement notions use Mathlib's existing `MorphismProperty.IsSmall`,
  `RespectsIso`, `IsStableUnderCobaseChange`, `IsStableUnderRetracts`,
  `IsStableUnderTransfiniteComposition`, `IsCardinalFiltered`, `Arrow`, and
  `IsCardinalLocallyPresentable`; no private versions are introduced.

Proof imports retain the node's available plan: nonpublic imports of
`Sheaf.CategoryTheory.AccessiblePieClosure`,
`Sheaf.CategoryTheory.AccessibleSubdiagramCriterion`, and
`Sheaf.CategoryTheory.AccessibleFunctorPresentabilityRanks`. Mathlib imports cover
object presentability, a regular bound for a small family, filtered-colimit element
calculus, smallness of presentables, directed-poset reindexing, and presentability of
small colimits. The three tree lemmas `lem-coef-weak-saturation-tree-presentation`,
`lem-coef-good-subset-enlargement`, and `lem-coef-small-cellular-tree-descent` have
neither a Lean record nor Mathlib match at this reading and hence no module to import;
they are proof-only, so do not prevent stating this item. The maintainer can add
those imports when their statements land. The theorem docstring gives all ten proof
steps and names the relevant nodes.

Edge cases checked:

- The small generating subsets C₀ and J may be empty; no closure property is imposed
  on either subset. Their closures still contain all isomorphisms, including the
  zero-length composite. In particular the Set example with C = W = all arrows
  is no longer forced to have a U-small weakly saturated class of all arrows.
- `IsStableUnderTransfiniteComposition.{w}` quantifies over U-small well-ordered
  shapes with well-order-continuous diagrams. A singleton shape includes identities;
  successor and limit stages include finite and arbitrary U-small ordinal composites.
- Nonempty filtered indexing is part of the empty-test-diagram condition. No empty
  filtered colimit or new nonemptiness assumption on W is slipped in.
- An empty ambient category cannot satisfy cocompleteness: the empty diagram needs
  an initial object. A terminal category is permitted. No zero object, initial map,
  characteristic, or size equality between object and Hom universes is assumed.
- The generators of W need not be presentable in the ambient arrow category: the
  node's explicit accessibility convention is used instead of a stronger shorthand.

Searches executed during this pass:

- `msearch.py ... leanfinder` query: "A weakly saturated intersection of an accessible
  two-out-of-three class of arrows with a small generated class has a small set of
  weak saturation generators". Eight hits, concerning filtered generators,
  orthogonality, or the small-object argument; no exact theorem.
- `msearch.py ... loogle` query: `CategoryTheory.MorphismProperty,
  CategoryTheory.IsLocallyPresentable`. Zero hits.
- `msearch.py ... grep` query: `intersection|inter.*generat|Smith`, subdirectory
  `CategoryTheory/SmallObject`. Zero hits.
- `rg` over upstream `WeilConjectures`, the upstream name index, and shared
  `lean/Sheaf` for `exists_small_generators_intersection|[Ww]eakly[Ss]aturated|Smith`;
  also `grep -rn` for the item id in upstream `WeilConjectures`. No upstream match.
  Shared Lean has the simplicial-specific `SSet.Enhanced.WeaklySaturated`, which
  does not state this theorem, and the related
  `CategoryTheory.MorphismProperty.exists_small_generators_intersection` in
  `Sheaf.CategoryTheory.SmithSmallSaturatedIntersection`.
- I opened that entire Smith theorem and its node. It adds `[HasLimits A]` and uses
  this item as its proof dependency, so it is not this statement and cannot replace
  it. In particular using it here would both add completeness and reverse the
  intended proof route. The new full name `CategoryTheory.exists_small_generators_intersection`
  is distinct and absent from the checked upstream and shared source.
- The node already carries additional LeanSearch/LeanFinder/Loogle/grep searches;
  their no-exact-match verdicts are consistent with this fresh check.

Repairs of the earlier sandbox attempt: removed the erroneous conclusion requiring
J itself to contain all isomorphisms and be closed under pushouts, transfinite
composition and retracts; replaced S by W in the ambient filtered-colimit closure
hypothesis; restored the available proof imports, explicit auto-implicit disabling,
header, and full ten-step proof docstring; corrected the report's composition order
and edge cases. The JSON copy was refreshed from the shared node, preserving every
field except `lean`, whose signature is copied verbatim from the revised module.
These are repairs of the Lean rendering, not a change of the node's statement.
There is no STATEMENT-DISPUTED flag or source/node fault.

Validation: `scompile.py Q17 lem-coef-accessible-intersection-generators
lean/Sheaf/CategoryTheory/AccessibleIntersectionGenerators.lean` compiled the revised
file and its missing side overlays without errors or warnings. The only theorem
proof remains `sorry` as required.

Resume verification, 2026-10-17 (Q17 stage-2 worker): I reopened the current node,
both statement dependencies and their records, Mathlib's defining signatures, the
three available side-project proof modules, and the earlier sandbox source. The
sandbox node differs from the shared node only in `lean`; its recorded signature
matches the file verbatim. The existing file needs no further statement repair.
I reread the sandbox HTT PDF at printed pp. 818–819 (Definition A.2.6.2) and
821–823 (Lemma A.2.6.9 and its proof). The source's two accessibility conditions
are precisely the ambient closure and small-family presentation clauses of
`hWaccess`; no ambient presentability condition on that small family is intended.

Fresh searches in this resumed pass: `msearch.py` LeanSearch and LeanFinder both
used "A weakly saturated accessible intersection of classes of arrows is
generated by a small set". Each returned eight related results; these concern
sieve saturation, accessible-category generators, smallness and the small-object
argument, not this intersection theorem. Loogle used
`CategoryTheory.MorphismProperty, CategoryTheory.IsLocallyPresentable` and returned
zero hits. Mathlib grep used `intersection|inter.*generat|Smith` in
`CategoryTheory/SmallObject` and returned zero hits. Fresh upstream/shared `rg`
and upstream item-tag `grep -rn` confirmed the distinct Smith theorem described
above and no exact upstream match. There is no item repair-note file. This is
worker verification only; the independent second reading remains outstanding.

## Earlier second reading (a previous round; superseded)

Reserved for the independent second reader required by the dispatch brief. The
previous attempt's self-reported second reading is withdrawn: it overlooked the
small-generator conclusion mismatch and the filtered-colimit closure mismatch
listed above. This worker does not claim an independent second reading or deliver
this packet. The second reader must check the corrected node/module and deliver it.

## Second reading by Q17

I read the shared node, its source at HTT Lemma A.2.6.9 (pp. 821--823), the
dependency records, and the complete Lean declaration independently. The node's
objects and hypotheses render as follows.

- The universe convention is rendered by explicit `u`, `v`, and `w`, with
  `A : Type u`, `[Category.{v} A]`, and `[LocallySmall.{w} A]`. The
  `hAloc` existential supplies a regular `kap : Cardinal.{w}` and
  `IsCardinalLocallyPresentable A kap`; this supplies the required U-small
  colimits and a U-small family of presentable generators.
- The three arrow classes are exactly `C W C₀ : MorphismProperty A`, and
  `[MorphismProperty.IsSmall.{w} C₀]` plus `hCgen` says that the chosen small
  class lies in `C`.
- The four closure clauses for `C` are rendered separately by `hCiso`,
  `hCpush`, `hCtrans`, and `hCretract`. The universal minimality clause
  `hCmin` says that every class with those four properties and containing `C₀`
  contains `C`; together these are exactly the node's weak-saturation
  hypothesis.
- The four corresponding clauses for `C ⊓ W` are `hCWiso`, `hCWpush`,
  `hCWtrans`, and `hCWretract`, matching the node's second hypothesis.
- Repleteness of `W` is `hWreplete : W.RespectsIso`.
- `hWaccess` introduces the node's regular `lam`, its `Fact lam.IsRegular`,
  and a small `S ≤ W`. Its first conjunct closes `W` under every
  `lam`-filtered colimit in `Arrow A`; its second presents every `W f` as a
  colimit of arrows in `S`, up to `Nonempty (colimit F ≅ Arrow.mk f)`. The
  index category is `Type w` with `Category.{w}`, so it is the prescribed
  U-small index and no larger independent universe is introduced.
- `hWtot` has the three implications for `W f`, `W g`, and `W (f ≫ g)`, with
  Lean's `f ≫ g` the source-first form of the node's `g ∘ f`.
- The conclusion is `∃ J`, with `IsSmall.{w} J`, `J ≤ C ⊓ W`, and a universal
  weak-saturation minimality condition over `P`. Thus it says precisely that
  the U-small `J` generates `C ∩ W`; it does not require `J` itself to be
  saturated or replete.

No hypothesis is added or omitted, and every quantifier and closure clause is
present. The source calls `A` presentable and the node expands this using the
recorded locally-presentable and colimit conventions. The arrow category is
Mathlib's `Arrow A`, and all filtered colimits are the recorded
`CategoryTheory.Limits.colimit` in that category.

I checked edge cases explicitly: `C₀`, `S`, and the resulting `J` may be empty;
the identity/isomorphism clauses still cover the empty tree and zero-length
composition. `IsCardinalFiltered` includes the empty test diagram and hence
nonempty indexing as required. A terminal category is allowed, while an empty
category cannot satisfy the local-presentability colimit hypothesis. No zero
object, characteristic, finiteness, Noetherian condition, or equality of object
and Hom universes is assumed; `n = 0` is irrelevant to this statement.

For the one-definition check I reran LeanSearch/LeanFinder, Loogle, and `rg`
searches over Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf`.
They found related accessible-category, small-object, and Smith-specific
declarations but no declaration of this theorem. The shared
`CategoryTheory.MorphismProperty.exists_small_generators_intersection` is a
different theorem in a different namespace: it assumes `[HasLimits A]`,
`[HasColimits A]`, and a packaged two-out-of-three class, so it cannot replace
this node. The dependency declarations `MorphismProperty.IsSmall`,
`IsCardinalFiltered`, `IsCardinalLocallyPresentable`, `Arrow`, and
`CategoryTheory.Limits.colimit` were opened and match the uses in the file.

The only mismatch found in the prior worker's draft had already been repaired:
the conclusion no longer imposes saturation properties on `J`, and the
filtered-colimit closure in `hWaccess` is correctly stated for `W` rather than
for the small generating class `S`. The current file's signature is verbatim
equal to the sandbox node's `lean.statement`, has no unbound variables or lines
over 100 characters, and contains only the required `sorry` proof. I made no
further source or statement changes.
