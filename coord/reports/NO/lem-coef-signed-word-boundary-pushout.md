## Worker report

The new module `Sheaf.CategoryTheory.SignedWordBoundaryPushout` states
`SSet.SignedWord.signed_word_boundary_pushout`. Its single proof is `sorry`.
The ten helper definitions contain real data and introduce precisely the objects and
canonical colimit arrows in this node; no additional theorem is postponed. The item node
is copied unchanged except for `lean`, including the original status supplied by the
shared checkout. There is no mathematical statement correction, new independent notion,
or dependency repair.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The category of finite signed words, including the empty word, is the already published
  `SSet.SignedWord`, with `length : ℕ` and `sign : Fin length → Bool`. Its `Hom` consists of
  a monotone map of positions with the sign-preservation equation; its category instance
  composes the underlying functions. `true` denotes plus and `false` minus. None of these
  notions is copied. `emptyWord = ⟨0, Fin.elim0⟩` selects its unique length-zero object.
- The full subcategory `I_{≤n}` is `(lengthLE n).FullSubcategory`, using Mathlib's
  `ObjectProperty.FullSubcategory`, and `lengthLE n w` is exactly `w.length ≤ n`.
  `truncatedDiagram E n` is its inclusion followed by `E`.
- The diagrams are `E : SignedWord ⥤ SSet.{u}`. The single universe `u` is explicit and
  unrestricted. All variables are explicitly bound, with `autoImplicit false`.
- Properness is the existing `IsProper E`: its first conjunct asserts degreewise
  injectivity for every injection of positions; the second identifies the degreewise
  image of every common-position injection with the intersection of the two given
  images. This includes the empty intersection. `hE` and `hE'` impose it on every diagram
  to which the attachment or naturality statements apply.
- `C_n(E)` is `truncatedColimit E n = colimit (truncatedDiagram E n)`, using the dependency's
  actual `CategoryTheory.Limits.colimit`. No extra existence assumption is imposed:
  simplicial sets have all these small colimits. `truncatedColimitι` is the corresponding
  `colimit.ι`.
- `alternating n e` has length `n`, starts with `e`, and switches sign at each position:
  `if i.val % 2 = 0 then e else !e`.
- `wordBoundary E n e` is the supremum, in the subcomplex lattice, of
  `Subfunctor.range (E.map f)` for every word `w`, proof of `w.length < n`, injection
  `f : w ⟶ alternating n e`, and proof `Function.Injective f.toFun`. Subfunctor suprema
  are pointwise unions. The empty word is one of these words whenever `n ≥ 1`.
- The theorem's existential witness `b` supplies simplicial maps from these actual
  subcomplexes to `C_n(E)` for the length-`n+1` attachment. The first conjunct fixes every
  value: for each subword injection, every simplicial degree `d`, and every simplex `x`,
  its image lies in the boundary and `b` sends it to `truncatedColimitι E n w ... x`.
  The existential `hx` is only the proof that this particular simplex is in that subset.
  Since the subword images cover the boundary, this prescription determines `b` uniquely;
  it is not an arbitrary attaching map or an uncharacterized choice of data.
- The second conjunct is `IsPushout` for the displayed square. Its top arrow is
  `coprod.desc (b ... true) (b ... false)`. The left arrow is exactly `coprod.map` of the
  two `wordBoundary.ι` inclusions. The right arrow is `truncatedColimitStep`, defined by
  `colimit.pre` for the inclusion of truncations. The bottom arrow is
  `alternatingColimitMap`, the `coprod.desc` of the two colimit cocone maps. `IsPushout`
  includes commutativity and the colimit universal property of the span, giving precisely
  existence and uniqueness of the maps to every simplicial set requested by the node.
- All positive lengths are covered by writing the attachment length as `n + 1` for
  `n : ℕ`; no zero-length attachment is asserted.
- The third conjunct asserts naturality for every `η : E ⟶ E'` between proper diagrams.
  For every boundary simplex `x` it explicitly asserts that the value of `η` lies in
  the target boundary and that applying the target `b` gives the same simplex as applying
  the canonical map `truncatedColimitMap η n` to the source `b`. Thus both the induced
  boundary restriction of `η` and its equation with `b` are specified. The remaining
  square arrows are the fixed colimit and coproduct constructions, which are natural by
  their definitions and Mathlib's colimit/coproduct naturality identities.
- The last conjunct asserts `IsIso (truncatedColimitι E 0 emptyWord ...)` for every proper
  `E`, expressing `C_0(E) = E(ε)` by its canonical isomorphism, as required for chosen
  categorical colimits rather than literal equality of selected objects.

Dependency declarations read and used:

- `def-nagata-category`: `CategoryTheory.Category`, from
  `Mathlib.CategoryTheory.Category.Basic`; its full structure extends `CategoryStruct`
  by the identity and associativity laws. Used by the signed-word category and functors.
- `def-weil-pbc-simplicial-set`: `SSet`, from
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, and `SSet.Subcomplex`, from
  `Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex`. Their signatures/docstrings identify
  the simplicial functor category and subfunctors. I also read the recorded degeneracy,
  nondegeneracy and finite-nondegenerate-simplex declarations; those clauses are not used
  by this theorem.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `colimit.ι`, and
  `colimit.pre`, from `Mathlib.CategoryTheory.Limits.HasLimits`, with `colimMap` for natural
  transformations. These are the actual colimit constructions, not another predicate.
- Existing helpers `SSet.SignedWord`, `.Hom`, `.instCategory`, `.IsProper` from
  `Sheaf.CategoryTheory.ProperWordColimitInvariance` were read in full and reused.
  The invariance theorem in that module is not used. Its node is a downstream proof
  consumer, so adding it as a statement dependency would create a DAG cycle and is
  deliberately avoided. This import uses only its existing independent helper definitions.
  The future reciprocal proof import into `ProperWordColimitInvariance` must be omitted
  under stages/2-statements.md §3(7), since it would close a module import cycle; moving the
  shared definitions into a separate module is a possible later maintenance refactor.

Edge cases checked before writing:

- For length one the two boundaries are exactly the image of `E(ε)` and the square
  attaches `E(+)` and `E(-)` over `E(ε)`; `C_0` is treated independently.
- The zero-valued diagram has empty boundaries and colimits; there is no nonemptiness
  assumption. For a constant-point diagram, properness holds, each positive boundary is
  the point, and the attachment square is a pushout of the canonical fold maps.
- Disjoint position subsets intersect in the empty word, so its image must be retained
  in boundary unions. The definition includes it; the union is not over nonempty words.
- Repeated-sign words such as `++` are present in the full truncation and have noninjective
  collapse maps. They are not silently removed: their retract relations are precisely
  why only the two alternating values contribute new attachments.
- The empty word has a unique function from its empty position set; the alternating
  construction also makes sense at zero, while pushouts are only asserted at successors.
- Both signs, arbitrary simplex dimensions, and arbitrary coefficient-set universe `u`
  are included. Identity transformations are included in naturality.

Searches made:

1. `msearch.py ... leanfinder "Colimit over signed words is a pushout attaching alternating
   words along proper subword boundaries"`: eight hits, on `Monoid.PushoutI.NormalWord`
   and related group-pushout words; no signed-word diagram-colimit statement.
2. `msearch.py ... loogle '"IsPushout", "colimit"'`: twelve hits, including
   `CategoryTheory.IsPushout.isColimit` and `.of_isColimit`, and generic colimit/pushout
   preservation lemmas; none states this attachment theorem.
3. `msearch.py ... grep 'signed.?word|alternating.?word|boundary.?pushout|proper.?functor'`:
   fifteen hits concerning Coxeter alternating words, with no match.
4. `rg` of the source `WeilConjectures`, project `lean/Sheaf`, and upstream-name index
   for `SignedWord` and this node id found only the existing signed-word/properness
   helpers and the downstream theorem's explanatory proof. There is no attachment theorem.
   Direct searches in Mathlib's CategoryTheory/AlgebraicTopology and both project source
   roots for all proposed qualified helper names and `signed_word_boundary_pushout` found
   no conflicting declaration.
5. Read Mathlib's full-subcategory, subfunctor range/complete-lattice, coproduct, and
   `IsPushout` declarations to reuse their exact APIs. No private category, subcomplex,
   colimit, or pushout definition is introduced.

Source checked: Dwyer--Kan, *Calculating simplicial localizations*, Section 4.1,
Proposition 4.3 and Definition 4.4, printed pp. 22–23, directly in the PDF named by the
node. The subset-pair presentation in 4.1 is precisely the existing signed-word category.
The current node already states the proper-functor version with positive attachment
length and a separate degree-zero clause. No source discrepancy or statement dispute
was found. The theorem docstring supplies the finite-colimit proof in words, including
well-definedness on intersections and naturality, because the DAG proof list is empty.

Validation: `scompile.py NO lem-coef-signed-word-boundary-pushout` compiled the sandbox
and library forms successfully with no errors or warnings. The initial API qualification
error was repaired by using `Functor.whiskerLeft`. The required `deliver2.py NO lem-coef-signed-word-boundary-pushout --no-push`
printed `OK (dry run)` for commit `3224b22cba`: the commit compiles and passes preflight
except for the second reading, which is reserved for the independent reader. Nothing
was pushed. No proof or second-reading section has been written by this worker.

## Second reading by NO

Independent audit on 2026-10-17: I opened the sandbox node and module, the three
statement-dependency nodes and their Mathlib declarations, and the full published
`ProperWordColimitInvariance.lean` defining the reused category and properness. I read
Dwyer--Kan, Section 4.1, Proposition 4.3 and Definition 4.4 in the cited PDF, including
rendered printed pages 22 and 23 (PDF pages 6 and 7). This source is a PDF, not a
Stacks tex source. Its pairs of complementary finite position subsets are exactly
finite signed words; indexing positions from zero instead of one changes no object
or morphism. The source gives the boundary union and attachment square; this node
already specifies the proper-functor version and separates degree zero. No ambient
ring, characteristic, nonemptiness or finiteness hypothesis on simplex sets is assumed.
There is no repair note for this item, no statement_change, no new definition node,
and no dependency module in this delivery. Only the item's lean record differs from
the shared node.

Object/hypothesis/conclusion inventory and independent H3 verdicts:

1. **Index category, empty word, composition.** `SSet.SignedWord` has `length : ℕ`
   and `sign : Fin length → Bool`; its `Hom` has a monotone position function and
   the sign-preservation equation. `instCategory` composes the functions. These
   signatures, read in the published module, are exactly the node's category.
   `emptyWord` has length zero and empty sign function. Verdict: exact.
2. **Full length truncations.** `lengthLE n w := w.length ≤ n` and
   `(lengthLE n).FullSubcategory` retain every such word and all its morphisms.
   `truncatedDiagram` is the inclusion composed with `E`, not a category of
   alternating words or of injections alone. Verdict: exact.
3. **Diagrams and properness.** The binders `E : SignedWord ⥤ SSet.{u}` and
   `hE : IsProper E` introduce exactly the required diagram and hypothesis.
   In the imported definition the first conjunct is injectivity on every simplex
   degree for every injective position map. The second quantifies over all two
   injections into a common word and all injections whose position image is their
   intersection, requiring equality of the corresponding simplex ranges. Every
   position intersection has its inherited signed word, uniquely in this skeletal
   ordered category; hence this encoding neither adds nor omits a condition.
   The degree binders `n : ℕ` cover all simplex objects. Verdict: exact.
4. **Chosen colimits and canonical maps.** `truncatedColimit` uses Mathlib `colimit`,
   `truncatedColimitι` uses `colimit.ι`, `truncatedColimitStep` uses `colimit.pre`
   along the full truncation inclusion, and `truncatedColimitMap` uses `colimMap`
   on the whiskered transformation. I checked the recorded colimit declaration
   and canonical-cocone API against the dependency. Colimits exist in SSet for
   these small indexing categories; the theorem adds no HasColimit hypothesis.
   Verdict: exact.
5. **Two alternating words.** `alternating n e` has length `n` and sign `e` at
   even zero-based positions and `!e` at odd positions. Thus true/false mean the
   two required initial signs. The attachment length is `n + 1`, ranging over
   exactly the positive lengths. Verdict: exact.
6. **Boundary subcomplex.** `wordBoundary` is the iterated supremum of
   `Subfunctor.range (E.map f)` for every `w`, `w.length < n`, morphism into the
   alternating word and proof that its position function is injective. I checked
   Mathlib's range definition and pointwise `iSup_obj`; this is the union of
   precisely the node's images, with the empty subword included. Verdict: exact.
7. **Well-defined prescribed simplicial boundary maps.** The existential family
   `b E hE n e` consists of actual SSet morphisms from the boundary to the lower
   colimit. The first conjunct evaluates each on every subword representative in
   every degree and equates it to `truncatedColimitι` applied to that representative.
   `Nat.le_of_lt_succ hw` is exactly the lower truncation bound. The existential
   `hx` is only a membership proof, with no choice of a value or hidden hypothesis.
   The subword ranges cover the boundary, so these equations uniquely determine
   each map. A simultaneous family is equivalent to the node's prescriptions;
   uniqueness also removes any dependence on a properness proof. Verdict: exact.
8. **Square and pushout universal property.** In `IsPushout`, the top map is
   `coprod.desc` of the two `b` maps, the left is `coprod.map` of the actual
   subcomplex inclusions, the right is `truncatedColimitStep`, and the bottom is
   `alternatingColimitMap`, a `coprod.desc` of the two cocone maps. I checked
   Mathlib's argument order: `IsPushout` includes commutativity and a colimiting
   pushout cocone; its desc and hom_ext give the node's existence and uniqueness
   for every simplicial target. Verdict: exact.
9. **Naturality.** The third conjunct quantifies over every transformation
   `η : E ⟶ E'` between proper diagrams, without injectivity or weak-equivalence
   assumptions. It asserts preservation of each boundary simplex and precisely
   the equation between target `b` after η and source `b` followed by the induced
   colimit map. The other square arrows are fixed canonical colimit maps and
   coproduct inclusions, whose naturality follows from their defining component
   identities. Identities and composition are included. Verdict: exact.
10. **Degree zero.** The last conjunct is `IsIso` of the canonical map
    `E.obj emptyWord ⟶ truncatedColimit E 0`. This expresses the node's categorical
    identification rather than literal equality of arbitrarily chosen colimit
    objects. It is asserted for all proper diagrams as in the node's scope.
    Verdict: exact.

Edge cases: the empty word is present and is the unique length-zero word; disjoint
subwords intersect at the empty word, never an omitted nonempty-word condition.
At attachment length one both boundaries are the image of E(emptyWord), giving the
expected two attachments over C_0. Nonalternating words (including ++ and its
nonidentity endomorphisms) remain in every full truncation; the proof must check their
collapse relations. Empty-valued diagrams and constant-point diagrams satisfy the
statement with the expected empty or point boundaries. No nonempty simplex assumption
occurs. `u` is arbitrary, including zero, while the finite-word category is small in
universe zero, so no larger index universe has been silently restricted. The statement
has no unbound universe or term variables (`autoImplicit false`); arithmetic ring,
characteristic and scheme edge cases do not arise here.

Independent H4 searches, with queries different from the first worker's:

- `msearch.py ... leanfinder "Filtration colimit of two colored ordered finite sets by
  alternating maximal words with latching boundary union pushouts"`: eight hits on
  RelativeCellComplex, SimplicialThickening, horn colimits and subcomplex multicoequalizers.
  I opened RelativeCellComplex: it stores attachment data and does not prove this
  signed-word attachment theorem. No exact match.
- `msearch.py ... loogle '"IsPushout", "Subfunctor"'`: zero hits.
- `msearch.py ... leansearch "A functor on finite ordered sets with signs has a colimit
  filtration by gluing the two alternating words along all strict subwords"`: eight
  generic filtered-colimit hits for groups, monoids, functor categories and posets;
  no signed-word statement.
- Direct `rg -i 'two.colou?r|signed.?word|proper.?word|alternating.*colimit|colimit.*alternating'`
  on upstream WeilConjectures, shared lean/Sheaf and Mathlib CategoryTheory and
  AlgebraicTopology found the published SignedWord/IsProper helpers and consumers,
  but no attachment theorem or duplicate helper construction. The differently named
  alternating Cech complexes concern another notion. I also opened the actual
  Mathlib SSet, Subcomplex, Subfunctor.range, full-subcategory and IsPushout APIs.

H5/H6/H8/H9: all ten helpers construct actual data from the existing category,
subcomplex lattice, coproduct and colimit APIs. None depends on the invariance theorem
or on an undetermined sorry object. The sole postponed theorem is the item itself and
its proof remains `sorry`; no proof has been added. All declarations have source and
blueprint docstrings, and all lines fit 100 columns. The import of the downstream
invariance module reuses only its independent category/properness helpers; as recorded
by the worker, the reciprocal proof import is omitted under stage-2 rule 3(7) because
it would close a module cycle. No duplicate category or private local interface was
introduced.

Mismatch and repair: no Lean signature or mathematical statement mismatch was found.
The worker report incorrectly says that the DAG proof list is empty: the current node
has ten explicit steps. The old docstring compressed these into five and did not
spell out the checks of all collapses and nonidentity equal-length endomorphisms.
I replaced only that proof narrative with ten corresponding steps: ordered-image
factorization; canonical maximal-run collapse; boundary representative independence;
cocone construction; short-source arrows; all surjections; arbitrary arrows; pushout
existence/uniqueness; naturality; degree zero. This makes the stage-3 handoff agree with
the node. I updated the lean record's date and verified that lean.statement is still
verbatim the unchanged theorem signature. No node statement correction or citer audit
is needed; there are no new nodes or repaired dependency modules to audit.

Second-reader validation: the prescribed `scompile.py NO
lem-coef-signed-word-boundary-pushout` invocation compiled the final sandbox and library
forms successfully (1.3 seconds each), with no errors or warnings. Every delivered
Lean file (the one module) was compiled separately. The theorem signature was checked
against lean.statement byte for byte before compilation.
