## Worker report

The module `Sheaf.CategoryTheory.ExtremeBimoduleAttachment` states
`CategoryTheory.ExtremeBimoduleAttachment.extreme_bimodule_attachment`, with `sorry`.
There are no construction choices from unproved existence statements and no additional
postponed theorems. The two inline helper declarations describe exactly the displayed
mapping square and the two local conclusions belonging to this node. The corrected theorem
quantifies a natural factorization `f = j ≫ p` through `V′`; `p` is componentwise Bergner
weak and the strict cocone and mapping square are stated for `j`.

The quantification over `J` is the naturality clause: `T`, `B`, `V` are functors and
`g`, `f` are natural transformations. Their transitions preserve blocks, including
noninjective object functions inside a block. Taking `J` to be the one-object discrete
category recovers any individual input. Taking it to be the walking arrow gives any
map of inputs. Arbitrary composable families are covered by arbitrary `J`.
The factorization map `p` is the canonical cellular replacement comparison; no arbitrary
comparison map replaces a cocone leg.

Hypotheses, each matched to the Lean:

- Small simplicial categories and the specified Bergner model are the published `SCat.{u}`
  and `N : CoherentNerveComparisonStatement.{u}`, with `N.bergner`.
  The universe can be enlarged uniformly to contain every small diagram in question.
- The finite linearly ordered set is `I : Type u`, `[LinearOrder I]`, `[Finite I]`.
  Its distinct least and greatest elements are `a`, `b`, `hab : a < b`,
  `ha : ∀ i, a ≤ i`, and `hb : ∀ i, i ≤ b`.
- `S : Set I`, `haS`, and `hbS` say precisely that the subset contains both endpoints.
- The disjoint blocks are `O j i : Type u`. The dependent sums implement the disjoint
  unions, so no redundant disjointness assumption on type carriers is required.
  `eB j : B.obj j ≃ Σ i : I, O j i`, and `eT j`, `eV j` with indices in `S`,
  give exactly the stipulated object sets, up to their specified identifications.
- `T_directed`, `B_directed`, and `V_directed` require every degree of a reverse-block
  mapping simplicial set to be empty. No mapping simplicial set within a block is restricted.
- The enriched functors are `g : T ⟶ B` and `f : T ⟶ V`.
  `g_objects` is the precise inclusion of the same element of the same block, and
  `f_objects` is the identity under the common object identifications. `T_blocks`,
  `B_blocks`, `V_blocks` express the stipulated block preservation for maps of inputs.
- `f_weak` requires a weak homotopy equivalence at precisely the nonextreme pairs.
  The negated conjunction allows every other pair, including both diagonal blocks,
  intermediate blocks, and reverse-block empty mapping sets.
- `g_endpoints` requires a weak homotopy equivalence for every ordered pair within
  `O_a` and within `O_b`; it imposes nothing on the other mapping sets of `g`.

Conclusions, each matched to the Lean:

- The outer existential supplies a diagram `V' : J ⥤ SCat`, natural enriched functors
  `j : T ⟶ V'` and `p : V' ⟶ V`, and `f = j ≫ p`. The componentwise Bergner weak
  equivalence is `N.bergner.model.categoryWithWeakEquivalences.weakEquivalences (p.app k)`;
  the explicit mapping-space clause is
  `SSet.Enhanced.IsWeakHomotopyEquivalence ((p.app k).map x y)`.
- `eV'` gives the same `S`-block object sets for `V'`, makes `j` the identity on labels,
  and transports the labels along `p` to the supplied `eV`.
- The first inner universal clause quantifies every strict cocone `iB : B ⟶ Z`,
  `iV' : V' ⟶ Z` with `g ≫ iB = j ≫ iV'` and every componentwise
  `IsBergnerHomotopyPushout` assertion. `CoconeConclusion` then renders the extreme
  square through `V'` and the weak equivalence of `iB` on every other mapping pair.
- The second inner existential clause supplies a strict homotopy-pushout cocone for
  `(g,j)` and `eZ : Z.obj k ≃ Σ i : I, O k i`, with the two object equations and block
  preservation. Thus the representative has object set `⨿_I O_i`; the original `V` is
  reached through the displayed weak equivalence `p`.
- The square is a derived colimit via `IsDerivedLimit` on the opposite cocone, with the
  actual maps stored by `MappingPushoutSquare`; no local Kan or fibrancy binder is added.
- Empty endpoint or intermediate blocks, empty mapping simplicial sets, reverse-block
  pairs, arbitrary object identifications within blocks, and empty indexing categories are
  all literal edge cases of the binders and remain allowed.

Dependency declarations used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement`, `BergnerModelData`, with
  `SCat` and `hom` from its infrastructure import. Read their definitions and docstrings.
- `Sheaf.CategoryTheory.CofibrantSimplicialInversion`:
  `CategoryTheory.CofibrantSimplicialInversion.IsBergnerHomotopyPushout`.
  Read its full cofibrant replacement and cocone comparison definition.
- `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
  `CategoryTheory.SimplicialLocalizationCalculus.IsDerivedLimit` and its underlying
  `IsInjectivelyFibrant`. Read both full definitions and their dual interpretation.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.weakEquivalenceStructure`, with the published realization weak
  equivalences, and `SSet.modelCategoryQuillen.J.rlp` for Kan fibrations.

The last three owning nodes are already landed and are added to `stmt_deps` solely
for these shared interfaces, as authorized by the landed-node addition rule.
No dependency record is replaced and no private duplicate is introduced.

The module imports every recorded proof-dependency module available in the shared DAG.
`lem-cbc-left-proper-derived-cell-colimits` and
`lem-coef-scat-fixed-object-pushout-comparison` have no Lean record or Mathlib match
and are proof-only prerequisites; their statements are not needed to type this item.
They are therefore not re-stated, and no import is invented for them.
The small-object dependency's recorded Mathlib module is imported directly.
The theorem docstring contains the complete twelve-step DAG proof, retaining successor
and limit induction, endpoint coefficients, derived-colimit comparisons, and naturality.

Edge cases checked before writing:

- Empty `O_a` or `O_b`: the extreme square assertion has no pairs; all existing pairs
  of `B` are nonextreme. The cellular generator family is empty. The functor `f` is
  then locally weak everywhere and identity on objects, so `B` itself is a representative.
- Empty intermediate blocks and the minimal order with two endpoints: no extra
  nonemptiness or third block is used by the signature.
- Empty individual mapping sets and reverse pairs: degreewise `IsEmpty` has the intended
  meaning, and realization weak equivalence and projective cofibrancy apply without Kan.
- Both endpoint blocks contain arbitrarily many objects: `g_endpoints` quantifies over
  every ordered pair, not just endomorphisms or one selected object.
- A change in an intermediate mapping set of `g` need not be a weak equivalence;
  the signature never imposes one.
- The test `T(x,z)=S⁰`, `B(x,z)=V(x,z)=point` with trivial endpoint endomorphisms
  yields a circle at the extreme mapping space. The result requests a homotopy pushout,
  not the ordinary point pushout, and permits this example.
- The boundary of the zero simplex is empty and is retained in the complete proof plan.
- Maps identifying objects within a block are allowed: no transition is assumed injective.
- An empty parameter category is allowed; all component assertions then are vacuous,
  as expected for a family with no inputs.

Searches made with the prescribed wrapper (recorded in `searches.jsonl`):

- LeanFinder: `extreme mapping space square homotopy pushout directed simplicial categories
  Bergner` returned eight unrelated Cech conerve and relative-cell results, no exact statement.
- Loogle: `SimplicialCategory, EnrichedFunctor` returned no hit and reported the first
  identifier unknown in the remote index.
- LeanSearch: `homotopy pushout of simplicial categories mapping spaces extreme blocks`
  returned eight hits on attaching cells, precylinder homotopies, horns, and ordinary
  pushouts; none is this enriched extreme-block excision statement.
- Mathlib grep: `IsHomotopyPushout|HomotopyPushout|homotopyPushout` in AlgebraicTopology
  returned no hit. The actual source tree search for those names also found none.
- `rg` on the upstream `WeilConjectures` for the item id, extreme attachment names,
  and the proposed full declaration names returned no duplicate.
- `rg` on project `lean/Sheaf` found the published Bergner homotopy-pushout definition
  and the generic derived-limit predicate. These are used here. Searches for directed
  blocks/extreme attachment found no existing statement of this item.
- `rg` on `dag/lean_names_upstream.json` found no proposed-name collision.
  `tools/blueprint_refs.py search 'extreme bimodule'` returned no blueprint node match.

The current blueprint ancestor proof was opened; it states the coefficient adjunction,
not this enriched auxiliary assertion, as the node's source and split report already say.
The attempt to open the cited HTT PDF online timed out. Its appendices are background
only; the mathematical content being rendered is exactly the supplied agent-formulated
node and its twelve-step proof. The source correction follows the cellular replacement and
comparison in proof steps 3--6.

Validation: `scompile.py` is the only compilation entry point used. The first attempt
exposed an untyped lambda before `.op`; it was replaced by the published weak-equivalence
structure. The final clean compile and delivery preflight are recorded by the wrapper.

The dry run passed (commit `52cee02843`); the Kan--Quillen import was then made public
because its weak-equivalence structure occurs in the statement. The final dry run and
push repeat the full per-file compile and server preflight. Read-only dependency-closure
checks found no path back to this item from any of the three added landed dependencies.

## Statement corrected

The old statement required a strict homotopy-pushout cocone for the given `f : T ⟶ V`.
This fails in the returned H3 counterexample: with `I = {a < b}`, singleton endpoint
blocks, `T(x,z) = S⁰`, `T(x,x) = T(z,z) = pt`, `T(z,x) = ∅`, and `B = V = [1]` with
`g = f` collapsing the two points, the ordinary pushout is `[1]` while the homotopy
pushout has extreme mapping space `S¹`. The corrected statement follows the cellular
factorization in proof steps 3--6: it asserts `f = j ≫ p` with `p : V′ ⟶ V` a
componentwise Bergner weak equivalence, a strict homotopy-pushout cocone for `(g,j)`,
and the extreme square through `V′` together with `V′(x,z) → V(x,z)`.

Source: HTT Appendix A.3.2--A.3.3 as background, with the correction following this
module's proof steps 3--6. The sole citer is
`lem-coef-directed-three-face-mapping-pushout`; it still holds because its face-gluing
argument can use the factorization and strict `(g,j)` cocone, retaining the required
extreme square and other-pair equivalences.

## Second reading by Q154

Independent maintainer second reading of immutable delivery 2ad47175e8e84e32cd16d6dccf19fdac16cfbc6b. The original placeholder is replaced by the reading below. No Lean or node signature was changed.

## Hypotheses and conclusions

- SCat.{u} is the existing bundled category of small simplicially enriched categories;
  hom is its actual enriched mapping simplicial set. N supplies the recorded Bergner
  model and its weak_iff_dwyer_kan characterization. Taking this existing structure as
  a parameter adds no geometric hypothesis.
- I, LinearOrder, Finite, a, b, hab, ha and hb give exactly a finite order with distinct
  least and greatest elements. S, haS and hbS retain both endpoints.
- O, eT, eB and eV identify the object carriers with the appropriate disjoint sums.
  g_objects is the literal inclusion and f_objects the identity under these
  identifications. T_blocks, B_blocks and V_blocks allow arbitrary block-preserving
  transition functions, including functions identifying objects inside one block.
- T_directed, B_directed and V_directed require degreewise emptiness precisely for
  reverse-block mapping objects. Within-block categories are unrestricted.
- f_weak excludes only the ordered extreme pair; g_endpoints covers every ordered
  pair in each endpoint block. Neither requires equivalences on intermediate mapping
  objects of g. There are no local Kan, cofibrancy, nonemptiness, or injectivity assumptions.
- The existential supplies V', j and p as a functor and natural transformations, with
  f = j ≫ p. This is the well-typed factorization T → V' → V intended by the prose's
  composition notation. The two following clauses give Bergner and mappingwise weak
  equivalences for p. eV' and its equations preserve all labelled objects.
- Directedness of V' is implied, even though not repeated as a conjunct: its actual
  mapping map under p has target a reverse-block mapping object of V, empty in each
  degree. A function to the empty type forces its source empty. Likewise block
  preservation of V' follows from naturality of p, its object equation and V_blocks.
- The universal cocone clause retains strict equality g ≫ iB = j ≫ iV' and the
  recorded IsBergnerHomotopyPushout predicate for every component. That predicate
  genuinely asks for a cofibrant replacement span and weak comparison from its
  ordinary colimit; it is not an ordinary-pushout substitute.
- MappingPushoutSquare fixes the apex and both actual mapping maps, using HEq only
  to transport equal endpoint types. Its cocone fixes the middle map by naturality.
  Nonempty prevents vacuity; quantifying every such representation is harmless,
  since these are the same fixed square under endpoint transport.
- CoconeConclusion uses the existing IsDerivedLimit on the opposite cocone, with
  realization weak equivalences and Kan fibrations opposite. Unfolding
  IsInjectivelyFibrant gives projective cofibrancy on the original span: lifting
  against objectwise trivial fibrations. The comparison is exactly the comparison
  from the colimit of a weakly equivalent projectively cofibrant span to the apex.
  It therefore states a homotopy pushout of spaces, with the actual cocone maps.
- The other half of CoconeConclusion covers all nonextreme mapping objects of B,
  not just objects in the overlap. The outer mappingwise clause for p supplies
  V'(x,z) → V(x,z) at every extreme pair, since j is bijective on labelled objects.
- The existential representative cocone has precisely the I-block object set and
  both stipulated inclusion maps. Its transition maps preserve blocks. Arbitrary
  parameter categories J express natural factorization and representative cocones
  for families; a singleton gives the individual assertion and a walking arrow
  includes maps of inputs. The square maps are actual functor maps and thus retain
  the naturality required for the mapping comparison.

## Source and correction audit

I opened https://www.math.ias.edu/~lurie/papers/HTT.pdf and read the background
in Appendix A.3.2 and A.3.3, notably Example A.3.2.18, Theorem A.3.2.24 /
Remark A.3.2.25, Proposition A.3.2.27 / Corollary A.3.2.28, and Definition A.3.3.1 /
Proposition A.3.3.2 (printed pp. 863, 865, 869–870). These supply enriched-model
and diagram-model background; none is asserted to state extreme-pair excision.
The historical main-20261015 blueprint proof file is absent from the local literature
checkout. I read its current ancestor node prop-coef-integral-exceptional-adjoint
and its proof for context. The source explicitly identifies this assertion as an
agent-formulated auxiliary, so the substantive source is its recorded cellular
argument, not an alleged numbered HTT theorem or a pro-etale theorem.

I read all twelve proof steps in the item and their rendering in the theorem docstring.
Steps 1–5 retain actual free-arrow attaching maps, unchanged endpoint coefficients,
fixed object sets and the extreme-only cellular factorization. Steps 6–10 compare
the derived enriched pushout and the actual mapping cocone using products of the
endpoint weak equivalences, gluing along monomorphisms and filtered colimits.
Step 11 uses the monomorphism into V' to obtain a homotopy pushout of spaces;
step 12 retains maps of generators, cellular sequences and cocones. The two
proof-only nodes without Lean records are not needed to type the statement and
are not replaced by fabricated declarations here.

The §1(C) correction is substantive but justified: strict cocones for the original
noncofibrant leg need not represent its derived cocone. In the supplied two-object
example, the span of extreme mapping spaces is pt ← S⁰ → pt, with homotopy
pushout S¹. A strictly commuting original cocone forces the two generating
vertices to agree and cannot supply that comparison. Resolving the right leg
retains the homotopy while allowing a strict cocone. The replacement is exactly
the construction in steps 3–6, and does not add a hypothesis to the input.

I independently enumerated all stmt_deps/proof_deps citers: the sole citer is
lem-coef-directed-three-face-mapping-pushout. I read its full statement and proof,
especially steps 2 and 6–9. Its holds:true verdict is valid, with the comparison
made explicit: compose p with the original face inclusion to make the replacement
cocone at C[K]. The induced map of spans is objectwise weak, so this is still a
homotopy-pushout cocone. The mapping squares for V' and V differ by the weak
mapping maps of p and have identical B and apex legs. Invariance of derived
pushouts transfers the square to the original V, preserving the actual 03 map
and other-pair weak equivalences required by the citer. Only one citer exists,
so the instruction to open two is inapplicable. No citer edits are needed.

## Definitions, universes, and edge cases

The two local helpers are concrete structure/predicate definitions belonging to
this node, not missing independent DAG prerequisites. Neither contains sorry,
choice from an unproved existence assertion, an arbitrary replacement comparison,
or a private copy of the shared homotopy-pushout or weak-equivalence notions.

All binders are explicit with autoImplicit and relaxedAutoImplicit disabled.
The single u is the advertised common small universe of the simplicial-category
interface; it does not equate two independently stipulated site/coefficient
universes. I, J and the block carriers may be placed in a common larger universe.
No hidden universe parameter demanding colimits of arbitrary larger size appears.

Checked empty endpoint blocks (no extreme pairs, all remaining B pairs covered),
empty intermediate blocks, all object sets empty, the two-element order, multiple
objects in an endpoint block, empty reverse and forward mapping objects, n=0
empty boundary, arbitrary non-Kan mapping objects, empty J, and noninjective
block-preserving transition functions. The S⁰-collapse example is allowed by the
corrected signature and no longer requests the false strict original cocone.

For one-definition-per-notion I searched Mathlib, upstream WeilConjectures, the
Q154 lean/Sheaf tree and dag/lean_names_upstream.json for the item id, proposed
names and extreme attachment terminology. There was no duplicate (the immutable
module is not in that clone). Independent msearch LeanFinder query 'homotopy
pushout mapping spaces directed simplicial categories extreme pair' returned
Cech conerve, horn-pushout and small-object construction hits, not this assertion.
LeanSearch query 'Mapping spaces in homotopy pushouts of directed simplicial
categories' returned sHom, sHomComp and ordinary pushout/nerve hits, not this
assertion. Existing enrichment, weak-equivalence and derived-limit notions are
reused through their owning recorded modules.

## Mechanical checks and compiler evidence

The JSON lean.statement equals the theorem signature byte for byte, from theorem
through the text before := by. All three declarations are listed. The module and
each declaration have source-place and blueprint docstrings, and the theorem has
all twelve proof steps. No line exceeds 100 characters. The sole theorem proof
is exactly by sorry; helper definitions have real bodies and no local proofs.
Imports are in the permitted namespaces; extra imports are named proof-route
inputs. There are no new dependency modules or new definition nodes to repair.

I reproduced the compile with:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py Q154 lem-coef-extreme-bimodule-attachment snapshot/lean/Sheaf/CategoryTheory/ExtremeBimoduleAttachment.lean

Exit code 0, no diagnostics. The wrapper checked sandbox
Sheaf/Stage2/Sandbox0.lean in 2.0 seconds and library
Sheaf/CategoryTheory/ExtremeBimoduleAttachment.lean in 2.2 seconds, with the
60-second per-file limit and private overlay. The installed scompile.py now
coordinates this via the server wrapper; I used it as provided, not direct ssh,
a direct Lean invocation, or a global build. The worker report records a prior
dry-run compile but does not give its final timing; this independent clean run
provides reproducible evidence for the immutable file.

No git mutation, repository edit, live Lean write, claim, delivery, merge, or global
build was performed. Only this review and the complete report replacement were
written under the permitted review directory. head.txt remains
2ad47175e8e84e32cd16d6dccf19fdac16cfbc6b.
