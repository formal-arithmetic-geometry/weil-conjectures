## Worker report

The module `Sheaf.CategoryTheory.Sites.CoherentGeneratorSubobjectClosure` states
`CategoryTheory.coherent_generator_subobject_closure`. Its sole theorem has proof `sorry`;
there are no new definitions, dependency modules, or statement corrections. The node's
statement, dependencies, and proof plan are unchanged.

Hypotheses, one by one:

- A small site is `C : Type u`, `[Category.{v} C]`, `J : Precoverage C`, and
  `_hJ : J.IsSiteForCoverings`. The ambient category throughout is exactly
  `Sheaf J.toGrothendieck (Type (max u v w))`, with all natural transformations as morphisms.
- The containing universe is `max u v w`: the independent `w` allows sheaf values to be
  larger than either the object or morphism universe of the site. Both the generator
  index `I` and every generating-cover index `A` lie in this containing universe.
- The given small family is `G : I → Sheaf J.toGrothendieck (Type (max u v w))`.
  `hqc` requires `IsQuasiCompactObject.{max u v w} (G i)` for every member.
- `hgen` says that every sheaf `X` has a small family `G (ι a) ⟶ X` whose canonical
  coproduct map `Sigma.desc f` is epi. Repetitions and empty index sets are permitted.
- `hoverlap` quantifies over all `i j k` and all sheaf morphisms `f : G j ⟶ G i`,
  `g : G k ⟶ G i`, requiring quasi-compactness of `pullback f g`.
- After the first conclusion, the additional assumptions are implications:
  `∃ i, Nonempty ((⊤_ ...) ≅ G i)` and
  `∀ i j, ∃ k, Nonempty ((G i ⨯ G j) ≅ G k)`.
  Thus the initial conclusion does not depend on these later assumptions.

Conclusions, clause by clause:

- `∀ i, IsCoherentObject.{max u v w} (G i)` states coherence of every generator.
- The class D in the node is written inline as the object property
  `fun T ↦ IsQuasiCompactObject T ∧ ∃ (i : I) (m : T ⟶ G i), Mono m`.
  The next clause says each such `T` is coherent. There is no arbitrary-subobject
  quasi-compactness assertion: quasi-compactness of T is explicitly required.
- For every `K : Type`, `[SmallCategory K]`, `[FinCategory K]`,
  `ObjectProperty.IsClosedUnderLimitsOfShape D K` says that D contains every object
  isomorphic to a limit of a K-diagram with objects in D. Mathlib's `LimitOfShape`
  quantifies over a full functor `K ⥤ E` and a limiting cone, so all sheaf morphisms
  are included; none is required to come from a site arrow. Empty K is allowed.
- `∃ S : ObjectProperty E, ObjectProperty.Small.{max u v w} S ∧ ...` is a small
  full subcategory, namely `S.FullSubcategory`. `∀ i, S (G i)` includes the actual
  generators, not only a cofinal selection; `∀ T, S T → IsCoherentObject T` gives its
  coherence. `S.isoClosure.IsClosedUnderLimitsOfShape K` for every finite K is closure
  under chosen finite limits up to isomorphism. This avoids incorrectly demanding that
  the set of representatives S contain every isomorphic sheaf object.
- The last clause inside the existential says every X receives an epimorphic coproduct
  of objects B a satisfying S. This is the final generating assertion. The statement
  assumes the family generates from the outset, exactly as the node does, so the
  node's repeated conditional "if the family generates" has its antecedent available.
- Finally `(ObjectProperty.ofObj G).limitsClosure
  (fun K : (Σ K : Cat.{0, 0}, FinCategory K) ↦ K.1) T → IsCoherentObject T`
  states coherence of the entire finite-limit closure. Mathlib's existing inductive
  `limitsClosure` includes the generators, transport by isomorphism, and limits of
  all indexed shapes. Its shape family is exactly all finite small categories.
  Finite categories at any higher universe have equivalent representatives here;
  thus this is the ordinary finite-limit closure, with no restriction on sheaf maps.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the recorded site convention.
  Its full signature and three covering axioms were read.
- `def-weil-size-convention` is recorded as a convention with no declaration.
  The explicit universes above implement it; no phantom universe object is introduced.
- The recorded `Sheaf.CategoryTheory.Sites.CoherentToposRepair` publicly imports
  `Sheaf.CategoryTheory.Sites.CoherentTopos`. The latter supplies the actual constituent
  definitions `CategoryTheory.IsQuasiCompactObject`, `IsQuasiSeparatedObject`, and
  `IsCoherentObject` belonging to `def-trf-coherent-topos`; their entire definitions and
  docstrings were read. This statement uses those object predicates, not the packaged
  coherent-topos/geometric-morphism predicates introduced by the repair. It therefore
  directly imports the smaller defining module. No private copy or new interface is used.
- The sectionwise-limit proof dependency is the Mathlib match
  `CategoryTheory.Sheaf.createsLimitsOfShape` in `Mathlib.CategoryTheory.Sites.Limits`;
  its neighboring `isSheaf_of_isLimit` and finite-limit instance were read. The module
  is imported as a proof dependency. The site's covering-axiom module imports the
  definitions of sheaves, and sheafification supplies the existing coproduct structures.
- `lem-trf-topos-finite-cover-calculus` has no Lean record or mathlib match at the time
  of reading. It is a proof-only dependency, so there is no module to import yet;
  its clauses (1) and (3) are named in the theorem's complete eight-step proof docstring.
- Mathlib's `ObjectProperty.IsClosedUnderLimitsOfShape`, `ObjectProperty.Small`,
  `ObjectProperty.ofObj`, `ObjectProperty.isoClosure`, `ObjectProperty.limitsClosure`,
  `Cat`, and `FinCategory` are reused after reading their definitions. A new notion
  or definition node is not needed to spell out D or small full subcategories.

Sources and edge cases:

Read Stacks `sites.tex` around Definition 0D07 and Lemmas 0GMP/0GMQ, and the limit
interface for 00W2. Extracted ILO XI, printed p. 179 (PDF p. 185): its finite-limit
closed coherent generating subcategories are the context, not a verbatim statement of
this abstract criterion. Read the latest blueprint unit `sk-i-curve-zero/_section.md`
and `lem-trf-local-term-locality.proof.md`: the current contracting-correspondence route
is not changed by this inherited auxiliary node. The eight agent proof steps are
reproduced in the theorem's docstring, rather than attributed to ILO as a quotation.

Checked Sets on a point site: G = {1} generates, its overlap is 1, D contains the
empty and singleton sets, and empty equalizers remain in D. With G the finite sets,
D contains all finite sets and arbitrary equalizers give the expected finite subsets.
The empty generator family is not prohibited; its generating assumption can hold in
a degenerate topos, and only the additional terminal-membership implication then fails
for an empty I. Empty finite covers and diagrams remain permitted. Equalizers use
arbitrary parallel natural transformations. An object merely mono into a generator
is never asserted to be quasi-compact without that hypothesis. The empty site and
all universe-zero specializations are included.

Searches for an existing statement (all via the prescribed msearch wrapper):

- LeanFinder: "A quasi-compact generating family of set sheaves with quasi-compact fiber
  products consists of coherent objects and its quasi-compact subobjects are closed
  under finite limits". Eight hits on coherent-topology sheaf comparison and Precoherent;
  none states an object-level generator/subobject criterion.
- Loogle: `CategoryTheory.ObjectProperty.limitsClosure,
  CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape`. Three hits for generic
  closure stability/equality/minimality; these supply the interface but not the theorem.
- Grep, Mathlib/CategoryTheory: `IsCoherentObject|IsQuasiCompactObject|coherent.*generator`.
  Zero hits.
- LeanSearch: "In a Grothendieck topos quasi compact generators with quasi compact fiber
  products are coherent and their quasi compact subobjects form a finite limit closed
  family". Eight hits on coherent topology, Precoherent, and quasi-coherent modules;
  no exact match.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  searched `IsQuasiCompactObject`, `coherent.*generator`, `quasi.compact.*subobject`,
  and `coherent_generator_subobject_closure`. The object definitions exist in
  CoherentTopos; the parent FinitarySiteCoherentGenerators is a site-specific criterion;
  CoherentEpimorphicQuotient assumes an already coherent topos; ToposCompatibleGenerators
  supplies finite-limit generators without object coherence. None states this node.
  `grep -rn lem-trf-coherent-generator-subobject-closure lean/WeilConjectures` found no hit.

Validation: the first draft with the broad CoherentToposRepair import timed out under
60 seconds. A minimal import/instance probe using the smaller defining CoherentTopos
module compiled cleanly. The final statement compiled cleanly in both sandbox and library modes through
scompile.py. The prescribed deliver2.py --no-push completed with OK: the packet
passes server preflight and compiles. No live file or tool was
edited and no global build was run.

## Second reading by Q84

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
