## Worker report

The module `Sheaf.AlgebraicTopology.BousfieldSmithBoundedGeneration` defines
`simplicialSpaceCardinal`, the total bidegree cardinal of a simplicial space,
`IsLocalObject`, and `IsLocalEquivalence` using the recorded Reedy fibrancy and
simplicial mapping-space maps.  It states
`SSet.SegalSpace.bousfield_smith_bounded_generation` with proof `sorry`.
The item statement is unchanged.  No new definition nodes, dependency modules,
statement corrections, or disputes were needed.

Hypothesis and conclusion correspondence:

- The fixed universe is `universe u`; `P`, `Q`, and all simplicial spaces are
  `SimplicialSpace.{u} = SimplexCategoryᵒᵖ ⥤ SSet.{u}`.  The fixed map is
  `f : P ⟶ Q`, with `hf : ∀ n q, Function.Injective ((f.app n).app q)`, exactly
  the bidegreewise monomorphism condition.
- `simplicialSpaceCardinal X` is
  `Cardinal.mk (Σ p : SimplexCategoryᵒᵖ, Σ q : SimplexCategoryᵒᵖ,
  (X.obj p).obj q)`, rendering `|X| = |coprod_{p,q≥0} X_{p,q}|`.
- `IsLocalObject f Z` is the conjunction of `IsReedyFibrant Z` and
  `Enhanced.IsWeakHomotopyEquivalence (mappingSpacePre f Z)`.  The latter is
  the recorded map `Map(Q,Z) → Map(P,Z)` from the simplicial-space mapping
  construction.
- `IsLocalEquivalence f u` universally quantifies `Z`, assumes
  `IsLocalObject f Z`, and requires weak homotopy equivalence of
  `mappingSpacePre u Z`, i.e. `Map(Y,Z) → Map(X,Z)`.
- The theorem first obtains `γ : Cardinal.{u}` with
  `Cardinal.aleph0 < γ` and `γ.IsRegular`; this is the uncountable regular
  small cardinal depending only on the fixed `f`.  The standard cardinal
  regularity characterization is the stated union property for fewer than
  `γ` sets each of size less than `γ`.
- For every bidegreewise monomorphism `u : X ⟶ Y` satisfying
  `IsLocalEquivalence f u`, and every bidegreewise monomorphism
  `c : C ⟶ Y` with `simplicialSpaceCardinal C < γ`, the conclusion supplies
  `D`, `d : D ⟶ Y`, and `i : C ⟶ D`.  It states that `d` is a subspace
  inclusion, `c = i ≫ d` expresses `C ⊆ D`, and `i` is bidegreewise
  injective.  It also states `simplicialSpaceCardinal D < γ`.
- The intersection `X ∩ D` is the pullback of `u` and `d` in the functor
  category, and its inclusion into `D` is exactly `pullback.snd u d`.  The last
  clause requires `IsLocalEquivalence f (pullback.snd u d)`, rendering the
  required local-equivalence intersection in every bidegree.

Dependency declarations used:

- `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`, namespace
  `SSet.SegalSpace`: `SimplicialSpace`, `mappingSpacePre`, and
  `IsReedyFibrant` (via the imported Segal-space module), together with the
  dependency theorem `SSet.SegalSpace.reedy_cartesian_simplicial`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declaration
  `SSet.KanQuillen.right_proper_kan_quillen`, supplies the recorded Kan--Quillen
  weak homotopy equivalence and fibration meanings used by
  `Enhanced.IsWeakHomotopyEquivalence`.
- `Mathlib.SetTheory.Cardinal.Regular` supplies `Cardinal.IsRegular` and the
  cardinal arithmetic used by the size predicate.

Edge cases checked before writing: empty `C`, `X`, or `Y` are allowed; the
empty subspace has cardinal zero and the theorem does not impose nonemptiness.
The identity map and an empty or full intersection are represented by the same
pullback expression.  The bidegree quantifiers range over all outer and inner
simplex degrees, including degree zero.  No characteristic, fibrancy of `X`
or `Y`, or localized model structure is added.  The cardinal universe is the
same `u` as the simplicial-set entries, so no smallness case is excluded.

Searches actually run in this worker session on 2026-10-17:

- `msearch.py leanfinder`: "A uniform cardinal bounds subspaces of monomorphic
  local equivalences of simplicial spaces": eight hits concerning dimension,
  generators and skeletons of simplicial sets; no local-equivalence cardinal bound.
- `msearch.py loogle`: `"Bousfield", "Subcomplex"`: zero hits.
- `msearch.py grep`: `Bousfield|bounded.*subobject|IsLocalEquivalence|
  simplicialSpaceCardinal`: seventeen hits, all ordinary Bousfield localization
  references or the bounded order on subobjects. Reading Bousfield.lean shows
  that `ObjectProperty.isLocal` tests ordinary Hom bijections, not weak homotopy
  equivalences of mapping simplicial sets.
- `msearch.py leansearch`: "Bounded subobjects of local equivalences in
  simplicial spaces": eight hits, including SSet.Subcomplex and generic
  cofibrant-object localization results, no bounded local-equivalence theorem.
- `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `IsLocalObject|IsLocalEquivalence|
  simplicialSpaceCardinal|bousfield_smith|Bousfield|[Ll]ocalEquivalence`:
  unrelated ordinary localization, dense-sheaf equivalence and Bousfield--Kan
  constructions. No existing form of the three helpers or the theorem.
- The prescribed literal item-id grep over upstream `WeilConjectures` found
  nothing. Additional Mathlib cardinal-regularity searches located
  `Cardinal.card_iUnion_lt_iff_forall_of_isRegular`, whose full signature was
  read and verifies the stated union interpretation.

The three helpers belong to notions explicitly introduced in this very node,
so they are owning-node declarations, each with the item's blueprint docstring
and listed in `lean.declarations`; no independent definition node is needed.

Proof-plan imports (non-public):
`Sheaf.CategoryTheory.AccessibleFunctorPresentabilityRanks`,
`Sheaf.CategoryTheory.AccessibleSubdiagramCriterion`,
`Mathlib.CategoryTheory.Presentable.Presheaf`, and
`Mathlib.CategoryTheory.Limits.HasLimits`. The two available ordinary category
proof-dependency modules and their full theorem/docstrings were read. The
proof dependencies `lem-coef-simplicial-local-equivalences-accessible` and
`lem-coef-simplicial-space-small-subobjects` currently have neither a Lean record
nor Mathlib match, so no import yet exists for them. They are proof inputs,
not notions required to state this theorem.

Source limitation: Hirschhorn Chapter 4 is marked WANTED in the node and is
not available locally. This delivery renders the node's explicit specialization;
it does not claim to have checked a verbatim Hirschhorn theorem. The ancestor
blueprint proof was opened; it gives the coefficient-adjunction context, as the
node already explains, not the homotopy-localization specialization itself.

Validation: the original module compiled cleanly through `scompile.py` in both
sandbox and library mode; after completing the proof-plan imports and docstring,
compilation and the required dry run are repeated. Independent second reading
is left to the next worker. No `STATEMENT-DISPUTED`, node correction, or interface
repair was needed.

## Second reading by N5

I independently read the complete item node, its six proof steps, the complete Lean
module, and both statement-dependency nodes and their recorded declarations. The
item is an internal lemma, has no `statement_change`, and no maintenance repair
note exists for it. No new nodes or dependency modules occur in this delivery.

Statement inventory and correspondence (H3):

1. Fixed universe of small sets and `sS = Fun(Delta^op, sSet)`:
   `universe u` and the recorded `SimplicialSpace.{u}`. I opened
   `SegalCartesianExponent.lean:48`: this is precisely
   `SimplexCategoryᵒᵖ ⥤ SSet.{u}`, not Segal spaces or complete Segal spaces.
   Verdict: exact, including arbitrary `u`.
2. Fixed monomorphism `f : P -> Q`: `{P Q : SimplicialSpace.{u}} (f : P ⟶ Q)`
   and `hf : ∀ n q, Function.Injective ((f.app n).app q)`. The first clause of
   `reedy_cartesian_simplicial`, read in full, identifies precisely these
   bidegreewise injections with Reedy cofibrations. Verdict: exact.
3. Local objects: `IsReedyFibrant Z ∧ Enhanced.IsWeakHomotopyEquivalence
   (mappingSpacePre f Z)`, written explicitly in both tests in the final file.
   I read `IsReedyFibrant` and `IsReedyFibration` in
   `SegalCartesianExponent.lean:69-77`: the terminal map satisfies the relative
   matching condition for opposites of simplex injections. No Segal condition
   is imposed. I read `mappingSpace` and `mappingSpacePre` in
   `SimplicialSpaceReedyCartesian.lean:44-52`: the latter is the actual
   precomposition map `Map(Q,Z) -> Map(P,Z)`, obtained from the cartesian closed
   structure and outer-degree-zero evaluation. Verdict: exact.
4. Local equivalences: the hypothesis universally quantifies every
   `Z : SimplicialSpace.{u}`, assumes exactly the local-object conjunction in
   item 3, and requires weak homotopy equivalence of `mappingSpacePre u Z`,
   with direction `Map(Y,Z) -> Map(X,Z)`. I read
   `Enhanced.IsWeakHomotopyEquivalence` in `EnhancedDiagramsCones.lean:93-97`
   and its use in `KanQuillenRightProper.lean`: this is bijectivity on realized
   components and all positive based homotopy groups. Verdict: exact; no source
   or target fibrancy, and no localized model structure is assumed.
5. Total cardinal of a simplicial space:
   `simplicialSpaceCardinal X = Cardinal.mk (Σ p, Σ q, (X.obj p).obj q)`.
   `SimplexCategory` has one object for each natural-number degree, so the
   dependent sum counts exactly all outer/inner bidegree simplices.
   Verdict: exact; this counts all simplices, not just nondegenerate ones.
6. One uncountable regular small cardinal, depending only on `f`:
   `∃ γ : Cardinal.{u}, Cardinal.aleph0 < γ ∧ γ.IsRegular ∧ ...` precedes
   every quantifier over `X`, `Y`, `u`, and `C`. I opened Mathlib's
   `Cardinal.sum_lt_of_isRegular` and
   `Cardinal.card_iUnion_lt_iff_forall_of_isRegular` in `Regular.lean:204-223`:
   this regularity is the node's union-of-fewer-than-gamma-small-sets condition.
   Verdict: exact quantifier order and cardinal universe.
7. Every local-equivalence monomorphism `X -> Y`: the theorem universally binds
   `u : X ⟶ Y`, then bidegreewise injectivity and the full test of item 4.
   Verdict: neither extra hypotheses nor missing hypotheses.
8. Every small simplicial subspace `C` of `Y`:
   `c : C ⟶ Y`, bidegreewise injectivity, and
   `simplicialSpaceCardinal C < γ`. A mono representative is equivalent to
   its image subspace; the bound is invariant under that isomorphism.
   Verdict: exact, without requiring `C` to meet `X`.
9. A subspace `D` of `Y` containing `C`: existential `D`, `d : D ⟶ Y`,
   and `i : C ⟶ D`, with injectivity of `d`, `c = i ≫ d`, and injectivity
   of `i`. This represents precisely the two subspace inclusions and their
   containment triangle. Injectivity of `i` also follows from injectivity of
   `c`, so it imposes no extra mathematical requirement. Verdict: exact.
10. The bound on `D`: `simplicialSpaceCardinal D < γ`. Verdict: the same
    strict total-cardinality bound, not a separate cardinal or degreewise bound.
11. Local equivalence `X intersect D -> D`: the final universal `Z` test is
    the same test of item 4 applied to `pullback.snd u d`. Pullbacks in this
    functor category are bidegreewise pullbacks, and the second projection
    is exactly the intersection inclusion into `D`. Verdict: exact direction,
    intersection, and locality condition.

Edge cases: the empty simplicial spaces `C`, `X`, or `Y` are allowed without any
`Nonempty` assumptions; the empty total sum has cardinal zero. The zero/empty
subspace, empty intersection, full subspace, identity arrows, and `f` an
isomorphism all use the same formulas. Outer and inner degree zero are included.
There is no scheme or coefficient ring, so empty schemes and characteristic
restrictions do not arise. All simplex entries and the cardinal use universe
`u`, while the large collection of all small simplicial spaces is quantified
in its usual object universe; no independent test universe makes locality
vacuous, and no extra universe equality is imposed.

Source reading: no Stacks tag is asserted by this node. I read the ancestor
blueprint proof at
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`;
it supplies the coefficient-adjunction ancestry, not a literal proof of this
homotopy lemma. I also opened and read Rezk, Proposition 9.1, printed pp. 21-22,
including the final Bousfield-Smith paragraph, at
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf .
Its standing setting is simplicial spaces with the Reedy structure and an
inclusion `f`; its locality tests are exactly items 3-4. Its final paragraph
bounds generating local acyclic inclusions. The current node explicitly calls
its more precise bounded-intersection statement an agent-formulated input,
not a verbatim Rezk theorem. The Rochester `pshmain.pdf` endpoint failed, but I subsequently obtained the
scan at https://webhomes.maths.ed.ac.uk/~v1ranick/papers/hirschhornloc.pdf
in the sandbox scratchpad and read the images of printed pp. 76-80
(PDF pages 90-94), plus the contents page. Sections 4.4 and 4.5 have precisely
the recorded headings. Their standing hypotheses are a left proper cellular
model category and a set of maps S. Proposition 4.4.3 recognizes local
subcomplex inclusions by localized deformation retractions; Proposition 4.4.5
controls intersections. Definition 4.5.3 fixes a cardinal from the cells and S;
Proposition 4.5.5 produces a bounded subcomplex with a local intersection
inclusion, and Proposition 4.5.6 gives the bounded right-lifting test. The
node specializes this framework to Reedy simplicial spaces and S = {f};
its arbitrary prescribed C and regular strict total-size bound are explicitly
agent-formulated, rather than a verbatim restatement of Proposition 4.5.5.
Thus no extra Noetherian, finiteness, or coefficient hypothesis is hidden in
that source. The general left-proper/cellular hypotheses concern the fixed
Reedy model structure, not an extra restriction on X, Y, or C.

Independent searches (H4):

- LeanFinder query: `Uniform cardinal bound for enlarging subspaces so the
  pullback of a simplicial local equivalence remains local` returned eight
  simplicial dimension/subcomplex hits; none gives the bounded-locality lemma.
- LeanSearch query: `Homotopy local objects defined by equivalences on mapping
  simplicial sets and bounded bisimplicial subobjects` returned ordinary
  Hom-set localization, cofibrant localization, relative homotopies, and
  enriched Hom equivalences; none is the required bounded statement.
- Loogle query `Bousfield Smith bounded generation` returned no hits (unknown
  identifier `Bousfield`); this supplied no candidate match.
- The wrapper grep query `localWeakEquivalences|IsLocalFor|local.*[Oo]bject|
  bounded.*[Ss]ub` under `AlgebraicTopology` returned generic localization hits,
  not the bounded lemma. Direct `rg` over Mathlib, slopmaster2
  `WeilConjectures`, and the shared project's `lean/Sheaf` also used
  `Bousfield|Smith|bounded generation|IsLocalObject|IsLocalEquivalence|
  simplicialSpaceCardinal` and, crucially, `localWeakEquivalences|IsLocalFor`.
- The last conceptual search DID find the already defined locality notions:
  `SSet.SegalSpace.IsLocalFor` and `SSet.SegalSpace.localWeakEquivalences`
  in `SimplicialSpaceLocalizationIntervalCriterion.lean:43-55`.
  I opened their definitions and full theorem/docstring, and also read
  `localAcyclicMonomorphisms` in `SimplicialLocalBoundedLifting.lean:46-53`.
  They use the identical local-object and local-equivalence tests. There is
  no existing bounded-intersection theorem or named total-cardinality helper.

Mismatch and repair: the first worker's `IsLocalObject` and
`IsLocalEquivalence` duplicated `IsLocalFor` and `localWeakEquivalences` under
other names. I removed those two definitions and their `lean.declarations`
entries, and expanded their exact tests at the two positions in the theorem.
Importing their owning module here would create the dependency cycle
`lem-coef-simplicial-space-localization-interval-criterion ->
lem-coef-simplicial-local-bounded-lifting ->
lem-coef-bousfield-smith-bounded-generation`; I verified this path from the
current node records. Writing the tests inline, as the bounded-lifting module
also does, introduces no second definition and no backward import. The
expanded tests are definitionally the existing locality predicates. This is
only a Lean representation repair: the node's mathematical statement, its
hypotheses, proof plan, dependencies, and all conclusion clauses are unchanged.
I also updated the module documentation to reflect the remaining helper.

H5-H9 checks: `simplicialSpaceCardinal` is real dependent-sum cardinal data;
there are no hollow definitions or chosen data from mere existence. The only
postponed theorem is the item's named theorem, with proof `sorry`. Its
docstring retains all six proof steps and their dependencies; the module and
every remaining declaration have source/blueprint docstrings. There are no
private/local definitions, local notation, hidden let statements, unbound
variables, or lines over 100 characters. All universes and variables are
explicitly bound. The node's `lean.statement` was regenerated verbatim from
the final theorem signature. The four non-public proof-plan imports remain;
the two unstated proof-only nodes require no new statement dependency module.
The complete signatures of the statement dependencies were read, not inferred
from their names, and no dependency record requires repair.

Validation: after the repair, the prescribed `scompile.py N5
lem-coef-bousfield-smith-bounded-generation
lean/Sheaf/AlgebraicTopology/BousfieldSmithBoundedGeneration.lean` compiled the
only delivered Lean file cleanly in sandbox and library modes. No error or
warning was reported. The dry run and delivery results are appended below.

Delivery check: `deliver2.py N5 lem-coef-bousfield-smith-bounded-generation
--no-push` printed `OK (dry run)` at commit `8a15310c56`; preflight and both
compilation modes passed. The source-reading report was then completed and
the final delivery check repeated.
