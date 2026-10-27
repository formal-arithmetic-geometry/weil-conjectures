## Worker report

The module `Sheaf.CategoryTheory.InternalActionSheafEquivalence` states
`CategoryTheory.InternalActionSite.setSheafEquivalence`. The item changes only in `lean` and the addition of
`def-sfb-internal-set-actions` to `stmt_deps`. The TeX statement, original dependencies,
and eight-step accepted proof are unchanged. The already landed definition node binds the existing
declarations; no new node, dependency module, or statement correction is needed.
All theorem proofs are `sorry`; the packaging structure contains actual fields,
not chosen data or a definition selected from an existence assertion.

The statement-to-Lean correspondence is as follows.

- The universe V is the explicit universe `u`. `C : Type u` with `[SmallCategory C]`
  makes both objects and arrows V-small; the values `GrpCat.{u}` and `Type u` are
  in the same universe. `[HasFiniteLimits C]` is precisely the stated finite-limit
  hypothesis. The size-convention node is metatheoretic and supplies no declaration.
- The base site is `J : Precoverage C`, `hJ : J.IsSiteForCoverings`. Its generated
  topology is the recorded `J.toGrothendieck`. The group sheaf is the arbitrary
  functor `K : Cᵒᵖ ⥤ GrpCat.{u}` and the hypothesis
  `hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})`.
- The category E^K is the already recorded `SetActions J K hK`. Its definition is
  Mathlib `Mod` in the cartesian monoidal category of set sheaves, over the actual
  underlying group sheaf. Thus its action is a natural sheaf map K times X to X,
  with unit and associativity laws; its morphisms are equivariant sheaf maps.
  `setAction` evaluates exactly that action on sections. No private replacement
  for E^K, action law, or equivariant morphism has been introduced.
- `Object K`, `Arrow K`, `opArrow K f a`, and `topology K J` are the dependency's
  actual labeled category and generated topology. `categoryStruct` composes base
  arrows in Lean's diagrammatic order, with label `b * K.map g.op a` in the
  mathematical order (f,a) after (g,b). No ring or module parameter is imposed on
  the set-valued statement.
- `SetActionEquivalenceData` packages an equivalence with its characterizing
  section formulas. Its `sections` and `restriction` render E(X)(U)=X(U) and
  E(X)(f,a)(x)=a acting on f-star x. The `morphisms` field says forward maps have
  unchanged components. Section equivalences account only for Lean's bundled
  categories; all restriction and morphism equations commute with them.
- `inverseSections`, `inverse_restriction`, and `inverse_action` render the inverse
  formulas N(f,1) and N(1_U,a). `inverse_morphisms` renders unchanged inverse
  components. `unit_sections` and `counit_sections` pin both round trips to the
  identity on sections, rather than leaving an unrelated equivalence.
- The existential `P` has that full interface for arbitrary presheaves: they are
  encoded by sheaves for the bottom topology. This imposes no restriction, since
  Mathlib's `Presheaf.isSheaf_bot` holds for every presheaf. The auxiliary named
  theorem `groupSheafForEmptyCoverage` records the group-presheaf instance of this
  fact after `Precoverage.toGrothendieck_bot`; its proof is deliberately postponed
  and its docstring names the exact transport proof. The existential `_E` has the
  same interface for the actual sheaves and the actual topology `topology K J`.
- `labelOneSieve K S` is the dependency's S_1. The existential `matching` is a
  bijection between compatible families on every sieve S and compatible base
  families on S_1, using Mathlib `Presieve.FamilyOfElements` and `.Compatible`.
  Its first equation is evaluation at (f,1). Its second is the exact normalization
  z_(f,a)=a acting on z_(f,1), transported through `P.sections`. This also pins the
  inverse of the bijection, rather than asserting unrelated equinumerosity.
- The third matching-family clause says a section amalgamates the labeled family
  exactly when its identified base section amalgamates the normalized family.
  The fourth states the equivalence of unique existence explicitly. Neither
  statement assumes that S covers: the node asserts this for every sieve.
- The next clause gives the exact sheaf iff for the arbitrary action presheaf M:
  its extension is a sheaf for `topology K J` iff its base is a sheaf for
  `J.toGrothendieck`. The subsequent clause treats every base presheaf, including
  those without any action: generated-topology sheafness iff `IsSheafFor M R`
  for every `R ∈ J U`. This is the covering-family/matching-family criterion
  from the node, expressed in its existing presieve encoding.
- `IsGrothendieckTopos.{u} (SetActions J K hK)` is the final small-site-presentation
  assertion. The preceding `_E` already specifies the particular small site
  `Object K` with `topology K J`, not merely an unspecified presenting site.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, read in full, including bind
  composition and existence of covering pullbacks for some choice.
- `Sheaf.CategoryTheory.InternalActionSitePresentation`:
  `CategoryTheory.InternalActionSite.Presentation` and `presentation` were read
  in full. Its publicly re-exported `InternalActionSiteBasic` supplies `Object`,
  `Arrow`, `categoryStruct`, `category`, `opArrow`, `topology`, `labelOneSieve`.
  The module's R-module presentation itself is not misused as a set equivalence.
- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`:
  `CategoryTheory.IsGrothendieckTopos`, read in full, with its single presenting
  universe and `SmallCategory` witness.
- `Sheaf.CategoryTheory.TwistedSiteSieveGeometry`:
  `CategoryTheory.InternalActionSite.sieve_geometry`, read in full and imported
  as a proof dependency. Its sieve order equivalence and covering characterization
  give step 1 of the prescribed proof.
- `Mathlib.CategoryTheory.Sites.SheafOfTypes`:
  `CategoryTheory.Presieve.isSheaf_pretopology`, the recorded Mathlib match of
  `lem-weil-pbc-pretopology-sheaf-condition`, read with its pullback hypothesis;
  `Mathlib.CategoryTheory.Sites.IsSheafFor` provides the actual matching-family,
  compatibility, amalgamation, and sheaf-for-a-presieve definitions.
- `Sheaf.CategoryTheory.ActionToposGeometricRestriction`:
  `CategoryTheory.InternalActionSite.groupSheaf`, `groupMonoid`, `SetActions`,
  `setAction`; read their complete signatures and docstrings, including the
  actual operation maps and internal module laws. The landed definition node
  `def-sfb-internal-set-actions` records `groupSheaf`, `groupOne`, `groupMul`,
  `groupMonoid`, `SetActions`, and `setAction` among its declarations. The
  operation-law theorems are internal proof helpers of these explicit definitions. Its theorem `geometricRestriction` is NOT
  used to obtain this lemma's equivalence. The current live server source was
  also checked using `scompile.py --source`.

Import direction: `ActionToposGeometricRestriction` supplies existing definitions
needed by this statement and currently does not import this module. Its DAG
proof list names this item. Therefore a later automatic proof-import insertion
from that module to this one must be skipped as a module import cycle (the
exception in stages/2-statements.md §3.7). This delivery does not add a reverse
DAG dependency on that downstream theorem and does not use it as proof input.

Edge cases checked before writing:

- A trivial group recovers ordinary sheaves; the label normalization and both
  restriction formulas become ordinary restrictions. The theorem also permits
  arbitrary noncommutative section groups: the order is b g-star(a), not its
  reversal, and the recovered action is left, not right.
- Empty covering families and the empty sieve are permitted. Compatibility has
  its Mathlib vacuous meaning; the unique-existence clause then imposes exactly
  the singleton-section condition when that sieve covers.
- Empty section sets and empty-valued presheaves are not ruled out by any
  nonemptiness hypothesis. Matching families and amalgamations use those exact
  types. The base sheaf criterion quantifies over all base presheaves.
- A genuinely empty category fails the already-stated finite-limit assumption
  (it has no terminal object); no extra exclusion is introduced.
- Bottom topologies in the presheaf interface impose no site or sheaf hypothesis
  on the arbitrary action presheaf. In particular the main theorem does not
  assume the action presheaf already satisfies the actual J-sheaf condition.
- Object, arrow, group-value, and set-value universes all retain precisely V;
  there is no artificial finite-index or cardinal restriction.

Searches actually run:

1. `msearch.py leanfinder`: "Equivalence of sheaves of sets with an action of a
   sheaf of groups and sheaves on the labeled arrow action site". Eight hits,
   headed by `CategoryTheory.Equivalence.sheafCongr`; generic site equivalences
   and natural-equivalence sheaf criteria do not state the labeled-action
   constructions or matching-family normalization.
2. `msearch.py loogle`: "CategoryTheory.Mod, CategoryTheory.Sheaf". Zero hits.
3. `msearch.py grep` in CategoryTheory:
   `internal.{0,20}(action|group)|action.{0,20}(site|sheaf)`. Thirteen hits,
   including Cartesian internal modules and internal groups in Types; no exact
   labeled action-site equivalence.
4. `msearch.py leansearch`: "Internal group actions on sheaves of sets are module
   objects over the internal group object in the cartesian monoidal category of
   sheaves". Eight hits, including `Sheaf.cartesianMonoidalCategory`, internal
   group Hom structures, and ordinary `Action`; these confirm the ambient
   framework but do not supply this statement.
5. `rg` in `lean/WeilConjectures` for internal actions and action/sheaf/site
   combinations, and for this node id: no exact theorem. `rg` in `lean/Sheaf`
   found the exact existing action definition in `ActionToposGeometricRestriction`
   and the module-valued equivalence in `InternalActionSitePresentation`; both
   are reused. The former's `GeometricRestriction` contains only part of the
   requested result and not the arbitrary-presheaf and matching-family clauses,
   so it is not an existing match for this item.
6. `blueprint_refs.py search 'internal group action'` and, on repair,
   `blueprint_refs.py search 'internal set actions'`: zero blueprint nodes.
   DAG grep finds the plain definitions recorded only on the downstream theorem
   node, whose proof dependencies contain this item. The newly landed existing:true definition
   record now makes the statement dependency explicit and acyclic.

The current blueprint `latest` direct-images proof, paragraph (3), was read;
this node supplies its separately introduced categorical infrastructure and does
not alter that blueprint unit's statement. No STATEMENT-DISPUTED issue found.


## Reused landed definition

`def-sfb-internal-set-actions` has now landed from Q145's delivery of
`lem-sfb-internal-restriction-geometric-coherence`. Its statement is broader than
our former proposed node: it includes internal set actions and normalized
precomposition data. Its internal-set-action clause is exactly the notion this
item uses, with the same `SetActions` signature and the same underlying group,
unit, multiplication, monoid instance, and section-action declarations. Its extra
precomposition clauses add no hypothesis to this item. The complete current node,
its declaration record, and the existing action definitions were reread.

This delivery cites that landed id in the item's `stmt_deps`; it carries no copy
or modification of the existing definition node. Its recorded module remains
`Sheaf.CategoryTheory.ActionToposGeometricRestriction`, already publicly imported
by the unchanged Lean file. No reverse dependency on the downstream theorem
`lem-sfb-action-topos-geometric-restriction` is introduced.

## Returned delivery repair

Return on immutable head d1e299faf4f6: fixed the duplicate-new-node collision.
The sandbox's proposed `def-sfb-internal-set-actions.json` has been removed from
the packet; the item instead cites Q145's landed definition node. The retained
item was compared to current main, whose non-stage-2 fields are preserved.
Compared with current main, only the item `lean` and its added definition
`stmt_deps` entry change. Compared with the returned packet, the independently
created definition-node file is removed and this report describes reuse rather
than creation. The Lean module is byte-identical to the previously reviewed file.

The original H2/H12 issue from b04efb62b0c3 remains fixed: internal set actions
have an explicit acyclic definition-node statement dependency. The stage-3
module import cycle with the parent remains until the plain definitions get
their own module, as the maintainer noted; this metadata repair does not attempt
that refactor. All previously checked hypotheses, clauses and edge cases remain
unchanged. No independent second reading is claimed by this worker.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
