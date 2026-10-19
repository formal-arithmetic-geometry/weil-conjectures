## Worker report

The module `Sheaf.Topology.SpectralLimitCohomology` states
`TopCat.Sheaf.spectralLimit_cohomology`. It also defines the auxiliary
`spectralLimitCohomologyMap` by an explicit composite of the recorded normalized site
cohomology pullback, cohomology of the adjoint sheaf morphism, and restriction along
`Opens.map_top`. This definition contains real data and no postponed proof. The main theorem
has the sole `sorry`; its docstring carries all seven steps of the DAG proof.

The source was read at `literature/stacks-project/cohomology.tex`, the setup immediately
before `lemma-colimit` and that lemma's statement and proof (Tag 0A37). The final sentence is
exactly the whole-space assertion being formalized. No statement correction was needed.

Hypothesis and clause correspondence:

- A nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Its preorder category is the category used by the colimits.
- The spectral spaces are `S : I → TopCat.{u}` with `[∀ i, SpectralSpace (S i)]`.
  The transition maps `f i j h` are continuous by their `TopCat` type; `hf` says
  `IsSpectralMap`, and `hfid` and `hfcomp` are their identity and composition laws.
- The limit is `X : TopCat.{u}` with `[SpectralSpace X]`. The continuous projections
  are `p`; `hpcomp` is their compatibility. `hlimit` asserts that each compatible tuple
  is the image of exactly one point. `htop` is the infimum of the induced topologies,
  hence precisely the coarsest topology making the projections continuous.
- The abelian sheaves are `F i : (S i).Sheaf AddCommGrpCat.{u}`. The morphisms `α`
  have exactly the type `F i ⟶ (pushforward ... (f i j h)).obj (F j)`.
  `hαid` and `hαcomp` are their sectionwise identity and cocycle equations. `HEq`
  only handles the different names for equal inverse-image opens resulting from `hfid`
  and `hfcomp`; it makes no choice of a different map.
- `P : I ⥤ X.Sheaf AddCommGrpCat.{u}`, `eP`, and `hP` present the diagram
  `i ↦ p_i⁻¹ F_i`. The `eP i` identify its objects with the recorded constructed
  inverse images, namely `sheafPullbackConstruction.sheafPullback`.
  On any stage open `U` and section `s`, `hP` says that the transition map sends the
  image of `s` under the unit for `p i` to the image of `α i j h s` under the unit
  for `p j`. This is the precise adjoint/pullback construction in the node. By the
  inverse-image adjunction, these equations determine the arrows uniquely; they are
  presentation equations, not arbitrary transition-map parameters. Their objectwise
  transports allow any presentation of the same diagram. `[HasColimit P]` supplies
  the colimit requested by the node, and `colimit P` is its `F` on `X`.
- `cf`, `hcf` and `cp`, `hcp` specify the canonical cohomological pullback families
  for `f` and `p`, using the existing `SiteCohomologyFamily.IsPullback`. This is
  naturality, compatibility with Yoneda connecting morphisms, and degree-zero
  normalization by the inverse-image adjunction unit. Its existing existence and
  uniqueness interfaces show that this is the canonical pullback, not a new choice
  of cohomology maps. The needed additivity is supplied explicitly by Mathlib's
  `Functor.additive_of_preserves_binary_products` for direct image and
  `Adjunction.left_adjoint_additive` for inverse image, without adding an instance
  assumption on the spaces or maps.
- Every degree is covered by `q : ℕ`, including zero.
- The conclusion constructs `H : I ⥤ AddCommGrpCat.{u}` and identifications `eH`
  with `Sheaf.H' (F i) q ⊤`. Its arrow equation specifies the transition maps to
  be `spectralLimitCohomologyMap ... (α i j h) q`, i.e. cohomological pullback
  followed by cohomology of the adjoint of `α`. This is the same as applying
  cohomology to `α` and then the direct-image edge map.
- The conclusion also constructs the cocone `c` and its vertex identification `ec`
  with `Sheaf.H' (colimit P) q ⊤`. Its leg equation uses the adjoint of
  `(eP i).inv ≫ colimit.ι P i`, so these are exactly the pullback-and-coprojection
  maps in the node. Existence of the induced diagram and cocone is asserted, not
  assumed. Finally `IsIso (colimit.desc H c ≫ ec.hom)` is precisely the stated
  canonical isomorphism from the colimit of stage cohomology to cohomology on `X`.

Dependency declarations used:

- `Mathlib.Topology.Spectral.Basic`: `SpectralSpace` (the recorded definition,
  Tag 08YG); `Mathlib.Topology.Spectral.Hom`: `IsSpectralMap`.
- `Mathlib.Topology.Sheaves.Functors`: `TopCat.Sheaf.pushforward`. Inverse image
  and its unit use the construction explicitly identified in the recorded
  `def-weil-pbc-topological-inverse-image` Mathlib match:
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` and
  `.sheafAdjunctionContinuous`, from `Mathlib.CategoryTheory.Sites.Pullback`.
  Their signatures and the pushforward's sectionwise definition were read.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`, `Cocone`,
  and `colimit.desc`, exactly the recorded colimit notion.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: `Sheaf.H'`,
  `Sheaf.cohomologyPresheafFunctor`, and `Sheaf.cohomologyPresheaf`. Their full
  signatures were read. Evaluation at `⊤ : Opens X` is the recorded cohomology
  of abelian sheaves on a space.
- `WeilConjectures.CategoryTheory.SiteCohomologyPullbackData`:
  `CategoryTheory.SiteCohomologyFamily` and `.IsPullback`. The source was read
  using `scompile.py --source` with exactly this recorded module name. This
  already landed node is added to `stmt_deps`; no duplicate normalization notion
  or new definition node is introduced. The published existence and uniqueness
  modules were inspected to check that normalized families give canonical maps.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`, and
  `Mathlib.Algebra.Category.Grp.AB` supply the standard Ext and Grothendieck
  sheaf-category instances. All universes are explicitly bound and
  `autoImplicit` is disabled.

Every recorded project/upstream proof-dependency module is imported without `public`:
Cech, PushforwardCohomology, FullLongExactSequence, RightDerivedUniversalDeltaFunctor,
SiteCechVanishingCriterion, SpectralDirectedLimit, and SpectralLimitDescendOpens.
The as-yet unstated `lem-weil-pbc-spectral-limit-sheaf-sections` has no module to
import; it is a proof dependency only, so it does not prevent stating this theorem.
Mathlib proof leaves are supplied by these imports and the explicit Grothendieck/AB imports.

Edge cases checked against the statement and Tag 0A37:

- Empty index sets are excluded explicitly, as required; singleton directed sets and
  identity transitions remain allowed. Antisymmetry is not imposed on the preorder.
- Empty stage spaces and an empty limit remain allowed; no point or surjectivity
  assumption is added. The compatible-tuples assertion handles their emptiness.
- Zero abelian sheaves and degree zero are allowed. There is no positive-degree
  restriction in the conclusion.
- No compactness of all opens, finite index set, injectivity/flasqueness of `F i`,
  or surjectivity of transition maps is assumed. Spectrality applies only as stated.
- Object and coefficient sizes use the standard common universe `u`, and the index
  is in that same universe; no independent index universe or finiteness condition
  on cohomology is imposed.

Searches for an existing statement:

- `msearch.py leanfinder`, query "Abelian sheaf cohomology of directed inverse limits
  of spectral spaces commutes with filtered colimits": 8 hits, principally condensed
  locally constant-presheaf colimits. None states this varying-space higher-cohomology theorem.
- `msearch.py loogle`, query `"cohomologyPresheafFunctor", "colimit"`: zero hits.
  An earlier malformed query reported an unknown identifier and was replaced by this query.
- `msearch.py grep`, query
  `(cohomology|functorH).*(colimit|[Ll]imit)|(colimit|[Ll]imit).*(cohomology|functorH)`:
  5 hits concerning local/group/nonabelian cohomology, none the requested theorem.
- `msearch.py leansearch`, the whole-space continuity statement: service unavailable
  (Internal Server Error); no mathematical verdict is inferred from this failure.
- `rg` of upstream `WeilConjectures`, project `lean/Sheaf`, Mathlib topology/sheaves,
  and `dag/lean_names_upstream.json`, searching the item ID, proposed declaration
  names, spectral limits, and cohomology/pullback names: no existing exact theorem.
  The useful hits were the recorded spectral-limit topology modules and the site
  pullback data interface, which this module reuses.

Validation uses only server `scompile.py`, nice 19, two threads and the 60-second
per-file limit. The final clean compile and dry-run result are recorded below.

Final validation: `scompile.py` compiled the delivered module cleanly in 25.1 seconds,
with nice 19, two threads, and the unchanged 60-second limit. `deliver2.py --no-push`
printed `OK (dry run)`: compilation and preflight pass except for the intentionally
pending independent second-reading section. Nothing was pushed. The second reader
must perform that reading and deliver; this worker has not written it.

## Second reading by NM

I independently opened the sandbox node and module, the five statement-dependency
nodes and their recorded signatures, the actual Mathlib definitions, and the published
`WeilConjectures.CategoryTheory.SiteCohomologyPullbackData` source fetched by
`scompile.py --source`. I read `cohomology.tex` around lines 3339–3450: the standing
setup preceding `lemma-colimit`, its whole-space conclusion (Tag 0A37), and its proof.
The node is exactly that whole-space conclusion specialized to a nonempty directed
preorder. The source imposes no omitted coefficient, finiteness, separation beyond
spectrality, or surjectivity hypothesis.

The object/hypothesis/conclusion list, matched independently with the Lean:

1. Nonempty directed index set: `{I : Type u} [Preorder I] [Nonempty I]
   [IsDirected I (· ≤ ·)]`. Verdict: exact; no antisymmetry or greatest index required.
2. Spectral spaces and continuous spectral inverse transitions: `S`, its pointwise
   `SpectralSpace` instances, `f`, and `hf`. `TopCat` supplies continuity;
   `IsSpectralMap` is continuity plus preservation of compact opens, not an open-map
   condition. `hfid` and `hfcomp` give precisely the inverse-system equations.
   Verdict: exact, using the actual Mathlib spectral-space notion of the dependency.
3. Spectral limit space and projections: `X`, `[SpectralSpace X]`, `p`, `hpcomp`.
   `hlimit` gives existence and uniqueness for every compatible tuple, hence the
   bijection in the node. `htop` gives the initial topology: the infimum is the
   coarsest topology here because Lean orders topologies oppositely to their sets
   of opens. Verdict: exact topological limit, with no projection-surjectivity premise.
4. Abelian sheaves at stages: `F i : (S i).Sheaf AddCommGrpCat.{u}`.
   `α i j h : F i ⟶ (pushforward ... (f i j h)).obj (F j)` is exactly the
   f-map in the node. I checked that Mathlib's pushforward evaluates by preimage
   of opens. `hαid` and `hαcomp` are identity and cocycle on every section.
   `HEq` only transports across the opens identified by `hfid`/`hfcomp`.
   Verdict: exact, including identities and arbitrary compatible f-maps.
5. Limit coefficient sheaf: `P`, `eP`, and `hP` present `i ↦ p_i⁻¹ F_i`.
   The imported constructed `sheafPullback` is the left-Kan-extension followed
   by sheafification from the inverse-image dependency; its adjunction is the
   actual `sheafAdjunctionContinuous`. The equation `hP` tests the conjugated
   arrow on the unit image of each section. By adjunction this specifies its
   adjoint on every section, and therefore determines the entire sheaf arrow.
   It is exactly pullback of the adjoints of `α` through `hpcomp`.
   `[HasColimit P]` supplies the chosen colimit; `colimit P` is the node's F.
   Verdict: exact presentation of the specified diagram, not an arbitrary diagram
   with merely isomorphic objects or arbitrary transition maps.
6. Cohomology and canonical pullbacks: `Sheaf.H' ... q ⊤` is exactly the
   recorded Ext model of right-derived global sections, not cohomology of a
   different site or an arbitrary derived functor. `cf`, `hcf`, `cp`, `hcp`
   present the normalized canonical pullbacks. I checked all three clauses of
   the actual `SiteCohomologyFamily.IsPullback`: coefficient naturality,
   compatibility with Yoneda boundaries for short exact sequences and their
   exact inverse images, and unit normalization in degree zero. I also opened
   the existence and uniqueness interfaces: topological inverse image is exact,
   so normalized families exist and are unique. These parameters impose no
   additional mathematical restriction. The explicit additivity witnesses are
   derived from adjunction and preservation of products, rather than hypotheses.
   Verdict: exact canonical maps using the already recorded notion.
7. All nonnegative degrees: `(q : ℕ)`. Verdict: exact, including q = 0.
8. Stage cohomology system: the existential `H` and `eH` identify the objects
   with `H^q(X_i,F_i)`; the first conjunct identifies every transition arrow
   with `spectralLimitCohomologyMap ... α ... q`. I checked the definition:
   normalized pullback, cohomology of the adjoint of α, then restriction using
   `Opens.map_top`. Verdict: the specified transition system, whose existence
   is concluded rather than assumed.
9. Canonical comparison to limit cohomology: the existential `c` and `ec`
   identify the cocone vertex with `H^q(X,colimit P)`. The leg equation uses
   exactly the adjoint of `(eP i).inv ≫ colimit.ι P i`, followed by the same
   canonical cohomology map. Thus `colimit.desc H c ≫ ec.hom` is the node's
   pullback-and-coprojection comparison. `IsIso` asserts precisely its
   invertibility as a morphism of abelian groups. Verdict: every conclusion
   clause and quantifier agrees; no arbitrary isomorphism replaces this map.

Edge cases: an empty index set is explicitly excluded by both source setup and
node. Singleton systems, identity arrows, empty spaces, empty compatible-tuple
sets and zero coefficient sheaves remain allowed. `hlimit` does not require a
point in an empty limit. Degree zero is covered. There is no characteristic or
field assumption. The one arbitrary universe `u` accommodates all index, space,
and coefficient sizes by taking their common upper universe; the index is in
the same universe as the spaces, as required by the project convention. No
unbound variables/universes, local notation, private copy, hollow definition,
non-sorry theorem proof, or unsupported extra instance assumption was found.

Independent H4 searches: `msearch.py leanfinder` with “Cohomology continuity for
inverse systems of coherent spaces and direct systems of abelian sheaves” returned
eight hits (continuous group cohomology and condensed locally constant-presheaf
colimits), none this varying-space theorem. `msearch.py loogle` with
`"SpectralSpace", "H'"` returned zero hits. Direct `rg` searches over upstream
`WeilConjectures`, project `lean/Sheaf`, and Mathlib topology and site modules used
`spectral.*cohom`, `cohom.*spectral`, both proposed declaration names, and
`cohomology.*colimit`/`colimit.*cohomology`. I opened the nearest project hit,
`TopologicalFilteredCohomology`: it concerns sheaves on one fixed space, not
varying spectral spaces. `SpectralLimitPullbackSections` concerns degree-zero
set-valued inverse-image sections. Neither duplicates this theorem or its
f-map cohomology composite. The published normalized-family definition is
reused, as are the recorded inverse image, colimit and cohomology definitions.

No new nodes or dependency modules are delivered; no statement correction is
present or needed. The additional statement dependency is the already recorded
normalized-pullback-data node, whose full source was verified above. The module
and declaration docstrings name the source and blueprint; the theorem docstring
follows all seven node proof steps, including the full-open-site injective
product construction and the canonical-map dimension-shifting conclusion.
The node's `lean.statement` was compared with the file signature verbatim.

Mismatches found: none. Changes: appended this independent second-reading report;
left the correct Lean module and node record intact. Server compile and delivery
preflight results follow below.

Second-reader validation: `deliver2.py --no-push` printed `OK (dry run)`
(commit b1f679b781), including clean server compilation and server preflight.
All validation used the required nice-19, two-thread, 60-second-per-file backend.
