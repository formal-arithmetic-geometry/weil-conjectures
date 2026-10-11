## Worker report

The module `Sheaf.Topology.ClosedPushforwardConstantStalks` states
`TopCat.closed_pushforward_constant_stalks`, with its sole theorem proof `sorry`.
The auxiliary definition module `Sheaf.Topology.ClosedPushforwardConstantPresheaf`
provides the actual section presheaf, without postponed data or auxiliary proof sorries.
No statement correction or disputed statement is needed.

Hypothesis and clause correspondence:

- The topological space T is `(X : TopCat.{w})`; the subset is `(C : Set X)`;
  closedness is `(hC : IsClosed C)`; the arbitrary coefficient set is `(R : Type w)`.
  There is no inhabitedness, separation, connectedness or finiteness hypothesis.
  All variables and universe levels are explicitly bound (`autoImplicit false`).
  A common arbitrary universe contains both sets, as in the sibling stalk modules;
  sets of different initial sizes can be placed in a common larger universe.
- The given presheaf L is `closedPushforwardConstantPresheaf X C R`. Its object at V
  is `LocallyConstant {y : X // y ∈ unop V ∧ y ∈ C} R`. The subtype topology is the
  subspace topology on V intersect C. `LocallyConstant.comap` along the inclusion
  prescribed by `i.unop.le` is restriction of functions. The functor laws are `rfl`.
  Mathlib's definition of `IsLocallyConstant` by open inverse images of all subsets
  is equivalent to constancy on a neighbourhood of each point: use the fibre of
  the value at that point, and conversely unions of the constant neighbourhoods.
- The stalk L_x is `.stalk x`, and the germ g_x is `.germ V x hxV g`.
  Reading `TopCat.Presheaf.stalkFunctor`, `stalk` and `germ` confirms that these are
  the neighbourhood colimit and its coprojections, with the neighbourhood category
  opposed to give reverse inclusion.
- Clause (0) is `(closedPushforwardConstantPresheaf X C R).IsSheaf`.
- Clause (a) has `∀ (x : X) (hxC : x ∈ C)`. Its existential `ev` is a function
  from the actual stalk to R. The displayed equality for every V, hxV and g is
  exactly `ev (g_x) = g ⟨x, hxV, hxC⟩`. `Function.Bijective ev` states bijectivity.
  The final `∀ ev', ... → ev' = ev` states uniqueness among all maps satisfying
  representative evaluation, without requiring the competing map to be bijective.
- Clause (b) has `∀ x, x ∉ C → Nonempty (L.stalk x) ∧ Subsingleton (L.stalk x)`.
  This says exactly one element; using only Subsingleton would omit existence.

Dependency declarations read and used:

- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, in
  `Mathlib.CategoryTheory.Limits.HasLimits`. The dual-generated declaration chooses
  a colimit object; `colimit.ι` is its coprojection. They are used by Mathlib's stalk
  and germ definitions imported through `Mathlib.Topology.Sheaves.Stalks`.
- `def-weil-pbc-sites-and-cohomology`: its recorded sheaf notions, rather than its
  cohomology declaration `Sheaf.H'`, are relevant here. `CategoryTheory.Sheaf` and
  `CategoryTheory.Presheaf.IsSheaf` in `Mathlib.CategoryTheory.Sites.Sheaf` supply
  sheaves on a site. `TopCat.Presheaf.IsSheaf`, in `Mathlib.Topology.Sheaves.Sheaf`,
  is exactly that predicate for `Opens.grothendieckTopology X`. No cohomology is used.
- The new definition node supplies `TopCat.closedPushforwardConstantPresheaf` from
  `Sheaf.Topology.ClosedPushforwardConstantPresheaf`. It uses Mathlib's existing
  `TopCat.Presheaf`, `LocallyConstant` and `LocallyConstant.comap`.

Source checked directly: [006W](https://stacks.math.columbia.edu/tag/006W) defines
constant sheaf sections as locally constant maps;
[007B](https://stacks.math.columbia.edu/tag/007B) identifies constant-sheaf stalks;
[00AE](https://stacks.math.columbia.edu/tag/00AE) describes closed pushforward stalks.
The local literature checkout has only citation lists, so these source pages were opened.
The docstring carries all three proof steps and names their DAG dependencies.

Edge cases checked mathematically before writing: X empty (point clauses vacuous,
sheaf condition still asserted); C empty (every section set and stalk is singleton);
C = X (ordinary locally constant germ evaluation); R empty (stalk empty on C, yet
singleton off C); singleton R; arbitrary non-Hausdorff spaces. Closedness supplies
the complement neighbourhood precisely where needed. The theorem assumes no extra
structure on R and does not exclude any of these cases.

Searches:

- `msearch.py leanfinder`: "Stalks of pushforward of constant sheaf along closed
  subset are the set on the subset and singleton outside" returned eight hits on
  skyscrapers and `TopCat.stalkToFiber`, none the full statement or section presheaf.
- `msearch.py loogle`: "TopCat.Presheaf.stalkPushforward, TopCat.locallyConstant"
  returned no hits, with unknown identifier `TopCat.locallyConstant`.
- `msearch.py leansearch`: "presheaf locally constant maps on intersection with
  closed subset" returned service unavailable (Internal Server Error).
- `msearch.py grep`: `closed.*[Pp]ush|[Ll]ocally[Cc]onstant` in Topology/Sheaves:
  zero hits. Direct rg of the source library for the item id and closed pushforward
  constant names found no matching declaration. General constant presheaf searches
  found site-level constant functors and sheafification, not this section encoding.
- Direct rg of `lean/Sheaf/Topology` found the inline descriptions in
  `InverseImageClosedPushforwardConstant` and `ClosedPushforwardConstantRestriction`,
  and the whole-space theorem `LocallyConstantGermEvaluation`, not a definition of
  this presheaf or the full theorem. Neither sibling theorem states the three clauses.
- DAG text search found these same statement nodes; no definition node carries
  the closed section presheaf. `tools/blueprint_refs.py search 'closed pushforward
  constant'` found zero blueprint nodes. The ancestor command identifies
  `thm-weil-pbc-henselian-idempotent-lifting`.
- Full-name rg in Mathlib, the upstream library, `lean/Sheaf` and
  `dag/lean_names_upstream.json` found neither new declaration name.

Local compilation of both delivery modules together: clean, no errors or warnings.
Server compilation and preflight are checked by the final deliver2 dry run.

## New nodes

`def-weil-pbc-closed-pushforward-constant-presheaf` defines the presheaf of locally
constant maps V intersect C to R with restriction of functions, using the sheaf/site
notions of `def-weil-pbc-sites-and-cohomology`. Its source is Tags 006W and 00AE.
The searches listed above, also recorded in `mathlib_searches`, found no named
reusable definition. It names the same concrete presheaf the existing sibling
statements write inline. The definition works for every subset; this extends the
construction's domain without changing the closed-subset theorem. It makes no
sheafhood claim. The item gains this one statement dependency; every other field
apart from `lean` is preserved. Its module contains no `sorry`. Its functor laws
are definitional equalities. The item retains its original statement verbatim.

## Second reading by J1

Independent reading of the node, both delivered modules, the dependency records and
actual declarations, and the Stacks source. I fetched the upstream `sheaves.tex` into
this item's scratchpad because the repository has no literature text checkout. Read
lines 553--595 (006W and its preceding paragraph), 995--1006 (007B), and 4926--4976
(00AE and its section preamble). The assumptions throughout are precisely a
 topological space, a set of coefficients, and closedness of the subset for 00AE;
there is no separation, connectedness, nonemptiness or finiteness assumption.
The online tag pages agree with the TeX:
https://stacks.math.columbia.edu/tag/006W,
https://stacks.math.columbia.edu/tag/007B,
https://stacks.math.columbia.edu/tag/00AE.

Object, hypothesis and conclusion checklist (all verdicts PASS):

1. T is an arbitrary topological space: `(X : TopCat.{w})`. Its topology is bundled,
   with no extra topological instance. C is an arbitrary subset `(C : Set X)` and
   the sole geometric hypothesis is `(hC : IsClosed C)`. R is an arbitrary set
   `(R : Type w)`, with no algebra, topology or inhabitedness requirement.
2. L(V) consists of locally constant functions on V intersect C, with the subspace
   topology: `closedPushforwardConstantPresheaf X C R` has
   `obj V := LocallyConstant {y : X // y ∈ unop V ∧ y ∈ C} R`.
   Read `IsLocallyConstant.tfae` in Mathlib/Topology/LocallyConstant/Basic.lean:
   its fifth equivalent predicate is exactly the node's neighbourhood definition.
   Its subtype topology is the induced topology from X, equally the topology on
   this intersection inside C. No topology on R is requested or hidden.
3. Restriction maps are restriction of functions. The definition uses
   `LocallyConstant.comap` along the inclusion given by `i.unop.le`. Opening that
   declaration confirms it is precomposition, not a chosen or abstract map.
   `map_id` and `map_comp` are definitional functor laws; no data is postponed.
4. L_x is the colimit over reverse-inclusion open neighbourhoods and g_x its
   coprojection: `.stalk x` and `.germ V x hxV g`. Read `stalkFunctor`, `stalk`,
   and `germ` in Mathlib/Topology/Sheaves/Stalks.lean: the diagram is
   `(OpenNhds.inclusion x).op` followed by L, and the germ is `colimit.ι` at
   `op ⟨V, hxV⟩`. Read the dual-generated `colimit` and `colimit.ι` definitions
   in HasLimits.lean, as recorded by def-weil-pbc-category-colimit.
5. Clause (0), sheafhood: `(closedPushforwardConstantPresheaf X C R).IsSheaf`.
   Read TopCat.Presheaf.IsSheaf in Mathlib/Topology/Sheaves/Sheaf.lean: it is
   CategoryTheory.Presheaf.IsSheaf for `Opens.grothendieckTopology X`, the
   recorded site's sheaf notion. This is the ordinary open-cover sheaf condition
   on sets, including the empty cover. The dependency
   def-weil-pbc-sites-and-cohomology records CategoryTheory.Sheaf among its
   declarations; its main cohomology declaration H' is irrelevant here.
6. Clause (a), every x in C: `∀ (x : X) (hxC : x ∈ C), ∃ ev : L.stalk x → R`.
   For every open V containing x and every actual section g, the equality
   `ev (L.germ V x hxV g) = g ⟨x, hxV, hxC⟩` is representative evaluation.
   `Function.Bijective ev` gives both injectivity and surjectivity.
   The last quantifier ranges over ALL `ev' : L.stalk x → R` satisfying the
   same evaluation law, and asserts `ev' = ev`; uniqueness is not restricted to
   maps already known bijective. Quantifier order matches the node.
7. Clause (b), every x outside C: `∀ (x : X), x ∉ C → Nonempty (L.stalk x) ∧
   Subsingleton (L.stalk x)`. Together these predicates say exactly one element;
   an empty stalk would fail the Nonempty conjunct. This is the singleton of
   sheaves of sets in 00AE, not a zero object in an abelian category.

Edge cases: empty X makes point assertions vacuous, but still asserts sheafhood;
empty C makes every section and every stalk singleton, even for empty R; C = X
recovers the ordinary locally constant sheaf. For empty R and x in C, every
neighbourhood domain contains x, so all section sets and the stalk are empty:
the unique empty evaluation map is bijective. For x outside C, the complement
neighbourhood has empty domain and its unique map gives an inhabited singleton
stalk. Singleton R also works. No index set, integer n, scheme or characteristic
occurs, so zero objects, n = 0 and characteristics impose no further restriction.
The universe w is arbitrary, with the space and coefficients in a common universe;
Lean's cumulative universes permit differently sized input types at a common
larger level. No test-object quantifier occurs in an independently smaller
universe. The neighbourhood index and Type-valued stalk share the correct size.
All variable and universe binders are explicit under `autoImplicit false`.

Independent H4/H12 searches, using different queries from the first reader:

- `msearch.py leanfinder "Sections on intersection with subspace as direct image
  of sheaf of locally constant functions"`: eight gluing/equalizer hits for
  general sheaves, no concrete intersection presheaf or complete theorem.
- `msearch.py leansearch "closed embedding direct image set sheaf stalk terminal
  outside image"`: unavailable, Internal Server Error; no mathematical verdict
  is inferred from the unavailable service.
- `msearch.py loogle "LocallyConstant, TopCat.Presheaf"`: zero hits.
- Direct rg with `constantSheaf`, `IsClosedEmbedding`, `stalkToFiber`,
  `locally.constant.*presheaf`, and `presheaf.*locally.constant` in Mathlib,
  the full WeilConjectures source, project's lean/Sheaf, and DAG nodes found
  the sibling inline constructions and the whole-space evaluation theorem,
  but no named definition of the intersection section presheaf or theorem
  containing these three clauses. Read ClosedPushforwardConstantRestriction,
  InverseImageClosedPushforwardConstant and LocallyConstantGermEvaluation:
  the first two bind an inline presheaf; the third only treats C = X.
  Read TopCat.stalkToFiber and its injectivity/surjectivity statements:
  they concern dependent functions on ambient opens satisfying a supplied
  LocalPredicate, not this specific direct-image presheaf. Upstream
  Topology/Sheaves/SpectralRestriction concerns abelian spectral restriction,
  not this set-valued construction. Full-name searches across Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found neither
  delivered full declaration name on the base.

New node def-weil-pbc-closed-pushforward-constant-presheaf was read independently
against 006W and the direct-image construction underlying 00AE. Its section formula
and restriction maps are exactly the source's construction; defining it on arbitrary
subsets is valid and the stalk theorem still assumes closedness. The searches above
and the DAG search show no reusable definition node already carrying it. Its
self-contained statement cites its site/sheaf dependency, which is its sole
stmt_dep; source has document and place; proof and proof_deps are empty and
mathlib_match is null. The id, chapter, unit, split status, created record,
blueprint ancestor and prefixed via list, none lean_audit and complete lean record
all meet brief-stage2 section 5. No dependency replacement module is needed.

H5/H6/H8/H9: the definition has no sorry, and the theorem's sole proof is `sorry`.
Module and declaration docstrings identify the source and their own blueprint ids.
The statement docstring follows the node's three proof steps and names the gluing,
germ-evaluation and colimit dependencies. Imports provide the notions actually
used, no private notation or local instance obscures the signature, and the
namespace and line widths follow the conventions. Both node lean.statement fields
are verbatim the corresponding signatures. No statement correction is present or
needed. No mismatch was found; both Lean modules and both node records are unchanged.
The only second-reading change is this appended review.

Local validation: `lcompile.py` on both delivery modules together compiled in
presheaf-then-stalk order, exit 0, 1.4 seconds, no errors or warnings. Final server
compilation and mechanical preflight are performed by deliver2.py below.
