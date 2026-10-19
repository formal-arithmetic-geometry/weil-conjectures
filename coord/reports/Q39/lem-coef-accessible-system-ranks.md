## Worker report

The module `Sheaf.CategoryTheory.AccessibleSystemRanks` states
`CategoryTheory.accessible_system_ranks`, with one `sorry` and no definitions or proofs.
It renders the agent-formulated simultaneous uniformization statement of
`lem-coef-accessible-system-ranks` without changing that node's statement or dependencies.
Its declaration docstring contains all ten proof steps from the node, including the
rank-enlargement construction, the two cardinal choices, and the explicit Hom retract inverse.

### Hypotheses and clauses

- The fixed universe U is `w`. Both index types `S T : Type w`, every cardinal
  `Cardinal.{w}`, and the small indexing diagrams quantified by Mathlib's accessibility
  classes use this universe. The object types `A : S → Type u` have an independent,
  unrestricted universe. `[∀ s, Category.{w} (A s)]` gives small Hom sets without
  requiring the object types to be small.
- Regular infinite cardinals use `Fact η.IsRegular`. Mathlib's `Cardinal.IsRegular`
  includes `aleph0_le` and equality with cofinality; its regular-union theorem
  `Cardinal.card_iUnion_lt_iff_forall_of_isRegular` expresses the union characterization in the node.
  `IsCardinalFiltered` quantifies over diagrams whose arrow type has cardinality
  less than the given rank, including the empty diagram.
- `[∀ s, IsAccessibleCategory.{w} (A s)]` is precisely accessibility of each category.
  In `Presentable.LocallyPresentable`, this class asserts an existential regular
  cardinal with `IsCardinalAccessibleCategory`. That latter class extends
  `HasCardinalFilteredColimits` and `HasCardinalFilteredGenerator`: the generator is
  an essentially small family of presentable objects and each object has a small
  filtered colimit presentation in it. A small representative family gives the
  equivalent small-family formulation of the node.
- `a b : T → S` are the specified endpoints; `H : ∀ t, A (a t) ⥤ A (b t)` is the
  small family of functors. Here the Lean endpoint `b` corresponds to the node's
  endpoint function, while the cardinal bound is separately named `bound`.
- `hH : ∀ t, ∃ (η : Cardinal.{w}) (_ : Fact η.IsRegular),
  HasCardinalFilteredColimits (A (a t)) η ∧ (H t).IsCardinalAccessible η`
  says exactly that each functor preserves filtered colimits at an infinite regular
  rank where its source admits them. The explicit source-existence conjunct is
  intentional: Mathlib's bare `Functor.IsAccessible` does not require it.
  This is the node's stated convention, not an extra hypothesis.
- `(bound : Cardinal.{w})` permits every small cardinal bound, including finite bounds.
- The existential `∃ (μ κ : Cardinal.{w}) (_ : Fact μ.IsRegular)
  (_ : Fact κ.IsRegular)` supplies the two infinite regular cardinals in U.
  The node's lower rank lambda is named `μ` because `λ` is a Lean keyword.
  `μ < κ ∧ bound < κ` is exactly the two strict inequalities.
- `∀ s, HasCardinalFilteredColimits (A s) μ ∧ IsCardinalAccessibleCategory (A s) κ`
  gives all small lower-rank filtered colimits and upper-rank accessibility for each
  category. It does not assert lower-rank accessibility or arbitrary cocompleteness.
- `∀ t, (H t).IsCardinalAccessible μ ∧ (H t).IsCardinalAccessible κ` gives preservation
  of all small filtered colimits at both ranks. By `Functor.IsCardinalAccessible`,
  these statements quantify over every `J : Type w` with `[SmallCategory J]` and
  `[IsCardinalFiltered J ...]`, and assert `PreservesColimitsOfShape J (H t)`.
- The final `∀ (P : A (a t)) [IsCardinalPresentable P κ],
  IsCardinalPresentable ((H t).obj P) κ` says that every upper-rank presentable
  object is sent to an upper-rank presentable object. Mathlib defines this using
  preservation of filtered colimits by the Hom functor, exactly as in the node.

### Dependency declarations and imports

The sole statement dependency `def-weil-pbc-category-colimit` records
`Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`, together
with `Cocone`, `IsColimit`, `colimit.desc`, and `CategoryTheory.IsFiltered`.
I read their full signatures and docstrings (including the `to_dual` source of
`colimit` and `colimit.desc`). The module publicly imports this recorded module;
Mathlib's filtered-colimit classes use exactly its `HasColimit`/`HasColimitsOfShape`,
not a separate colimit construction.

Additional existing Mathlib notions used in the signature:

- `Mathlib.CategoryTheory.Presentable.LocallyPresentable`:
  `CategoryTheory.IsAccessibleCategory`, `CategoryTheory.IsCardinalAccessibleCategory`.
- `Mathlib.CategoryTheory.Presentable.Basic` (transitively public):
  `CategoryTheory.HasCardinalFilteredColimits`,
  `CategoryTheory.Functor.IsCardinalAccessible`, `CategoryTheory.IsCardinalPresentable`.
- `Mathlib.CategoryTheory.Presentable.IsCardinalFiltered` (transitively public):
  `CategoryTheory.IsCardinalFiltered`.
- `Mathlib.SetTheory.Cardinal.Regular` (transitively public): `Cardinal.IsRegular`.

The already stated proof dependencies are imported without `public` from
`Mathlib.CategoryTheory.Presentable.Directed`, `Mathlib.CategoryTheory.Presentable.Limits`,
`Mathlib.CategoryTheory.Limits.Types.Filtered`, `Mathlib.SetTheory.Cardinal.Regular`,
and `Mathlib.SetTheory.Cardinal.HasCardinalLT`. These give the recorded reindexing,
small-colimit presentability, elementwise colimit, successor regularity, and small-family
bound interfaces. `lem-coef-sharp-filtered-poset-subsets` has no Lean record or
Mathlib match in the base, and therefore has no module to import yet. It is only a
proof dependency; no notion required by this statement is missing.

### Edge cases and source check

Checked the following against the signature and the node's proof before writing:

- `S` may be empty. Then the endpoint maps force `T` empty; the conclusion still
  requires two ranks above the bound and all family conclusions are vacuous.
- `T` may be empty with arbitrary `S`; category rank uniformization remains required.
- Individual categories may be empty: the empty generating family is allowed, and
  every filtered index is nonempty, so the colimit existence clauses are correct.
- Terminal categories, singleton families, zero and finite cardinal bounds are included.
  No `Nonempty`, positivity, cocompleteness, or fixed-witness hypothesis was added.
- Hom sets and all small indexing types use `w`, while `u` stays independent.
- The final object quantifier includes every object, without selecting generators or
  restricting the conclusion to an initially chosen accessibility rank.

Read the current blueprint source
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2, and the node's full statement, source record, and ten-step proof. This is
its auxiliary ordinary-category uniformization input, not the blueprint unit's own
statement. The source record honestly marks the full AR source WANTED and identifies
this simultaneous form as agent-formulated. No statement correction or dispute arose.

### Searches

All search commands used `msearch.py Q39 lem-coef-accessible-system-ranks`:

- `leanfinder`: "A small family of accessible categories and accessible functors admits
  common regular ranks with preservation of presentable objects" — eight hits:
  accessibility witness extraction, accessible functors and monotonicity,
  `IsCardinalAccessibleCategory`, and `IsCardinalPresentable`; no simultaneous theorem.
- `loogle`: "CategoryTheory.IsAccessibleCategory, CategoryTheory.Functor.IsAccessible,
  CategoryTheory.IsCardinalPresentable" — zero hits for the combined query. The notions
  themselves were found and their installed Mathlib declarations read directly.
- `leansearch`: "A small family of accessible categories and accessible functors has
  common regular accessibility ranks preserving presentable objects" — eight hits on
  individual accessible categories/functors and adjunction presentability; no match.
- `grep`: "uniformization|accessible_system_ranks|simultaneous.*accessib", restricted
  to Mathlib `CategoryTheory` — zero hits.
- Direct `rg` in installed Mathlib `CategoryTheory/Presentable` found all the existing
  notions used above; read `Basic`, `LocallyPresentable`, `IsCardinalFiltered`, and
  `CardinalFilteredPresentation` to check their definitions and universe conventions.
- Direct `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `accessibleSystemRanks`, `accessible_system_ranks`,
  `lem-coef-accessible-system-ranks`, and `uniformization` found only the proof citation
  in `Sheaf.CategoryTheory.AccessiblePieClosure`, not a declaration of this statement.
- Direct `rg` for "uniformization|strongly accessible|strong.*accessib|common.*rank"
  in project category theory sources and upstream found other accessibility inputs,
  not this ordinary simultaneous rank theorem.

No new nodes or dependency repairs are needed: each notion already has its exact
Mathlib definition. The node copy changes only `lean`; the signature is recorded
verbatim and every universe and variable is explicitly bound.

### Validation

Compilation uses only the authorized `scompile.py` wrapper, with the standard
60-second single-file limit. The first run caught the reserved identifier `λ`;
it was renamed to `μ` in the signature and node record. Final `scompile.py` compilation passed cleanly for both its sandbox check and the
module-path check (1.4 s and 1.1 s); no errors or warnings. The required
`deliver2.py --no-push` dry run independently repeated these clean compile checks;
it also builds the reviewable commit and runs the server preflight, leaving the
second-reading section to the independent reader. No push was requested.

## Second reading by Q39

I did not write this module. I opened the sandbox node and Lean file together,
read the base node and its sole statement dependency, and independently checked
all notions below in the installed Mathlib source. The statement matches the
node; no Lean or node repair is needed. Only this second-reading report is added.
The sandbox node differs from the base only in `lean`, and its `lean.statement`
is verbatim the theorem signature before `:= by`.

The node's objects, hypotheses and conclusions, in order, are:

1. Fix a universe U and use it for all smallness. Lean: `universe w u`,
   `S T : Type w`, and every rank and bound has type `Cardinal.{w}`.
   Verdict: exact. Mathlib's filtered-colimit classes quantify over
   `J : Type w` with `SmallCategory J`; category objects have the independent
   universe `u`. A common object universe imposes no finiteness or smallness
   requirement on the categories.
2. All categories are ordinary and have U-small Hom sets. Lean:
   `A : S → Type u` and `[∀ s, Category.{w} (A s)]`.
   Verdict: exact; no enriched, stable, additive, abelian, or cocomplete
   structure is assumed. `HasCardinalFilteredGenerator` also records local
   smallness, which this Hom universe supplies, not an additional hypothesis.
3. Colimits are those of `def-weil-pbc-category-colimit`. Lean: public import
   `Mathlib.CategoryTheory.Limits.HasLimits`, used by the existing cardinal
   colimit and preservation classes. Verdict: exact. I read `Cocone` in
   `Limits/Cones.lean:133`, `IsColimit` in `Limits/IsLimit.lean:64`, and the
   dual-generated `colimit` and `colimit.desc` interfaces in `HasLimits.lean`.
   Their coprojections, factorization and uniqueness are the node's universal
   property, not an alternative colimit construction. The dependency's
   Stacks source `categories.tex`, definition-colimit, lines 1310-1322,
   agrees; Mathlib's `IsFiltered` includes nonemptiness as in Stacks 002V.
4. The ranks are infinite regular cardinals. Lean: each witness uses
   `Fact η.IsRegular`, and the conclusion uses `Fact μ.IsRegular` and
   `Fact κ.IsRegular`. Verdict: exact. In `Cardinal/Regular.lean:41`,
   `IsRegular` includes `aleph0_le` and cofinality regularity; the union
   characterization at line 214 agrees with the node's definition.
5. Eta-filtered means that every diagram with fewer than eta arrows has
   a cocone. Lean: the existing `IsCardinalFiltered` used by the classes.
   Verdict: exact. `Presentable/IsCardinalFiltered.lean:44` quantifies over
   `F : A ⥤ J` and `HasCardinalLT (Arrow A) η`, with the empty test diagram
   included. It is not merely binary filteredness at higher ranks.
6. Eta-presentable means preservation by Hom of these small filtered
   colimits. Lean: `IsCardinalPresentable P κ` and
   `IsCardinalPresentable ((H t).obj P) κ`. Verdict: exact.
   `Presentable/Basic.lean:150` uses `coyoneda.obj (op P)` and
   `Functor.IsCardinalAccessible`, precisely the Hom functor.
7. Each member of the small family is accessible, meaning some infinite
   regular rank with the required colimits and a small family of presentable
   generators. Lean: `[∀ s, IsAccessibleCategory.{w} (A s)]`.
   Verdict: exact. I read `LocallyPresentable.lean:41,83` and
   `CardinalFilteredPresentation.lean:78,153`: accessibility existentially
   supplies a regular rank, filtered colimits, and an essentially small
   presentable generating property. `exists_small_generator` at line 166
   gives actual small representatives; presentations are colimits of small
   filtered diagrams in that property. No locally presentable hypothesis
   or all-colimits hypothesis is substituted.
8. The small functor family has specified source and target members.
   Lean: `(a b : T → S) (H : ∀ t, A (a t) ⥤ A (b t))`.
   Verdict: exact. The Lean endpoint name `b` and the separate cardinal
   name `bound` avoid conflating the two uses of b in the natural statement.
9. Each functor is accessible at some infinite regular rank at which its
   source has the colimits. Lean: `hH : ∀ t, ∃ (η : Cardinal.{w})
   (_ : Fact η.IsRegular), HasCardinalFilteredColimits (A (a t)) η ∧
   (H t).IsCardinalAccessible η`. Verdict: exact. The source-existence
   conjunct is required by this node's convention. Bare Mathlib
   `Functor.IsAccessible` would omit it. Witnesses may depend on t and
   need not coincide with the category witnesses.
10. For every small cardinal bound, choose two infinite regular ranks with
    lambda strictly less than kappa and the bound strictly less than kappa.
    Lean: `(bound : Cardinal.{w})` precedes
    `∃ (μ κ : Cardinal.{w}) (_ : Fact μ.IsRegular) (_ : Fact κ.IsRegular),
    μ < κ ∧ bound < κ ∧ ...`. Verdict: exact; μ renders lambda,
    and the ranks may depend on the supplied bound and whole system.
11. Every category admits all small lower-rank filtered colimits and is
    upper-rank accessible. Lean: `∀ s,
    HasCardinalFilteredColimits (A s) μ ∧ IsCardinalAccessibleCategory (A s) κ`.
    Verdict: exact. This does not require lower-rank accessibility.
12. Every functor preserves both lower-rank and upper-rank filtered colimits,
    and sends every upper-rank presentable object to one. Lean:
    `∀ t, (H t).IsCardinalAccessible μ ∧ (H t).IsCardinalAccessible κ ∧
    ∀ (P : A (a t)) [IsCardinalPresentable P κ],
    IsCardinalPresentable ((H t).obj P) κ`.
    Verdict: exact. `Basic.lean:54` requires `PreservesColimitsOfShape` for
    every small filtered shape at the rank. Category accessibility supplies
    the colimits at both conclusion ranks. The last hypothesis is an
    implication for arbitrary P, not a restriction to generators.

Edge cases: S empty forces T empty through the endpoint maps, but the two
regular ranks and strict bound remain required. T empty with S nonempty
retains all category conclusions. Empty individual categories and empty
small generating families are admitted; filtered diagrams are nonempty,
so colimit existence in an empty category has its proper vacuous meaning.
Singleton systems, terminal categories, and categories with a zero object
are admitted without extra structures or nonzero-object restrictions.
`bound = 0` and finite bounds are included, while the chosen ranks remain
infinite. Scheme emptiness, characteristic and an integer degree n are
inapplicable: this is an ordinary-category statement with no schemes,
rings or degree parameters. All variables and universes are explicitly
bound; the smallness universe is consistently w, independently of u.

Source reading: this item has no Stacks tag of its own. I read the named
blueprint proof paragraph and both cited papers at
https://www.math.muni.cz/~rosicky/papers/elem7.pdf (§3, printed p. 5) and
https://eprints.whiterose.ac.uk/id/eprint/103969/1/accim6.pdf (§2, printed p. 3).
The relevant portions concern ordinary accessible categories and functors;
they do not impose directed cocompleteness or any large-cardinal assumption
on uniformization. Later results in the papers have extra hypotheses, but
those are not the cited inputs. The papers describe single-functor
uniformization and sharp-rank enlargement. The simultaneous assertion is
explicitly agent-formulated in the node, whose ten-step proof makes both
common-rank choices and the bound on all generator images explicit. I
checked that proof rather than treating the blueprint paragraph as a
verbatim source for this auxiliary theorem. The full AR source remains
WANTED, as already recorded; no source-based correction is called for.

Independent searches on 2026-10-17, using the prescribed msearch wrapper:

- LeanFinder: "A set of accessible functors between accessible categories
  is strongly accessible at a common arbitrarily large regular cardinal";
  eight hits on individual accessibility witnesses and monotonicity,
  none giving this system theorem.
- Loogle: `"uniformization"`; four hits in the online Mathlib
  `Presentable.Uniformization`, including `uniformization_of_small`
  for a family of functors with fixed domain and codomain. I checked the
  installed Presentable files and used `scompile.py --source
  Mathlib.CategoryTheory.Presentable.Uniformization`: that module's source
  is unavailable in the compiler's source environment. These online
  declarations are not installed matches and do not justify an existing
  binding for this theorem.
- LeanSearch: "Simultaneous strong accessibility for a small diagram of
  accessible categories with an arbitrary cardinal lower bound";
  eight hits on accessibility constructors, witnesses and individual
  presentability, no exact statement.
- Wrapper grep: `uniformization|common.*accessib|simultaneous.*rank`;
  zero hits. Independently ran rg for `uniformization`,
  `strongly.*accessible`, `strong.*accessib`, `common.*(rank|regular)`
  and `accessib.*system` in installed Mathlib Presentable, upstream
  WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json.
  Project results are citations or other accessible-category lemmas,
  especially AccessiblePieClosure's proof citation of this item, not
  another declaration of this theorem. Existing Mathlib notions are
  all reused; no new definition is introduced.

No new nodes, dependency modules, statement_change, or repair note are
present. The sole dependency interface is usable. I verified the private
proof imports against the recorded Mathlib proof dependencies; the only
unstated proof dependency, `lem-coef-sharp-filtered-poset-subsets`, needs
no missing notion in this signature. All ten DAG proof steps are present
in the declaration docstring, including cocone gluing, generator-image
ranks and the explicit retract inverse. There is exactly one theorem
with proof `sorry`, no definitions, no file-local notation or instances,
and no line over 100 characters. No mismatch was found and nothing
mathematical was changed.

Validation: the second reader reran the authorized scompile.py wrapper
with the absolute sandbox file path. The sandbox compile passed in 0.9 s
and the module-path compile passed in 1.0 s, with no errors or warnings.
The second reader's deliver2.py --no-push run printed OK: its reviewable
commit passed server preflight and compilation. No push was made by the dry run.
