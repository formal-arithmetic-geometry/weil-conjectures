## Worker report

The new module `Sheaf.CategoryTheory.AlmostFilteredAbelianColimits` states
`CategoryTheory.almostFiltered_abelian_colimits_exact` with one `sorry` proof.
It introduces no definitions and changes only the item's `lean` field. The
statement and the seven-step natural-language proof are those of the DAG node.
The source was read locally in `literature/stacks-project/algebra.tex`,
lemma-almost-directed-colimit-exact (Tag 04B0), and `categories.tex`,
lemma-split-into-directed (Tag 002X). Additivity and the finite-limit expansion
are the supplements already specified by the node.

Hypothesis and clause correspondence:

- The size convention is rendered by explicitly declared universes `u w`,
  `I : Type u`, `[SmallCategory I]` and coefficients
  `AddCommGrpCat.{max u w}`. Thus both objects and arrows of I fit in the
  coefficient universe, and an arbitrarily larger coefficient universe is
  allowed. There is no independent smaller coefficient universe.
- Hypothesis (a) is `hspan`: for `a : v ⟶ x`, `b : v ⟶ y`, it supplies
  `z`, `c : x ⟶ z`, `d : y ⟶ z` with `a ≫ c = b ≫ d`.
- Hypothesis (b) is `hparallel`: for parallel `a b : x ⟶ y`, it supplies
  `z`, `c : y ⟶ z` with `a ≫ c = b ≫ c`.
- Neither `Nonempty I`, `IsConnected I` nor `IsFiltered I` is assumed.
- All diagram colimits exist: the first conjunct is
  `HasColimitsOfShape I AddCommGrpCat.{max u w}`. Mathlib already provides
  this instance, so the subsequent chosen `colim` and `colimit` terms require
  no additional assumption or choice from a postponed theorem.
- The second conjunct is `.Additive` for the actual Mathlib `colim` functor.
- The third is `PreservesFiniteLimits` for that same functor, including the
  empty limiting diagram, products and equalizers.
- A sequence of diagrams is `S : ShortComplex (I ⥤ AddCommGrpCat.{max u w})`.
  The antecedent asserts `ShortExact` after mapping S by evaluation at every
  `i : I`. `ShortExact` means exactness in the middle, a monomorphism first
  and an epimorphism second, precisely the displayed sequence with zero ends.
  The consequent maps the same S by `colim`; its two arrows are the induced
  colimit maps. The bundled zero-composite equation in `ShortComplex` is
  already implied by pointwise short exactness; it imposes no extra condition
  on a sequence covered by the node.
- The last conjunct says `IsEmpty I → ∀ F, IsZero (colimit F)`, exactly the
  explicit empty-index zero-group clause. In abelian groups categorical
  `IsZero` means the trivial abelian group, independently of a chosen model.

Dependencies and imports:

- `def-weil-size-convention` is recorded as a metatheoretic convention with
  no declaration or import; it is implemented by the universe binders above.
- `def-weil-pbc-category-colimit` uses
  `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
  `colim`, `HasColimitsOfShape`, and the associated cocone/universal property.
  I read the `colimit`/`colim` signatures, the cocone construction, and
  `IsColimit`'s factorization and uniqueness fields. This is the recorded
  Mathlib match, not a private construction.
- `Mathlib.Algebra.Category.Grp.AB` is public: its general colimit additivity
  instance gives the zero-morphism-preservation instance needed to type
  `ShortComplex.map`. It also imports the abelian group category and its
  colimit-existence instance. Its filtered homology-preservation instance is
  the match of proof dependency
  `lem-weil-pbc-filtered-colimit-abelian-groups-exact`.
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact` supplies the standard
  short exactness predicate. Its full three-field definition was read.
- The proof-only import
  `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit` is the
  recorded Mathlib module of
  `lem-weil-pbc-filtered-colimits-commute-finite-limits`; its finite-limit
  comparison declarations were read, along with the Ab instance in `AB`.
- Proof dependency `lem-sfb-almost-filtered-components` currently has no Lean
  record, Mathlib match or closed upstream audit in the read clone. Its full
  statement was read; there is no recorded module to import. It is cited in
  the proof docstring. The current statement needs neither its construction
  nor a missing notion, so it is not restated here.

Searches for an existing statement:

- `msearch.py ... leanfinder`, query: "Colimits of abelian groups over
  possibly empty disconnected categories with commuting span completions and
  coequalizable parallel arrows are additive and exact". Eight hits included
  `AddCommGrpCat.hasColimitsOfShape`, `hasColimit`, AB4, AB4Star, AB5 and
  filtered-colimit existence. These cover clauses or filtered components,
  not this two-condition result for possibly disconnected I.
- `msearch.py ... loogle`, query: `"colim", "PreservesFiniteLimits"`.
  Eight hits included `HasExactColimitsOfShape.preservesFiniteLimits` and
  `instPreservesFiniteLimitsFunctorAddCommGrpCatColim`. The latter requires
  `IsFiltered I`; the former assumes the exactness being asserted.
- `msearch.py ... grep`, query:
  `almost.*filtered|almost.*directed|component.*[Ff]iltered`, subdirectory
  `CategoryTheory`. Zero hits.
- `msearch.py ... leansearch`, query: "Abelian group colimits over
  categories satisfying the two almost filtered arrow conditions preserve
  finite limits and short exact sequences". Eight hits included the same
  filtered finite-limit instance, `colimitLimitIso`, AB5 and filtered group
  colimit constructions. Reading the signatures confirms the extra global
  filteredness requirement, so none is the whole statement.
- `rg` in Mathlib, `lean/WeilConjectures` and `lean/Sheaf` for almost-filtered,
  almost-directed and colimit finite-limit terminology found no exact
  declaration. Exact node-id search in `lean/WeilConjectures` found none;
  in `lean/Sheaf` it found only the proof-docstring citation in
  `AbelianLowerShriekExact.lean`. I also read that consumer's signature and
  docstring. The existing Set-valued almost-filtered result concerns another
  coefficient category and does not replace this theorem.
- The proposed declaration name was checked against all three source trees;
  it is new. No search service failure occurred.

Edge cases checked mathematically before writing: empty I satisfies the arrow
hypotheses vacuously, has zero colimit, and gives a zero short exact sequence;
a discrete category of any size gives a direct sum, including infinite
finite-support sums; the one-object identity category gives the original
sequence; the zero diagram stays zero. A nontrivial group as a one-object
category fails the parallel-arrow condition, so nonexact coinvariants are
excluded. A branching span without a commuting completion fails `hspan`.
Finite products commute with these direct sums by union of finite supports;
there is no claim about infinite-limit preservation. No statement correction,
new node, dependency repair or STATEMENT-DISPUTED fault is needed.

Validation: the prescribed `scompile.py Q151
lem-sfb-almost-filtered-abelian-colimits <file>` compiled both its sandbox and
library-module modes successfully, without errors or warnings (1.1 s and
1.2 s respectively). All variables and universes are explicit, `autoImplicit`
is false, and the only theorem proof is `sorry`.

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
