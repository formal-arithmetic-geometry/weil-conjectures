## Worker report

The module `Sheaf.Paper.ProfiniteTestObjectFunctor` states
`AlgebraicGeometry.ProEtale.profinite_test_object_functor`, with its entire proof `sorry`.
It uses the existing framework construction `profiniteToProEtOf X`, rather than
introducing another test scheme or another site. No node statement or dependency is changed.

Source read: the exact side framework's
`WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean`, especially its module
docstring at lines 38–52, the input descriptions at lines 112–120, and declarations
at lines 151–223. These explicitly describe the construction and its finite-quotient
limit interpretation, as in the cited Section 4 equations finite-XI/XS and Lemma lem:XS.
Also read `coord/pefw-upstream-framework.md`. The separately archived TeX and Stacks
checkout are absent on this machine; the exact Basic module is an expressly named
source of this node and is available in full.

Hypotheses and clauses, in order:

- The size convention is implemented by the explicitly bound universe `u` on
  `Scheme`, `Profinite`, finite sets, cover index sets and the small cofiltered index
  category. The dependency's record is a metatheoretic convention and has no module
  or declaration. There are no derived-category constructions in this statement.
- `X : Scheme.{u}` is arbitrary: no affine, quasi-compact, quasi-separated, nonempty,
  or Noetherian hypothesis is imposed.
- Mathlib `Profinite.{u}` has compact Hausdorff totally disconnected objects and
  continuous morphisms. The finite jointly surjective families are quantified
  explicitly in the covering clause.
- The existing `profiniteToProEtOf X : Profinite.{u} ⥤ X.ProEt` supplies the actual
  test objects, their weakly etale maps to `X`, maps for all continuous functions,
  and compatibility with identity and composition. `Scheme.ProEt` is the full
  weakly etale subcategory of schemes over `X`, exactly as the site dependency says.
- The first conjunct is `PreservesFiniteLimits (profiniteToProEtOf X)`.
- The second conjunct quantifies every finite `A : Type u` and asserts preservation
  of `Discrete A` colimits. This is finite disjoint-union preservation, including
  the nullary disjoint union.
- The third conjunct is a natural isomorphism from the finite-set restriction of
  the test functor, after `Scheme.ProEt.forget X`, to
  `forget FintypeCat ⋙ sigmaConst.obj (Over.mk (𝟙 X))`. The latter is precisely the
  diagram of coproducts of copies of `X` **in schemes over X**. `sigmaConst` uses
  `Sigma.map'` on a set map, so naturality identifies every transition map too.
- The fourth conjunct quantifies a small cofiltered category `I`, a diagram
  `D : I ⥤ FintypeCat.{u}`, and a cone `c` on its finite discrete profinite diagram.
  The hypotheses `IsLimit c` and `∀ i, Function.Surjective (c.π.app i)` say exactly
  that the cone is a finite-quotient presentation of its profinite vertex.
  `Nonempty (IsLimit ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X).mapCone c))`
  asserts the universal property of the image cone in `Over X`. Together with the
  preceding **natural** finite-stage identification, this is the asserted existence
  of `lim_i ∐_{s ∈ S_i} X` as an X-scheme. It retains all its legs and the transition
  maps. IsLimit supplies a unique comparison respecting legs with any other such
  presentation: this is the canonical presentation independence. The chosen vertex
  is always the same existing test object, and its maps are the existing functor's
  maps; no noncanonical pointwise choice replaces that functor.
- The fifth conjunct quantifies any finite family `S`, target `T`, and continuous
  maps `f`. Its sole hypothesis `∀ t, ∃ a s, f a s = t` is joint surjectivity.
  `Presieve.ofArrows ... ∈ Scheme.fpqcPrecoverage ...` says the corresponding
  actual underlying scheme arrows are an fpqc covering family, rather than merely
  saying their generated sieve covers. The fact they are arrows in `X.ProEt`
  supplies weak etaleness, so this is also a pro-etale covering in the named site.
- The final conjunct is a natural isomorphism of scheme-valued functors from
  `profiniteToProEtOf specZ` (forgetting its structure map) to the existing
  `profiniteToScheme`. The latter is literally `profiniteToCommRingCatOp ⋙ Scheme.Spec`.
  Its object is `Spec LC(S,ℤ)` and its map is `Spec` of
  `LocallyConstant.comapRingHom f.hom.hom`. Thus the identification includes
  functoriality and the specified action by precomposition. `specZ` is the standard
  universe-lifted terminal scheme `Spec (ULift ℤ)`, canonically `Spec ℤ`.

Dependency declarations read and used:

- `def-weil-size-convention`: its `lean.convention = true` record has no declaration;
  its prescribed explicit universe convention is followed directly.
- `def-weil-pbc-proetale-site`: recorded module
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, declaration
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; full source/docstring read and
  module imported. Its docstring explicitly uses the same Mathlib `Y.ProEt` and
  `ProEt.topology Y` that the statement and the existing framework use. This node
  also defines coefficient and derived categories, which this item does not use;
  no dependency replacement is required for the site paragraph.
- Existing construction: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.profiniteToProEtOf`, `profiniteToProEt`,
  `profiniteToScheme`, `profiniteToCommRingCatOp`, `specZ`.
- Finite-set and relative-limit interfaces: Mathlib's `FintypeCat.toProfinite`,
  `CategoryTheory.Limits.sigmaConst`, `Over.mk`, `Functor.mapCone`, and `IsLimit`.
- Covering interface: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicGeometry.Scheme.fpqcPrecoverage` and `CategoryTheory.Presieve.ofArrows`.

The module imports every available recorded proof-dependency module, with ordinary
(non-public) imports for those used only by the proof plan. In particular it imports
`Sheaf.AlgebraicGeometry.LimitAffineTransition` for
`AlgebraicGeometry.exists_limit_affine_transition_core`. The proof dependency
`lem-weil-pbc-locally-constant-prime-spectrum` has no recorded Lean module yet,
so there is none to import. The module docstring reproduces all ten proof steps
with their dependencies, including that future input.

Edge cases checked mathematically: `X` may be empty or non-quasi-compact; the
construction is a relative base change and no global affine assumption enters.
An empty profinite space has the empty finite quotient and zero locally constant
ring; its spectrum is empty. Empty finite coproducts are explicitly included by
`[Finite A]` with no `Nonempty A`. An empty jointly surjective family forces `T`
to be empty, and its fpqc condition is vacuous on that empty test scheme. A
one-point profinite set gives `X` and a one-stage presentation is allowed. The
cofiltered category is nonempty as part of `IsCofiltered`, not an added assumption.
There is no nonemptiness requirement on any finite quotient or on the profinite
vertex. The index category is small in the same universe as the finite sets and
schemes, avoiding vacuous hypotheses from a smaller independent universe.

Searches actually run:

- `msearch.py leanfinder`: “The profinite test scheme functor over any scheme
  preserves finite limits finite disjoint unions and sends finite jointly
  surjective covers to fpqc covers”: eight hits, involving affine-transition
  limits, quasi-compact covers and light condensed sites; no exact match.
- `msearch.py loogle`: `Profinite, CategoryTheory.Limits.IsLimit`: twelve hits,
  including `Profinite.asLimit`, `Profinite.exists_locallyConstant`, and
  `Profinite.Extend.functor_initial`; none states the relative test-functor theorem.
- `msearch.py grep`: `profiniteToScheme|profiniteToProEt|LocallyConstant.*Spec`:
  zero Mathlib hits.
- `msearch.py leansearch`: “The functor from profinite spaces to schemes given
  by the spectrum of locally constant integer-valued functions preserves finite
  limits”: unavailable, HTTP Internal Server Error; not recorded as a negative result.
- Direct `rg` of the upstream project for the node id: no hits. Concept searches
  of upstream `WeilConjectures`, and project `lean/Sheaf` for
  `profiniteToProEtOf`, `profiniteToProEt`, and profinite finite-quotient terms:
  no existing complete theorem. The exact side framework has the functor and
  the two partial input theorems over `Spec ℤ`, but does not state the arbitrary
  presentation or finite-disjoint-union clauses. Those partial inputs are reused
  through its imported module; they are not a complete existing match.
- Direct `rg` for the proposed full declaration name across upstream project,
  Mathlib, project `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No missing notion, unusable dependency, or statement dispute was found. No new
node or dependency module is added. The independent second reader will review
and deliver; this worker only runs the dry run.


## Second reading by NL

Read the item node, its entire ten-step proof, both statement dependency nodes,
`ProEtaleDerivedCategory.lean`, and the exact side framework
`WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean` (definitions at
151–224 and source discussion at 38–52). Also read
`coord/pefw-upstream-framework.md` and Mathlib's Proetale, Fpqc, Profinite.Basic,
Profinite.AsLimit and Products declarations. The archived RefactorInstruction
and Stacks TeX checkouts are absent here. The exact Basic module is itself a
named source of this node and explicitly gives the arbitrary-scheme base-change
construction and its relative limit interpretation. Independently read the
related Stacks lemma at https://stacks.math.columbia.edu/tag/097D: it assumes an
arbitrary ring, not a field or Noetherian ring. That lemma treats a more general
relative component-space construction, rather than literally stating all of
this node; the node's explicit proof supplies the additional arguments.

Object/hypothesis/conclusion checklist, in node order:

- Universes: `universe u`, `Scheme.{u}`, `Profinite.{u}`, `FintypeCat.{u}`,
  `A : Type u`, and `I : Type u` implement the bounded smaller universe.
  The size node is a metatheoretic convention with no declaration. No derived
  categories or coefficient hypotheses enter here. Verdict: matches.
- Profinite spaces and continuous arrows: Mathlib `Profinite` is the compact
  Hausdorff totally disconnected category, with continuous maps. Finite covers
  are expressed by the explicit finite-family clause. Verdict: matches.
- Arbitrary base scheme: `(X : Scheme.{u})`, without any additional instance
  or property. Verdict: matches, including non-quasi-compact bases.
- Small pro-etale site: `X.ProEt`, with its actual full-subcategory forgetful
  functor `Scheme.ProEt.forget X`. The recorded site's module imports and uses
  these same Mathlib objects; its extra coefficient-category construction is
  irrelevant here. Verdict: matches, no replacement dependency needed.
- Test objects and weakly etale structure maps: `profiniteToProEtOf X` is the
  existing functor formed by base change of `profiniteToProEt` along `toSpecZ X`.
  Its values are bundled weakly etale maps. Its domain includes every profinite
  space and all continuous maps. Functor laws provide identities and composition.
  Verdict: matches; no new or hollow construction.
- Presentation: `D : I ⥤ FintypeCat.{u}` with `[SmallCategory I]`
  `[IsCofiltered I]`, `c : Cone (D ⋙ FintypeCat.toProfinite)`, `IsLimit c`,
  and surjectivity of every `c.π.app i`. These say precisely finite discrete
  quotient presentation, without imposing extra conditions on `X` or `S`.
  Verdict: matches.
- Relative limit existence and identification: the natural isomorphism from
  the finite-set restriction to `forget FintypeCat ⋙ sigmaConst.obj
  (Over.mk (𝟙 X))` identifies every stage and every transition with the finite
  coproduct over X. Mathlib `sigmaConst` maps a function by `Sigma.map'` with
  identity component maps. `Nonempty (IsLimit (...mapCone c))` supplies the
  universal property for the specified image cone in `Over X`. Thus its vertex
  is the inverse limit in X-schemes. Verdict: matches, including cone legs.
- Canonical presentation independence: the same functorial vertex works for
  every presentation; the above natural identification and limit uniqueness
  give unique comparison isomorphisms respecting the legs. This is stronger
  information than a bare object isomorphism and expresses the node's canonical
  independence. Verdict: matches.
- Finite limits: `PreservesFiniteLimits (profiniteToProEtOf X)` is in precisely
  the required codomain. Verdict: matches.
- Finite covers: `∀ (A : Type u) [Finite A] ...`, with sole premise
  `∀ t, ∃ a s, f a s = t`, quantifies the required finite jointly surjective
  families. `Presieve.ofArrows ... ∈ Scheme.fpqcPrecoverage ...` asserts fpqc
  covering of their actual underlying scheme arrows. Maps between weakly etale
  X-schemes are weakly etale, so this is the indicated pro-etale covering too.
  Verdict: matches; no mere generated-sieve substitute.
- Finite disjoint unions: `∀ (A : Type u) [Finite A],
  PreservesColimitsOfShape (Discrete A) ...`. Verdict: matches all finite
  coproducts, including the nullary coproduct.
- Integral base and action on maps: final natural isomorphism compares
  `profiniteToProEtOf specZ` after forgetting to schemes with `profiniteToScheme`.
  The exact framework defines `specZ = Spec (ULift ℤ)` as the terminal scheme,
  `profiniteToScheme = profiniteToCommRingCatOp ⋙ Scheme.Spec`, and the latter
  ring functor's maps as `LocallyConstant.comapRingHom f.hom.hom`. Verdict:
  matches Spec LC(-,Z) functorially, including precomposition, with the standard
  universe lift of Z.

Edge cases: no `Nonempty` condition is imposed on X, the profinite spaces, finite
quotients, or finite family index. Empty S gives the zero locally constant ring
and empty scheme. A jointly surjective empty family forces empty target. The
empty coproduct is explicitly included. A singleton gives X. Cofilteredness
requires a nonempty indexing category, as a cofiltered presentation does; this
does not exclude the empty profinite space. Universes are shared with the
scheme and finite quotient category, rather than independently restricted below
it. No characteristic, coefficient-ring, or n assumption is introduced.

Independent searches (in addition to the worker's searches):

- LeanFinder: “Base changing the spectrum of locally constant integer functions
  gives a profinite scheme functor preserving coproducts and inverse limits of
  finite sets”. Eight hits: condensed free/solid functors, profinite product
  diagrams, and light condensed constructions; none is this scheme theorem.
- Loogle: `LocallyConstant, CategoryTheory.Limits.PreservesFiniteLimits`:
  zero hits.
- msearch grep: `profiniteTo|Spec.*LocallyConstant|LocallyConstant.*Spec`:
  25 hits, all on condensed functors, no scheme theorem.
- Direct rg on Mathlib AlgebraicGeometry, upstream WeilConjectures/SixFunctors,
  and project lean/Sheaf with `profiniteTo`, `LocallyConstant` near Spec/Scheme,
  and preservation/profinite terms: no complete theorem. Upstream Adic/UpperStar
  uses locally constant spectra for another purpose. Exact side Basic has the
  construction and partial Spec Z results, not the full relative-presentation
  and finite-coproduct assertion. Profinite.AsLimit is a limit in profinite
  spaces, not this relative scheme limit. No duplicate definition is needed.

No mathematical mismatch found. No new definition node, dependency module,
statement correction, or citer verdict is needed. One metadata mismatch repaired:
`lean.statement` had collapsed whitespace, so it was replaced by the literal
multiline signature from the module, as requested. The Lean module was left
unchanged. Its only theorem proof is `sorry`; its docstring follows all ten
node proof steps and names their dependencies. All variables/universes are
explicitly bound; no private notation, local instance, or new data definition.

Validation: `scompile.py NL lem-weil-pbc-profinite-test-object-functor
lean/Sheaf/Paper/ProfiniteTestObjectFunctor.lean` passed on the server: delivered
module 1.6 seconds, nice 19, two threads, 60-second per-file limit; no warnings
or errors. Side-only framework imports compiled in its private overlay. Literal
signature equality and 100-character Lean line widths were also checked.
The related Stacks source was additionally read directly as TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/proetale.tex,
`lemma-construct-profinite`, including the complete proof. It confirms the
arbitrary-ring hypotheses and finite discrete inverse-system construction.
