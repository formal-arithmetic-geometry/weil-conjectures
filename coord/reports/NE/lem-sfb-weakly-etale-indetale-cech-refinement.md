## Worker report

The module `Sheaf.AlgebraicGeometry.WeaklyEtaleIndEtaleCechRefinement` states
`AlgebraicGeometry.exists_finite_affine_indEtale_cech_refinement`. Its proof is
`sorry`, with the complete five-step DAG proof plan in the declaration docstring.
No definitions, additional lemmas, new nodes, or dependency repairs are needed.
The copied node changes only its `lean` field.

Clause-by-clause reading:

- Schemes U and V: `{U V : Scheme.{u}}`. Both are qcqs: `[CompactSpace U]`,
  `[QuasiSeparatedSpace U]`, `[CompactSpace V]`, `[QuasiSeparatedSpace V]`.
- The specified morphism is `(b : U ⟶ V)`, with `[QuasiCompact b]`,
  `[QuasiSeparated b]`, and `[WeaklyEtale b]`, respectively rendering each
  morphism hypothesis. Weak étaleness means flatness and flatness of the diagonal.
- The finite covering family is `∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U`.
  `Finite D.I₀` gives finiteness, and `∀ a, IsAffine (D.X a)` gives affine domains.
  A cover for this precoverage means exactly jointly surjective, weakly étale arrows
  satisfying the finite-affine-open fpqc covering condition. Such domains and arrows
  are objects over the terminal object U/U of the recorded small pro-étale site;
  this is the scheme-family presentation of that covering, not a coarser topology.
- `∀ (n : ℕ) (a : Fin (n + 1) → D.I₀)` renders every nonnegative integer and every
  ordered tuple of length n+1, with repeated indices allowed.
- `(∏ᶜ fun i : Fin (n + 1) ↦ Over.mk (D.f (a i))).left` is exactly the iterated
  scheme fibre product over U: products in the slice category of schemes over U
  have that universal property. Its `.hom` is the canonical map to U. No product
  over V is substituted. `CompactSpace` and `QuasiSeparatedSpace` of this `.left`
  render the two qcqs clauses.
- `∃ T : Scheme.OpenCover.{u} ...` gives an open cover of the entire tuple term;
  `Finite T.I₀` and `∀ β, IsAffine (T.X β)` give a finite affine open cover.
- For every β, `∃ (W : V.Opens) (_hW : IsAffineOpen W) (g : T.X β ⟶ W.toScheme)`
  introduces its affine target open and factoring map. `proAffineEtale g` is the
  recorded affine pro-étale property, equivalent on these affine schemes to the
  induced ring map being ind-étale. Its definition uses an index in `Type u` and
  `SmallCategory`, with filtered étale ring presentations. Étale ring algebras are
  finitely presented; hence the small filtered presentation clause is included.
- `g ≫ W.ι = T.f β ≫ (...).hom ≫ b` specifies that this is the stated composite
  to V, not an unrelated map from the chart.
- There is no affineness or weak-contractibility assertion about the whole tuple
  term, and no coefficient or cohomological datum among the hypotheses.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`; schemes use its equivalent topological
  `QuasiSeparatedSpace` form.
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`:
  `AlgebraicGeometry.WeaklyEtale` (flat and flat diagonal).
- `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`:
  `AlgebraicGeometry.proAffineEtale`, `proAffineEtale_Spec_iff`, and
  `proAffineEtale_iff_appTop`; its public dependency
  `WeilConjectures.RingTheory.ProEtale.IndEtale` gives `Algebra.IndEtale` and
  `RingHom.IndEtale`. These are the exact recorded sk-def-pe-morphisms interface.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`,
  `ProEt.forget`, `ProEt.precoverage`, and `Scheme.proetalePrecoverage`.
- The scheme-convention and size-convention nodes are explicitly recorded as
  conventions, with no declaration to import. The statement uses their specified
  Mathlib classes, `Scheme.{u}`, and universe-u cover indices and presentations;
  no independent lower test universe is introduced.
- Existing `CategoryTheory.Limits.piObj` in `Over U` supplies the tuple term,
  with `Mathlib.CategoryTheory.Limits.Constructions.Over.Basic` supplying its
  finite-limit infrastructure. This is existing categorical machinery, not a
  new notion needing a node.

All proof-dependency modules with recorded declarations are imported (proof-only
imports are non-public): EtaleComparison, IndEtaleSmallIndex,
FiniteAffineTensorBaseChange (the upstream module), ProEtaleQcqsSiteLimits,
QuasiCompactOpenIntersection, WeaklyEtaleStability, and the upstream
WeaklyEtaleIndEtale refinement theorem. Mathlib proof dependencies are available
through these imports and the statement imports. The refinement declaration
`RingHom.WeaklyEtale.exists_indEtale_comp` was read in its actual upstream module;
its node's attachment has a declaration list rather than a primary module field.
No imports were omitted because of cycles.

Edge cases checked: U may be empty and no `Nonempty D.I₀` is required. For an empty
index family there is no map `Fin (n+1) → D.I₀`, so tuple conclusions are correctly
vacuous. Empty tuple terms permit an empty open cover. The zero ring and empty
scheme are not excluded. At n=0 the slice product has one factor and is canonically
that factor; repeated indices in every degree are unrestricted. Non-affine,
non-separated qcqs schemes are allowed; only the explicit charts are affine.
No claim of weak contractibility or affineness of a whole multiple intersection
has slipped into the statement.

Source check: read the supplied Bhatt--Scholze PDF with `pdftotext -layout`.
Theorem 2.3.4 provides the faithfully flat ind-étale refinement, Proposition
2.3.3(4) supplies permanence, and Remark 4.1.3 gives the affine-local geometric
interpretation. The DAG's additional finite-cover and Čech bookkeeping agrees
with its five proof steps. No statement fault or correction was found.

Searches before writing:

- `msearch.py ... leanfinder`: “A quasi compact weakly etale morphism has a finite
  affine pro etale covering whose Cech intersections are locally ind etale over
  affine base opens”. Eight hits: ordinary affine cover/refinement constructions
  and étale site definitions, none giving this theorem.
- `msearch.py ... loogle`: `"WeaklyEtale", "QuasiCompact"`. Zero hits.
- `msearch.py ... grep`:
  `(indEtale|IndEtale|weaklyEtale|WeaklyEtale).*(cech|Cech|refinement|cover)`.
  Zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, weakly-etale Čech refinements and ind-étale Čech terms found no
  existing statement. A wider refinement/cover search found the existing
  proAffineEtale APIs and the affine ring refinement theorem used by the proof,
  with no theorem packaging the finite geometric cover and all Čech terms.
- Read the supplied example module and node. The current CompactObject module is
  withdrawn and has no declarations; the module header instead follows the
  current stage brief and the nearby WeaklyEtaleStability module.

Validation: the prescribed `scompile.py NE <item> <file>` passed both the sandbox
compile (18.2 seconds) and the library-path compile (10.1 seconds), without errors
or unexpected warnings. Delivery dry-run and push results are recorded below.

## Second reading by NE

(Written by the maintainer's cc second reader, because the delivered section was a
self-check that said no independent reading had been done (H11). The worker report
above is kept verbatim.)

The node's statement, listed, and the Lean that renders each part:

1. Schemes U, V, both qcqs (def-pc-scheme, def-weil-pbc-scheme-conventions):
   `{U V : Scheme.{u}}` with `[CompactSpace U] [QuasiSeparatedSpace U]
   [CompactSpace V] [QuasiSeparatedSpace V]`. Correct. Mathlib gives the scheme form
   of "quasi-separated" as `QuasiSeparatedSpace` (`quasiSeparated_iff_quasiSeparatedSpace`).
2. b : U → V is quasi-compact, quasi-separated and weakly étale:
   `(b : U ⟶ V) [QuasiCompact b] [QuasiSeparated b] [WeaklyEtale b]`. Correct.
   `QuasiSeparated b` already follows from U being qs, but the node states it, so it
   adds no assumption.
3. A finite covering family q_a : D_a → U in U_proét, with every D_a affine:
   `∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U, Finite D.I₀ ∧ ∀ a, IsAffine (D.X a)`.
   `proetalePrecoverage = propQCPrecoverage @WeaklyEtale`. Its families are
   weakly étale maps that are jointly surjective and satisfy the quasi-compact
   (affine-open finite-image) covering condition. That is exactly
   def-weil-pbc-proetale-covering. The domains are weakly étale U-schemes in
   Scheme.{u}, i.e. objects of U_proét (Scheme.ProEt U). Correct.
4. For every n ≥ 0 and every tuple (a_0,…,a_n), repeats allowed:
   `∀ (n : ℕ) (a : Fin (n + 1) → D.I₀)`. Correct.
5. D_{a_0…a_n} = D_{a_0} ×_U ⋯ ×_U D_{a_n}: `(∏ᶜ fun i ↦ Over.mk (D.f (a i))).left`.
   A finite product in `Over U` is the wide fibre product over U. Its `.hom` is the
   structure map to U. It is over U, not V. Correct.
6. That scheme is qcqs: `CompactSpace (…).left ∧ QuasiSeparatedSpace (…).left`. Correct.
7. The composite b_{a_0…a_n} has a finite affine open cover T_β:
   `∃ T : Scheme.OpenCover.{u} (…).left, Finite T.I₀ ∧ ∀ β, IsAffine (T.X β) ∧ …`. Correct.
8. Each T_β → V factors through an affine open V_β with T_β → V_β affine pro-étale:
   `∃ (W : V.Opens) (_hW : IsAffineOpen W) (g : T.X β ⟶ W.toScheme), proAffineEtale g ∧
   g ≫ W.ι = T.f β ≫ (…).hom ≫ b`. `proAffineEtale` is the recorded sk-def-pe-morphisms
   declaration, `MorphismProperty.pro.{u} (Etale ⊓ affine source)`. It forces T.X β to
   be affine (`proAffineEtale.isAffine`). On affine source and target,
   `proAffineEtale_iff_appTop` makes it equivalent to `RingHom.IndEtale` of the
   induced map on global sections. That is a small (universe-u) filtered colimit of
   finitely presented étale algebras, as the node says. The equation pins g to the
   stated composite. Correct.
9. No assertion that the whole fibre product is affine or weakly contractible, and no
   coefficient or cohomological hypothesis: none appears in the Lean. Correct.

Edge cases:
- U empty: the empty family is a cover (`bot_mem_propQCPrecoverage`), and nothing
  forces `Nonempty D.I₀`. With an empty index there is no tuple, so the clauses are
  vacuous.
- n = 0: a one-factor product, which is canonically D_a.
- Repeated indices are allowed, and empty tuple terms allow an empty open cover.
- Non-separated U and V, and V empty, are allowed.
- Universes: the cover indices and the pro-presentations are all in universe u, the
  scheme universe. This matches def-weil-size-convention, and no extra universe
  restriction is imposed.

Records: the node copy differs from the landed node only in `lean`. `lean.statement` is
verbatim the signature in the file, and the proof is `sorry` alone. The module and
declaration docstrings carry the source place and `(blueprint: …)`. The declaration
docstring follows all five node proof steps. There are no new definitions, so there is
no hollow data. The stmt_deps used are Mathlib Scheme/QuasiSeparated/WeaklyEtale/ProEt
and the upstream proAffineEtale. Neither convention node has a declaration.

Search: no existing declaration packages finite affine ind-étale refinements together
with their Čech terms. The upstream `RingHom.WeaklyEtale.exists_indEtale_comp` is the
affine ring-level refinement used in step 1. It is not the item.

Findings: no mismatch in the Lean or in the records. The only change is this section,
which replaces the self-check.
