## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePseudoCoherenceLocalOnSource` states both
clauses of lem-sfb-relative-pseudocoherence-local-on-source. Its declarations are
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_of_iSup_eq_top` and
`AlgebraicGeometry.Scheme.isPseudoCoherentRelativeTo_of_iSup_eq_top`. Both proofs are
`sorry`, and both docstrings give the source and the complete relevant argument.
No definitions, additional nodes, dependency repairs or statement corrections are needed.

The source was read in `literature/stacks-project/more-morphisms.tex`, at
`definition-relative-pseudo-coherence` (Tag 09UI), clauses (1) and (2),
`lemma-relative-pseudo-coherence-characterize` (Tag 09UJ), including its proof, and
the first paragraph of `lemma-characterize-pseudo-coherent` (Tag 0CSL).
The arbitrary derived object, locally finite type hypothesis, and absence of a
quasi-compactness assumption agree with those passages.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Locally of finite type: `[LocallyOfFiniteType f]`; the same class for
  `(U k).ι ≫ f` is inferred from the open immersion and composition instances,
  rather than imposed as an additional hypothesis.
- The arbitrary object of the unbounded module derived category is
  `(E : schemeDerivedCategory X)`, with no quasi-coherence or boundedness assumption.
- The integer degree is `(m : ℤ)` in the fixed-degree declaration.
- The arbitrary index set is `{I : Type v}`, with its universe independent of the
  scheme and derived morphism universes and with no finite or nonempty instance.
- The open subschemes are `(U : I → X.Opens)`; their schemes are `(U k).toScheme`.
  The covering equation is `(hU : iSup U = ⊤)`.
- The restricted morphism f_k is exactly `(U k).ι ≫ f`.
- The restricted object is exactly `((derivedPullback (U k).ι).obj E)`, hence the
  specified derived pullback rather than an unrelated restriction model.
- The first local hypothesis is `hE : ∀ k : I,
  IsMPseudoCoherentRelativeTo ((U k).ι ≫ f) m
  ((derivedPullback (U k).ι).obj E)`.
  The first conclusion is `IsMPseudoCoherentRelativeTo f m E`.
- The consequence has `hE : ∀ k : I,
  IsPseudoCoherentRelativeTo ((U k).ι ≫ f)
  ((derivedPullback (U k).ι).obj E)` and conclusion
  `IsPseudoCoherentRelativeTo f E`. This definition quantifies over every integer,
  allowing different cover and embedding witnesses for different degrees.
- There are no quasi-compactness assumptions on X, S, or f.
- The shared `[∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]` binder is the existing
  relative-pseudo-coherence interface's choice of derived category models on schemes;
  it is reused without imposing any relation between u, v and w.

Recorded dependency interfaces read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (source lines 36–44 and 73–76).
- `def-pc-morphism-conventions` is a convention record, not a declaration.
  Its locally finite type convention is `AlgebraicGeometry.LocallyOfFiniteType`
  in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (lines 39–47); its
  open-immersion and composition instances (lines 58–66) supply the restricted maps.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, read with its full docstring/signature.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback` and its K-flat/left-derived specification,
  read with the declaration's docstring and universe binders.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo` and
  `AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo`, both read in full.
  That public import also exposes the recorded derived-category and pullback modules.
- The stated proof dependency `lem-weil-pbc-affine-opens-basis` is imported via
  `Mathlib.AlgebraicGeometry.AffineScheme`, with its recorded Mathlib match
  `AlgebraicGeometry.Scheme.isBasis_affineOpens` at line 305.
  `def-weil-finite-type-morphism` uses the same public FiniteType import.
- Proof dependency `lem-sfb-relative-pseudocoherence-all-affine-charts` has no Lean
  record or Mathlib match at reading time, so there is no module to import for it.
  It is named explicitly in both proof docstrings. It is not needed to type the
  statements and is not a missing statement notion.

Edge cases checked before writing: the empty indexing set forces X to be empty by
`hU`; the relative property on the empty source is witnessed by the empty source
covers. Empty cover members add no conditions. A singleton cover with its member
all of X gives the identity restriction case. Infinite covers are allowed and
require no finite subcover or common degree bound. Empty S forces X empty.
The zero object admits zero strictly perfect approximations in every degree;
positive, negative and zero integer degrees are all included. There is no assertion
that intersections of affine opens are affine. No counterexample or node fault found.

Searches performed (all through the prescribed tooling or read-only source searches):

- `msearch.py ... leanfinder "Relative m pseudocoherence of a derived complex on
  schemes is local on the source for an arbitrary open cover"`: eight hits, all
  generic locality results for morphism properties (including
  `AlgebraicGeometry.IsLocalAtSource.of_openCover`), not the relative property of a
  derived object.
- `msearch.py ... leansearch "Relative m pseudocoherence of a derived complex is
  local on an arbitrary open covering of the source scheme"`: eight hits, again
  generic morphism-property locality, not this statement.
- `msearch.py ... loogle '"PseudoCoherent"'`: zero hits.
- `msearch.py ... grep 'pseudo.?[Cc]oher|[Rr]elativ.*[Cc]oher'`: one hit,
  Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean:297, the relative gluing data
  of a quasi-coherent algebra, unrelated.
- `rg -n 'PseudoCoherentRelativeTo|[Pp]seudo[Cc]oher.*[Ll]ocal|relative[Pp]seudo'
  lean/WeilConjectures lean/Sheaf`: found the existing relative definition and the
  closed-support relative criterion; no source-locality theorem. Ring-level
  localization theorems concern a different category and property.
- `grep -rn 'lem-sfb-relative-pseudocoherence-local-on-source'
  lean/WeilConjectures`: no hits.
- `rg -n 'isMPseudoCoherentRelativeTo_of|isPseudoCoherentRelativeTo_of|
  RelativePseudoCoherenceLocalOnSource' lean/WeilConjectures lean/Sheaf
  dag/lean_names_upstream.json`: no hits before creating the module.

## Second reading by Q01

On a separate rereading of the node, source passages and finished file, the first
declaration retains the exact fixed m on every restriction and in the conclusion.
The second declaration renders the separate all-m consequence, rather than adding
its stronger hypothesis to the first declaration. The source morphisms are the
actual inclusions composed with f, and the objects are the recorded derived
pullbacks. The cover equation permits the empty scheme, empty cover members and
arbitrary infinite index sets. All universe variables are explicit, and no additional
quasi-coherence, boundedness, separatedness or quasi-compactness assumption appears.
The derived-category model binder is precisely that used by the existing dependency.
No mismatch or correction was found. This is the dispatcher's single-worker delivery;
the maintainer's independent review follows delivery.

Validation: `scompile.py Q01 lem-sfb-relative-pseudocoherence-local-on-source` compiled
both the sandbox form and library-module form without errors or warnings (7.8 seconds
each). The required `deliver2.py ... --no-push` passed server preflight and per-file
compilation, reporting OK. The node copy differs from the shared node only in `lean`;
all module lines are at most 100 characters.
