## Worker report

The module `Sheaf.Paper.SystemProperOpenInvertibility` states
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.systemProperOpenInvertibility`.
Its sole theorem has proof `sorry`. The two helper definitions
`systemProperOpenFiniteSource` and `systemProperOpenFiniteTarget` are concrete
composites of existing isomorphisms; neither selects data by an existence axiom.
No mathematical statement correction is needed. The H2 repair adds one definition
ownership node with existing:true, without adding a Lean module.

Hypothesis and clause correspondence:

- The finite field and its fixed algebraic closure are `D : FiniteFieldDatum.{u}`.
  The prime and its distinction from the characteristic are `[Fact l.Prime]` and
  `_hl : l ≠ D.p`. The extension is `E₀ : Type u` with `Field`, `Algebra (Padic l)`
  and `FiniteDimensional` instances. Its valuation ring and chosen uniformizer
  are those already used by `Padic.coefficientExtensionRing`.
- The actual positive quotients and their quotient transitions are the published
  `compactSupportSystemLevel l E₀` and `compactSupportSystemQuotient l E₀`.
  Index `n : ℕ` denotes the node's positive level `n+1`, including its first level.
  The carrier is canonically lifted to universe `u+1`; the quotient ring remains
  exactly the recorded quotient, with no new coefficients or scalar extension.
- `A B C T : Scheme.{u}` denote the node's `A B C D`, respectively. Each is over
  `Spec D.k`, with locally finite type, quasi-compact and separated structure map.
  The four arrows are over that same base. The classes on `k,i` impose exactly
  quasi-compact open immersions, the classes on `r,p` properness, and
  `h : k ≫ p = r ≫ i` is the given commutative square.
- `Derived ... A` is the ordinary derived category of actual semilinear systems
  over the constant coefficient sheaves on the sequence site. It is not a sequence
  of unrelated derived objects. The existing `Modules`, `Derived`, `P`, `R`, `adj`
  and `J` retain the given semilinear transitions and the canonical adjunctions.
- The node's `s` is the published `StrictTower.squareLift k r p i h`, with its
  clopen structure. The existing `pi`, `beta`, and `alpha` in
  `SemilinearProperOpenMatePasting` build precisely the clopen identity/zero
  projector, inverse-open-unit transpose, and their composite with the open and
  pullback compositors. `gamma` is defined as `mateEquiv (adj ... r) (adj ... p)
  (alpha ...)`. Thus `e.hom = gamma.app H` identifies the displayed mate itself;
  it does not hypothesize an arbitrary comparison or infer equality by evaluation.
- `hH : ∀ n, ...` imposes intrinsic constructibility in every cohomological degree,
  using the recorded `IsConstructibleProEtaleFixedModuleSheaf` on the underlying
  fixed-module sheaf obtained by `proEtaleModuleRestriction`. The second conjunct
  is `∃ a b : ℤ, a ≤ b ∧ ∀ q, (q < a ∨ b < q) → IsZero ...`. Both bounds are inside
  `∀ n`; no bound is uniform. Finiteness of the coefficient ring is supplied by
  `Padic.finite_coefficientExtensionRing`, transported through `Equiv.ulift`,
  rather than assumed. The ordinary cohomology functor acts on the actual level
  obtained by `E ... n` followed by `StrictTower.ev ... 0`.
- `∃ e : J_i(R_r H) ≅ R_p(J_k H), e.hom = gamma.app H` is exactly invertibility
  of the specified mate. The following clause gives inverse naturality explicitly
  for every morphism `f : H ⟶ H'` and every isomorphism `e'` with the prescribed
  forward arrow. No extra condition is placed on an already invertible target:
  on the node's full domain such an `e'` is supplied by the same theorem.
- At each level the conclusion supplies a `ScalarEtaleOrigin` whose coefficient
  carrier equals `compactSupportSystemLevel ... n` and whose scalar homomorphism
  is heterogeneously equal to that ring's identity. The witness preserves its
  own origin complex and comparison isomorphism. The origin API is bounded below;
  every bounded constructible origin furnished by the recorded origin theorem is
  included. There is no etale-origin hypothesis on `H` and no uniform origin bound.
- For every such witness (not merely the existentially supplied one), the equality
  of isomorphisms identifies both the evaluated `e.hom` with `finiteGamma.hom`
  and the evaluated `e.inv` with `finiteGamma.inv`: applying `Iso.hom` gives
  the forward normalization equation; taking inverses gives the inverse equation.
  `finiteGamma` is the dependency's specified finite proper/open comparison.
  The helper source is `finiteSource` followed by the evaluation of
  `evalSource.symm`; the helper target is `finiteTarget` followed by evaluation of
  `evalTarget.symm`. These are exactly the canonical open/direct-image/evaluation
  comparisons. The universal witness clause includes every bounded etale-origin
  witness and records independence of its choice. The bounded-below API permits
  the same equation for any additional origin witness of this same level, as already
  stated by `gamma_finite`. Equality of isomorphisms packages the two arrow equations
  without separately elaborating their repeated transport composites.
- No `IsPullback` hypothesis occurs. Thus non-Cartesian squares, `r = 𝟙`, identity
  squares, and clopen refinement squares are retained. No system normalization,
  common lower bound, Tor amplitude or flatness hypothesis occurs.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and `pullback.lift`, used through the published square lift.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  construction import: `Padic.finite_coefficientExtensionRing`,
  `coefficientExtensionRing`, `coefficientExtensionTransition`.
- `Sheaf.Paper.SemilinearDerivedSections`: actual `Systems` and `DS`,
  `SemilinearDerivedSectionsData`, `semilinearDerivedSections`, and the
  unit/counit-normalized `AdjunctionEvaluation` / `evaluation_mate` interface.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`: `Modules`, `Derived`, `P`,
  `R`, `adj`, `J`, `pi`, `beta`, `alpha`, `gamma`, `E`, `evalSource`, `evalTarget`,
  `gamma_evaluation` and `gamma_finite`. These are reused, never restated.
- `Sheaf.Paper.CompactSupportNativeSystemEvaluation`:
  `compactSupportSystemLevel`, `compactSupportSystemQuotient`.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, the recorded intrinsic predicate.
- `Sheaf.Paper.ProEtaleConstantModuleEncoding`: `proEtaleModuleRestriction`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`: `constructible_proEtale_origin` and
  `ConstructibleOriginComparison`; its intrinsic/existing coefficient comparisons
  provide the origin without changing the input hypothesis.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`: `finiteSource`,
  `finiteTarget`, `finiteGamma`, `gamma_evaluation`, `gamma_isIso`; its public
  transport imports supply `ScalarEtaleOrigin` and `HD`.
- `Sheaf.SixFunctors.OpenTensorNormalization`: the normalized open-unit transpose.
- `Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars`: evaluation of the actual
  clopen mate word. These last two modules are proof imports.
- `def-weil-size-convention` and `def-weil-scheme-morphism-properties` are recorded
  conventions, not missing declarations. The site keeps objects in `u+1`, arrows
  in `u`, coefficients in `u+1` and derived localization in `u+2`.

The added statement dependencies are definition owners: semilinear operations,
intrinsic comparison and mate, the positive coefficient sequence, the landed
scalar-restriction definition, and the new existing:true evaluation-comparison
owner. The two added theorem dependencies identified in return H2 are removed.
All original statement and proof dependencies are preserved. No dependency node
is changed, and no downstream compositor module is imported.

Edge cases checked before and after drafting: the zero object has a valid interval;
empty schemes and empty opens are allowed by the recorded positive-stratification
convention (one empty stratum), and the theorem imposes no nonempty hypothesis.
Level zero means quotient power one. The case `r = 𝟙` preserves the clopen section
projector. Identity horizontal/vertical arrows and non-Cartesian squares have the
same mate definition. Intervals may vary arbitrarily with `n`. Nonflat quotient
maps, including the usual higher-power quotients, are not excluded. All universes
and variables are explicitly bound; `autoImplicit false` is set.

Searches made for reuse:

- `msearch.py`, LeanFinder, query `proper open adjunction mate invertibility derived
  semilinear varying ring systems`: eight hits, led by condensed locally-constant
  adjunctions and generic adjunction-composition lemmas; no matching theorem.
- `msearch.py`, Loogle, `CategoryTheory.Adjunction, CategoryTheory.IsIso`: twelve
  generic adjunction/equivalence hits; no geometric varying-ring assertion.
- `msearch.py`, LeanSearch, `derived varying coefficient systems proper open
  comparison isomorphism bounded constructible levels`: eight generic proper/open
  scheme morphism hits; no matching theorem.
- `msearch.py`, grep, `semilinear.*proper|proper.*open|properOpen` in
  `CategoryTheory`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for proper/open, semilinear and
  varying-ring names located the actual system mate, constant-ring calculus and
  evaluation normalization interfaces listed above. Upstream proper/open
  comparisons concern etale fixed coefficients and do not assert this item.
- Search for the exact item id in both Lean source trees found only a downstream
  compositor's proof-docstring reference, not an existing statement. Searches for
  `systemProperOpen` and `gamma_isIso` found no matching semilinear theorem.
- Read Stacks `more-etale.tex`, `lemma-shriek-proper-and-open` (Tag 0F7B), and the
  current blueprint's `sec-six-functors/sk-thm-sf-compatibility` statement/proof.
  The system extension and its five proof steps are the accepted node's agent
  assembly, not claimed as a verbatim Stacks system theorem.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
The early fully expanded version was factored into the two concrete comparison
helpers after a local compiler timeout. No limit or launcher tool was modified.


## Repair of H2 at 13c4f0cf25dc

The saved packet first passed deliver2.py --no-push (commit e824e87d438).
That mechanical pass does not resolve the independent ownership return. This repair
removes `lem-sf-semilinear-proper-open-mate-pasting` and
`lem-weil-pbc-proetale-constant-module-encoding` from the added `stmt_deps`.
`Derived`, `R`, `J`, `E` and `evalR` belong to
`def-sp-semilinear-constant-ring-operations`; `gamma` belongs to
`def-coef-semilinear-proper-open-mate`; the open adjunction belongs to
`def-sf-semilinear-proper-open-comparisons`. All remain cited. The scalar-restriction
functor is now cited through Q98's landed
`def-pur-proetale-module-scalar-restriction`, whose existing:true declaration is
`AlgebraicGeometry.Scheme.proEtaleModuleRestriction` in
`Sheaf.Paper.ProEtaleConstantModuleEncoding`.

The new owner described below covers `evalJInv`, its invertibility certificate,
`evalJ`, `evalSource`, and `evalTarget`, exactly as the return requests. It cites
`def-cbc-strict-tower-open-extension` for `StrictTower.J` and `StrictTower.jAdj`.
The Lean module remains byte-identical to the returned packet; neither helper
isomorphism nor the theorem signature nor its sorry proof is changed. The current
main item's original statement/proof/dependencies are preserved, with changes only
to `lean` and additional definition `stmt_deps`. No statement_change is needed.
The wrapper rebuilds the delivery on current main.

The maintainer's accepted mathematical checks continue to apply: every field and
geometric hypothesis, per-level cohomology bounds, exact mate hom, inverse
naturality, and finite normalization for every same-ring/id-scalar origin witness
are unchanged. The finite clause intentionally specializes the existing
`gamma_finite` equality. The inherited `lem-cbc` statement dependency continues
to supply the StrictTower finite comparison interface. Empty schemes/opens, the
first quotient, identity verticals, Cartesian and non-Cartesian squares, and
bounds drifting with n remain allowed.

## New nodes

`def-pur-semilinear-evaluation-comparisons` registers the existing open-unit-normalized
evaluation comparison and the two composite source/target comparisons in
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`, with existing:true and no new
Lean file. Its primary signature is exactly `def evalJ` at source line 2442;
its declarations list includes `evalJInv`, `evalJInv_isIso`, `evalJ`, `evalSource`,
and `evalTarget`. The two composites at lines 2536 and 2548 use the given `evalJ`
and `asIso evalR`, retaining their directions and order. The reverse mate at
line 2416 uses the given system and constant-tower open adjunctions. The already
proved invertibility certificate at line 2425 is only recorded, not restated.
Sources read: Stacks 03DI (`sites-modules.tex`, lemma-extension-by-zero) for the
open adjunction and its section formula, and 0F7B (`more-etale.tex`,
lemma-shriek-proper-and-open) for the proper/open comparison to which these
normalizations apply; the system realization is explicitly the blueprint
ancestor's old Steps 3–4, not a quoted Stacks system theorem.

The new definition has arbitrary schemes, arbitrary coefficient transition maps,
and any level n. In particular it adds no properness, finiteness, flatness,
quasi-compactness, boundedness, etale-origin or Cartesian hypothesis. Its formulas
match the two concrete Lean composites and the inverse open-adjunction mate.
The coefficient and site universes are unchanged. Identity and empty open cases,
zero objects, and n=0 require no separate choices. No new assertion of mate
invertibility or pasting is introduced.

Fresh searches for this owner were actually run on 2026-10-24 and are recorded in
its mathlib_searches: LeanSearch with "canonical evaluation comparison extension
by zero derived semilinear coefficient systems proper direct image" returned
8 function/polynomial/continuous-map results; LeanFinder with "adjunction mate
evaluation extension by zero semilinear derived systems canonical source target
comparison" returned 8 linear-map extension results; Mathlib CategoryTheory grep
for `evalJInv|evalSource|evalTarget` returned 0. Project grep found the five exact
published declarations, with other hits either their consumers or VaryingRing's
distinct operations. A scan of all live definition-node records found no owner of
these SemilinearProperOpen declarations; Q25's suggested owner is not landed.
`blueprint_refs.py search 'semilinear evaluation comparisons'` returned 0 nodes;
`ancestor` returned `prop-pur-adic-reconstruction-trace-coherence`. These findings
justify definition ownership with existing:true, not duplicate declarations.

## Repair self-check by Q78

Compared the repaired packet against current main using JSON field comparisons:
only the item's lean and stmt_deps differ. All original stmt_deps remain; the two
unwanted added theorem ids are absent, and both required definition ids occur.
Read the new owner's five full declarations, their docstrings and concrete bodies,
and the four dependency definition records. The exact `evalJ` signature is copied
verbatim and all direct owner dependencies exist. A recursive read-only scan of
11,778 locally available dependency records found no path back to this item; ten
inherited transitive ids were unavailable locally, so the authoritative server
preflight performs the delivery check.
This is a worker self-check; the independent mathematical reading is the
maintainer's return above. No additional reviewer agent was started.


Repair validation: the explicit scompile.py check passed both the sandbox module
(46.5 s) and its library-path form (57.1 s), with no errors or unexpected warnings.
The stored theorem signature and the new owner's existing evalJ signature both
match the source verbatim. The Lean file SHA256 remains
`2e7288f3990c6da099199921e19395c2fdb2ffde81361bfd58e7cb36a9f1b50a`.

The first repaired dry run requested the current schema field `import_flags`;
added `import_flags: []` to the new definition node and reran the dry run.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
