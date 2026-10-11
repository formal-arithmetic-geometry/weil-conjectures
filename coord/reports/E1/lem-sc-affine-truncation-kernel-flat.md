## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AffineTruncationKernelFlat.lean` states
`AlgebraicGeometry.affine_truncation_kernel_flat`, with its only proof `sorry`.
It defines no new notions. The statement assumes Tor amplitude only after restriction
to `U`, not on all of `Spec A`.

Hypothesis and clause correspondence:

- `A : Type u`, `[CommRing A]`, and `Spec (.of A)` render the affine scheme
  `X = Spec(A)`. No nonzero-ring or Noetherian hypothesis is imposed.
- `U : (Spec (.of A)).Opens` supplies the open subscheme, with `U.toScheme` its scheme;
  `hU : IsCompact (U : Set (Spec (.of A)))` renders quasi-compactness.
- `P : CochainComplex (ModuleCat.{u} A) ℤ` is the given cochain complex.
  `hP : ∃ n, ∀ i, n < i → IsZero (P.X i)` is boundedness above of the actual terms,
  rather than just of cohomology. `hfree` asserts `Module.Free A (P.X i)` and
  `Module.Finite A (P.X i)` for every degree, exactly finite free terms.
- The associated sheaf complex is the explicit `Functor.mapHomologicalComplex` of
  `tilde.functor (.of A)`, followed by `DerivedCategory.Q.obj`. Restriction to `U`
  is the shared composite `SheafOfModules.overFunctor ... U ⋙
  Equivalence.functor (Scheme.Modules.overEquiv U)`, with both categories named.
  Its `mapDerivedCategory.obj` is the corresponding object on `U`; no independent
  object or arbitrary comparison map substitutes for the associated complex.
- The two `HasDerivedCategory` instance binders specify the shared localizations
  of module sheaves on `X` and `U`. They impose no geometric hypothesis.
- `a b : ℤ` are the amplitude endpoints. `hamp` tests every module sheaf `G` on
  `U.toScheme` and every degree `i` outside the interval (`i < a ∨ b < i`), using
  the existing `schemeDerivedTensorCohomologyVanishes`. This is precisely sheaf Tor
  amplitude. No ordering hypothesis on the endpoints was added; an empty interval
  is allowed. The affine criterion can be applied with upper bound `max a b` in
  that case without changing the lower bound used by the proof.
- `r : ℤ`, `hr : r < a` render the chosen lower truncation degree.
  `LinearMap.range (P.d (r - 1) r).hom` is exactly `K = Im(P^(r-1) → P^r)`.
  `LocalizedModule.Away f` of this image is `K_f`, over `Localization.Away f = A_f`.
  In particular no equality with the kernel of the next differential on all of
  `Spec A` is asserted.
- The conclusion quantifies over every `f : A` with `PrimeSpectrum.basicOpen f ≤ U`,
  exactly `D(f) ⊆ U`. It asserts the conjunction of `Module.Flat (Localization.Away f)`
  and `Module.FinitePresentation (Localization.Away f)` of that same localized image.
  The parenthetical sheaf formulation in the node is the equivalent interpretation
  on the principal-open basis, rather than an extra conclusion with different objects.

Dependency declarations inspected:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  with their full definitions and docstrings, supply schemes and their morphisms.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsStrictlyPerfect`, `Scheme.IsPerfect`,
  and `Scheme.perfectSubcategory` were read. The node's citation is contextual:
  it assumes a bounded-above finite-free complex, not a bounded strictly perfect
  complex or the additional predicate `Scheme.IsPerfect`. Accordingly those predicates
  are not imposed. Mathlib's module freeness and finiteness give the terms directly.
- `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion`:
  `AlgebraicGeometry.affine_torAmplitude_iff` was read, including its termwise tilde
  construction, all-module-sheaf vanishing test, and module Tor-amplitude side.
  The same associated-sheaf construction and vanishing predicate are used here;
  the theorem is cited in the proof docstring for the restriction to each `D(f)`.
- The landed node `def-pc-derived-tensor-cohomology-vanishes` was added to `stmt_deps`
  because its recorded `AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes`
  (`Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes`) occurs directly in the
  signature. Its K-flat-representative definition was read; it is reused unchanged.
- The restriction uses the existing `moduleOverFunctor_*` instances from
  `Sheaf.Paper.DerivedHomMayerVietoris`. Exactness of the composite and its additivity
  are supplied explicitly by existing Mathlib theorems, with no file-local instances,
  new assumptions, or restated definitions.

Edge cases: the zero ring/empty affine scheme and empty `U` are admitted. For empty
`U`, admissible principal opens are empty, not necessarily absent (for example `f = 0`);
then the localized ring and module are zero. Nilpotent `f` is also allowed. `U = ⊤`
recovers the global affine case. Zero complexes and terms, arbitrary negative `r`,
`a = b`, and `a > b` are admitted. There is no boundedness-below, fixed rank,
nonempty-open, perfectness, or Noetherian assumption.

Searches actually made, recorded in `searches.jsonl`:

- LeanFinder: "localization of image differential bounded above finite free complex
  Tor amplitude is flat finitely presented". Eight results: generic Tor vanishing,
  derived t-structure support, and local flatness declarations; none is this theorem.
- Loogle: `Module.Flat, Module.FinitePresentation`. Six results, including projectivity
  of finitely presented flat modules and base change; none states truncation-image flatness.
- Mathlib grep through `msearch.py`: `truncation.*flat|flat.*truncation|last.one.flat`.
  Zero hits.
- LeanSearch: "image differential finite free cochain complex flat finite presentation
  Tor amplitude". Service unavailable (Internal Server Error), recorded as unavailable;
  no result or successful negative verdict is claimed for this search.
- `rg` in `WeilConjectures` and project `lean/Sheaf` for the truncation-flat patterns
  and the item id: only generic flat-model/last-one-flat ingredients, not this theorem.
  The module-flat-opcycles criterion and finite-locally-free parent are different nodes.
- Declaration-name/id search in `dag/lean_names_upstream.json` and `WeilConjectures`:
  no existing `affine_truncation_kernel_flat` or exact item-tagged declaration.

Source fault: the node cites Tag 08ED, which is the essential-surjectivity lemma,
not the truncation argument. The specified paragraph is in
[Stacks Tag 08EG](https://stacks.math.columbia.edu/tag/08EG), Lemma 36.13.6,
`perfect.tex`, `lemma-lift-perfect-complex-plus-locally-free`, proof.
The source paragraph and the corresponding TeX were read. The module cites the
correct place. The node's `source` is unchanged because it is outside this worker's
permitted fields; this is a reference error, not a mathematical statement correction.

The initial scratch draft incorrectly assumed global module Tor amplitude; it was
replaced by the stated sheaf Tor amplitude on `U` before this handoff. The initial
scratch files mistakenly placed in the read-only clone were removed. All delivery
files are in the designated sandbox. No independent second-reading section was
written: the second reader is responsible for it.

Validation: server single-file compile is clean, with all variables and universes
explicit and every theorem proof `sorry`. The required dry run is the final check.

## Second reading by E1

I reread the node statement against `AffineTruncationKernelFlat.lean`, item by item. The
affine object is rendered by `A : Type u`, `[CommRing A]`, and `Spec (.of A)`, with no
nonzero, Noetherian, or field assumption. The open subscheme and quasi-compactness are
`U : (Spec (.of A)).Opens` and `hU : IsCompact (U : Set (Spec (.of A)))`. The complex is
`P : CochainComplex (ModuleCat.{u} A)`; `hP` is bounded-above termwise vanishing and
`hfree` gives `Module.Free` and `Module.Finite` in every degree, hence the stated finite
free terms. The two `HasDerivedCategory` binders provide the module-sheaf derived
categories on `Spec A` and `U`. The associated complex in `hamp` is the explicit
`Functor.mapHomologicalComplex` of `tilde.functor (.of A)`, then `DerivedCategory.Q`,
restricted by `SheafOfModules.overFunctor` followed by the named `Scheme.Modules.overEquiv`.
The amplitude hypothesis is exactly vanishing of `schemeDerivedTensorCohomologyVanishes`
for every sheaf `G` and every `i` with `i < a ∨ b < i`; no ordering of `a,b` is added.
The lower degree is `r : ℤ` with `hr : r < a`, and
`LinearMap.range (P.d (r - 1) r).hom` is precisely `K = Im(P^(r-1) → P^r)`. Finally,
the conclusion quantifies over every `f : A` with `PrimeSpectrum.basicOpen f ≤ U` and
states both `Module.Flat (Localization.Away f) (...)` and
`Module.FinitePresentation (Localization.Away f) (...)` for the localized image. All
objects, hypotheses, quantifier order, and both conclusion clauses match the node.

Edge cases checked: zero ring and empty affine scheme, empty `U` (including `f = 0`),
nilpotent `f`, `U = ⊤`, zero complex or terms, negative `r`, `a = b`, `a > b`, and all
characteristics are admitted. Universes are shared through `u` for the ring/modules and
independent derived-category universe parameters only for the required instances.

I repeated the existing-definition searches (LeanFinder/Loogle, grep of Mathlib,
`WeilConjectures`, and project `lean/Sheaf`, with the queries recorded in
`searches.jsonl`). No declaration states this truncation-image theorem; the recorded
dependency declarations are the ones used in the signature. The node source says Tag
08ED, while the paragraph is actually in Tag 08EG, as the worker report records; this is
a node metadata/reference fault outside the permitted `lean` field, and the mathematical
statement is unchanged. I found no mismatch in the Lean and made no code or node-statement
changes.
