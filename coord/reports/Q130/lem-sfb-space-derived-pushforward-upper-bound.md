## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDerivedPushforwardUpperBound` states
`AlgebraicGeometry.AlgebraicSpace.derivedDirectImage_uniform_upper_bound`.
Its sole proof is `by sorry`; no definition or supporting theorem is introduced.
The node's mathematical statement and proof plan are unchanged.

Sources read: `literature/stacks-project/spaces-perfect.tex`,
`lemma-quasi-coherence-direct-image` (Tag 08FA), statement and proof of (2),
and `lemma-application-nice-K-injective` (Tag 08F7), especially (3).
08FA gives the endpoint-zero assertion; 08F7(3) gives the stated general
upper endpoint b. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read for context. This is an auxiliary node, not that unit's statement.
No source correction or STATEMENT-DISPUTED issue was found.

Hypotheses and clauses, in the order of the node:

- Fixed universes: explicit `universe u w`, `S : Scheme.{u}`, and
  `[HasDerivedCategory.{w} X.SmallModules]`,
  `[HasDerivedCategory.{w} Y.SmallModules]`. The existing small affine site has
  objects and arrows in u, coefficients and module sections in u. The derived
  localization size w is explicit and common, as in the existing derived-direct-image
  definition; it is not identified with u. These are the chosen localizations of
  the size convention, not extra geometric hypotheses.
- A scheme S and algebraic spaces X,Y over S: `{S : Scheme.{u}}`
  and `{X Y : AlgebraicSpace S}`. A morphism is `(f : X ⟶ Y)` in the full
  subcategory of fppf sheaves, retaining arbitrary algebraic-space morphisms.
- The small etale structure sheaves and module categories are those already
  constructed by `AlgebraicSpace.structureSheaf` and `Modules`.
  `SmallModules` is their restriction to the small affine model and is equivalent
  via `smallModuleEquivalence`. This is the same ringed topos and the same module
  universe, not a different coefficient category.
- Quasi-compactness of f: `hqc : IsQuasiCompactPresheafMap f.hom.hom`.
  Its definition quantifies over every affine scheme test over Y and requires a
  surjective etale quasi-compact scheme atlas of the pullback. This is precisely
  quasi-compactness of that algebraic-space source.
- Quasi-separatedness of f:
  `hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)`.
  This is the relative diagonal, rather than the absolute diagonal of X or Y.
- Quasi-compactness of Y: `hY : CompactSpace (Point Y.obj.obj)`.
  `pointTopologicalSpace` is the existing final topology on field-valued point
  classes, which is the usual topology of an algebraic space.
- Unbounded derived objects: `(E : X.DerivedModules)` is an object in the
  localization of all cochain complexes of module sheaves, not D(QCoh(X)).
- Quasi-coherent cohomology: `X.derivedQCohProperty E` says, for every integer n,
  that the inverse small-model equivalence applied to H^n(E) satisfies Mathlib's
  `SheafOfModules.IsQuasicoherent`. It places no condition on the terms of a
  representative complex.
- Canonical K-injective direct image: `(derivedDirectImage f).obj E` is the
  existing `smallModuleDirectImage f`'s `rightDerivedFunctor`.
  The ordinary functor is the original `moduleDirectImage f` conjugated by the
  restriction equivalences, so it retains its specified chart-limit normalization.
  `smallModules_hasKInjectiveResolutions` supplies K-injectives, and the upstream
  right-derived-functor construction uses the K-injective derivability structure.
  No arbitrary functor, comparison, or resolution is a hypothesis.
- Uniform positive integer: `∃ N : ℤ, 1 ≤ N ∧ ...` precedes both b and E.
  Thus one N works for every b and every E for the fixed f.
- Every integer upper endpoint: `∀ (b : ℤ) (E : X.DerivedModules), ...`.
- H^q(E)=0 for q>b:
  `∀ q : ℤ, b < q → IsZero ((DerivedCategory.homologyFunctor X.SmallModules q).obj E)`.
- H^m(Rf_*E)=0 for m>=b+N: the final `∀ m : ℤ, b + N ≤ m → IsZero ...`
  uses the target module category's homology functor on the canonical image.
- No lower bound and no Noetherian hypothesis: neither is a binder or implicit
  instance in this theorem. There is also no separatedness or representability
  requirement on f.

Dependency declarations used, with source modules inspected:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `structureSheaf`,
  `Modules` (via its public dependency chain).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; cohomology is `DerivedCategory.homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the slice
  sheafification instances and `QCoh`, using Mathlib's `IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImageModel`, `moduleDirectImage`.
  Its complete section-limit property, projection naturality, and uniqueness
  were read before using its derived extension.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `smallModuleDirectImage`,
  `smallModules_hasKInjectiveResolutions`, and `derivedDirectImage`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `IsQuasiCompactPresheafMap` and `diagonalPresheafMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `pointTopologicalSpace` on the existing `Point` classes.

The owning DAG nodes are added to stmt_deps as already-landed
interfaces: `def-sfb-space-derived-module-calculus`,
`def-sfb-space-quasi-compact-presheaf-map`,
`def-sfb-presheaf-map-separated-diagonal`, and `def-a1-space-point-topology`.
This is the allowed addition of landed statement dependencies; no existing notion
is redefined and no dependency record needs repair.

Stated proof dependencies are plain imports:
`SpaceCotangentRingMap` (the current recorded enlarged-site interface),
`SpaceChartLimitEnlargedSections`, `Sites.UnboundedLeraySections`, and
`RingedSiteKInjectiveResolutionsOfUniverses`. The two presently unstated
space uniform-chart/functor-bound proof prerequisites have no modules to import.
The four-step natural-language proof in the theorem docstring preserves the node's
uniform affine-chart bound, unbounded functor argument, derived Leray comparison,
and local cycle/boundary detection.

Edge cases checked mathematically before drafting: empty X or Y and E=0 give
zero cohomology and permit N=1; no nonemptiness is assumed. For identity f,
N=1 gives exactly vanishing in degrees m>b. For E=M[-b], its cohomology is in
 degree b and the conclusion is the higher-direct-image bound in degrees >=N.
Negative and positive b are allowed because b is an integer. Objects extending
arbitrarily far below b are quantified over unchanged. Neither finite type,
Noetherianity, separatedness of the spaces, nor representability of f is inferred
or assumed. The endpoint is inclusive at b+N, equivalently strict above b+N-1.

Searches actually run with msearch.py (group Q130, this item):

- LeanSearch: "Derived pushforward for a quasi compact quasi separated algebraic
  space morphism has a uniform upper bound on quasi coherent cohomology".
  Eight hits, including scheme-module ordinary pushforward section formulas and
  scheme separatedness implying quasi-separatedness; none states this theorem.
- LeanFinder: "For a quasi compact quasi separated morphism of algebraic spaces
  with quasi compact target derived pushforward has a uniform upper cohomological
  bound on complexes with quasi coherent cohomology". Eight scheme qc/qs property
  hits, including `QuasiCompact.of_comp` and base-change stability; no match.
- Loogle: `"rightDerivedFunctor", "IsLE"`. Three generic right-derived/Kan-extension
  hits; none is this algebraic-space uniform bound.
- Mathlib grep: `cohomological.?dimension|upper.*bound|rightDerived.*IsLE`
  in `Algebra/Homology`. Only `Embedding/Boundary.lean`'s unrelated embedding
  upper-boundary definition was returned.
- Local rg of upstream WeilConjectures and project Sheaf sources for the item id,
  upper-bound variants, and derived-direct-image bound names found no exact
  statement. The upstream `DerivedDirectImageUniformTruncationBound` and
  `UnboundedDerivedFunctorCohomologicalBound` were inspected: their signatures
  concern schemes, not arbitrary algebraic spaces, so they cannot be attached as
  an existing declaration of this item. The DAG upstream-name index has no item hit.

Validation: the prescribed scompile.py compiled both the sandbox module and its
library module path cleanly (3.9 s and 1.6 s). All variables and both universes
are explicitly bound; `autoImplicit` is false. Maximum line length is 92.

## Repair of returned delivery 8ce5d2ab9bb4

H2: Replaced `lem-trf-space-qc-separated-etale-local` in stmt_deps with
`def-sfb-space-quasi-compact-presheaf-map` (Q97) and
`def-sfb-presheaf-map-separated-diagonal` (Q32). Their landed lean records
own precisely `IsQuasiCompactPresheafMap` and `diagonalPresheafMap`, respectively.
The source definitions at lines 38 and 49 of
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal` were read again: they supply the
plain affine-test atlas predicate and canonical relative diagonal. The etale-local
theorem is not used by the statement. Its module import remains correct because
both definition records name that same module.

Compared with the returned packet, only this dependency substitution and the
report are changed. Compared with current main, the retained node statement and
proof fields agree; the additions to stmt_deps name the actual landed interfaces.
The Lean module, theorem signature, proof docstring, sorry body, and lean record
are unchanged, exactly as the return requests. No dependency node is edited.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
