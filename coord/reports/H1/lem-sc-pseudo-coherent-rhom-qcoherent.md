## Worker report

The module `Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent` states
`AlgebraicGeometry.pseudoCoherentRHomQuasiCoherent`, with its sole proof `sorry`.
It introduces no definitions or auxiliary assertions. The item's JSON changes only in `lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme Y is `(Y : Scheme.{u})`; Noetherian is `[IsNoetherian Y]`, Mathlib's
  locally Noetherian plus quasi-compact scheme, not merely locally Noetherian.
- A is `(A : Y.CommAlgebraSheaf)`, the shared commutative sheaf-algebra carrier.
  Its quasi-coherence is `hA : A.toModule.IsQuasicoherent`.
- A as an underlying O_Y-module is `A.toModule`. Its pseudo-coherence hypothesis
  `hpc` uses `Scheme.IsPseudoCoherent Y` on `DerivedCategory.Q.obj` of
  `(HomologicalComplex.single ... (ComplexShape.up ℤ) 0).obj A.toModule`, namely A[0].
- K is `(K : schemeDerivedCategory Y)`. Its membership in D⁺_QCoh(Y) consists of
  `hK : schemeDerivedQCohProperty Y K` and `hbounded : ∃ a : ℤ, K.IsGE a`.
  Mathlib's canonical t-structure IsGE says all cohomology below a vanishes.
- The first conclusion is `sheafAlgebraDerivedQCohProperty Y A hA` applied to
  `(derivedRHomAlgebraModule Y A hA).obj K`. This is precisely membership in
  D⁺_QCoh(A), including a lower bound, for RHom with its natural algebra action.
- Forgetting the algebra action is the recorded exact
  `(SheafOfModules.restrictScalars ... A.hom).mapDerivedCategory`. The second
  conclusion applies `schemeDerivedQCohProperty Y` to its image of that same
  algebra-valued RHom object; the third conjunct asserts `∃ a : ℤ, ... .IsGE a`
  for the same image. Together these are its membership in D⁺_QCoh(Y).
- The HasDerivedCategory binders for Y, its localized opens, and A supply the
  localization structures required by the dependency definitions. Universes u, w,
  wA are explicit. They impose no geometric, finiteness, or boundedness hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, the locally
  ringed space with an affine neighbourhood of every point.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory` and
  `schemeDerivedQCohProperty` (unbounded localization and quasi-coherent cohomology).
- `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`: `Scheme.IsPseudoCoherent`
  (local bounded-above finite-free model, arbitrary degree-dependent finite ranks).
- `Sheaf.AlgebraicGeometry.DerivedCategoryQCoherentAlgebra`:
  `sheafAlgebraDerivedQCohProperty`, including both boundedness and quasi-coherence
  of the underlying O_Y-modules of cohomology. Imported through the RHom module.
- `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule`: `derivedRHomAlgebraModule`,
  termwise Hom(A,I(K)) with its first-argument algebra action descended through Q.
  Its `derivedRHomAlgebraModule_underlying` identifies the restriction-of-scalars
  image with `CategoryTheory.derivedInternalHom` from the recorded dependency
  `Sheaf.Algebra.Homology.DerivedInternalHom`, specialized to A[0]. I read the
  functor and comparison docstrings and full signatures; no second RHom is defined.

Edge cases checked before writing: empty Y (pseudo-coherence is vacuous locally
and both conclusions concern zero sheaves); A the zero algebra (Hom(0,K)=0);
K=0; arbitrary negative or positive lower bound; non-affine and disconnected
Noetherian schemes. No nonempty condition, separation assumption, finite dimension,
fixed finite-free rank, or fixed cohomological bound has been inserted. A is placed
in degree zero, not an arbitrary pseudo-coherent derived algebra. Noetherian is
essential for the finite-cover argument with local bounds; merely locally Noetherian
would not justify that proof for a general pseudo-coherent complex.

Source verification: the local Stacks checkout is absent on this machine, so I read
https://stacks.math.columbia.edu/tag/0A6H directly. Clause (1) gives quasi-coherence
and local boundedness on any scheme. Its affine computation and the finite affine
cover supplied by the node's Noetherian hypothesis yield exactly the node's global
boundedness conclusion. The source comments' unbounded-components counterexample
uses a non-quasi-compact scheme and a varying shifted complex; it does not satisfy
this node's hypotheses. No statement correction or STATEMENT-DISPUTED flag is needed.
The declaration docstring carries all three node proof steps and their dependencies.

Searches made with msearch.py (results also in searches.jsonl):

- LeanFinder: `derived internal Hom from a pseudo-coherent module preserves bounded
  below quasi-coherent cohomology`: eight generic sheaf cohomology / Grothendieck
  abelian / Abelian hits; none is this theorem.
- Loogle: `SheafOfModules.IsQuasicoherent, DerivedCategory`: zero hits.
- Mathlib grep: `pseudo.?coherent|derivedInternalHom|RHom` under AlgebraicGeometry:
  25 unrelated `congrHom`, `fiberHomeo`, and `asOverHom` hits; no theorem.
- LeanSearch: `Derived internal Hom from a pseudo coherent algebra preserves bounded
  below quasi coherent complexes`: service unavailable (Internal Server Error).
- Source rg: `pseudo.?[Cc]oherent|derivedInternalHom|derivedRHomAlgebraModule`
  in WeilConjectures: one explanatory pseudo-coherence comment in
  Cohomology/DirectImage/FiniteFreeComplex.lean, no matching statement.
- Source grep for the exact node id: no match.
- Project rg: `pseudo.*[Rr][Hh]om|rhom.*[Qq]|derivedRHomAlgebraModule`:
  found the shared definitions, affine RHom theorem, and supported RHom theorem.
  Read AffinePseudoCoherentRHomQuasiCoherent.lean and RHomSupportedQuasiCoherent.lean:
  the former is affine and representative-dependent; the latter states local bounds
  and support for general complexes, not the algebra-action/global-bound statement.
  No existing declaration says exactly this node's statement.

Validation: local lcompile could not load DerivedRHomAlgebraModule.olean (cache
not yet refreshed); scompile compiled this file cleanly in 8.4 seconds, no warnings.

## Second reading by H1

I independently opened the item node, its delivered module, all six statement dependency
nodes and their recorded declaration modules. There are no new nodes, dependency modules,
or statement corrections in this delivery.

Source reading: the local Stacks checkout is absent. I read the upstream `perfect.tex`,
`lemma-quasi-coherence-internal-hom` (Tag 0A6H), its proof, and the chapter's Conventions,
as well as https://stacks.math.columbia.edu/tag/0A6H. The conventions place a module in
degree zero. Clause (1) assumes only a scheme, a pseudo-coherent first argument and a
bounded-below quasi-coherent second argument; it concludes quasi-coherence and local
boundedness. The node specializes the first argument to A[0] and assumes Noetherian Y.
Its global bound follows from the finite open cover given by quasi-compactness. There is
no implicit separatedness, base field, or finite-dimensionality assumption to add.

Object/hypothesis/conclusion inventory, with the Lean match and verdict:

- Scheme Y: `(Y : Scheme.{u})`. Mathlib's Scheme is a locally ringed space locally
  isomorphic to spectra of commutative rings. Exact match.
- Noetherian Y: `[IsNoetherian Y]`. Its actual class extends `IsLocallyNoetherian Y`
  and `CompactSpace Y`; this is the node's Noetherian scheme. Exact match.
- Quasi-coherent O_Y-algebra A: `(A : Y.CommAlgebraSheaf)` and
  `(hA : A.toModule.IsQuasicoherent)`. CommAlgebraSheaf is `Under Y.sheaf`, and
  toModule restricts the rank-one A-module along the structure map. The commutative
  algebra convention agrees with both algebra dependency nodes. Exact match.
- Pseudo-coherence as an O_Y-module: `hpc : Scheme.IsPseudoCoherent Y
  (DerivedCategory.Q.obj ((HomologicalComplex.single ... (ComplexShape.up ℤ) 0).obj
  A.toModule))`. The opened definition quantifies over every point and a neighbourhood,
  a bounded-above complex, degree-dependent finite free ranks, and a derived isomorphism
  after restriction. The single functor places A in degree zero. Exact match.
- K in D⁺_QCoh(Y): `(K : schemeDerivedCategory Y)`,
  `(hK : schemeDerivedQCohProperty Y K)`, and `(hbounded : ∃ a : ℤ, K.IsGE a)`.
  The first predicate checks every cohomology sheaf. Mathlib's `DerivedCategory.isGE_iff`
  identifies IsGE with zero cohomology below a. Exact match, including quantifier order.
- RHom with its natural A-action: `(derivedRHomAlgebraModule Y A hA).obj K`.
  I read its termwise Hom construction, multiplication/precomposition action, canonical
  K-injective resolution, localization lift, and full underlying comparison signature.
  `derivedRHomAlgebraModule_underlying` compares its derived restriction of scalars to
  the dependency `derivedInternalHom` with first argument A[0]. Exact match.
- Membership in D⁺_QCoh(A): the first conjunct is `sheafAlgebraDerivedQCohProperty
  Y A hA` on that object. Its opened definition includes an existential cohomological
  lower bound and quasi-coherence after restricting each A-cohomology sheaf to O_Y.
  Exact match; despite its name it includes the plus condition.
- Membership after forgetting scalars in D⁺_QCoh(Y): the second conjunct is
  `schemeDerivedQCohProperty Y` on the exact `restrictScalars ... A.hom` derived image
  of the same object; the last conjunct is `∃ a : ℤ, ... .IsGE a` on that same image.
  Exact match; the two bounds need not be specified or chosen equal in the statement.
- Localization structures: the explicit HasDerivedCategory binders are precisely those
  used by the recorded definitions, including every localized open for pseudo-coherence.
  Universes u, w and wA are explicitly bound; they are localization/carrier choices,
  with no geometric or finiteness assumption hidden in them. No unbound variable found.

Edge cases: empty Y is allowed (local pseudo-coherence is vacuous and sheaves are zero);
A=0 and K=0 are allowed and RHom is zero. No positive-rank, nonempty-cover, or nonempty-
scheme binder appears. The integer bound may be zero, negative or positive. The finite-
cover minimum argument in the docstring needs the elementary empty-cover case separately,
which is harmless because every sheaf on the empty space is zero. Disconnected and
non-affine Noetherian schemes and every characteristic are included. No index set is a
parameter of this theorem; finite ranks in the dependency include rank zero. The scheme
universe is arbitrary and the module carriers use the established dependency convention.

Independent searches (queries/results also recorded by msearch):

- LeanFinder: `quasi coherent cohomology of derived sheaf Hom with finite presentation`:
  eight finite-presentation/quasi-coherence definition hits, no derived Hom theorem.
- Loogle: `IsQuasicoherent, IsGE`: rejected unknown short identifier. Retried with
  `SheafOfModules.IsQuasicoherent`: twelve generic quasi-coherence declarations, no match.
- LeanSearch: `derived sheaf Hom of a finite presentation algebra and a bounded below
  quasi coherent complex`: service unavailable (Internal Server Error); no verdict.
- rg with `pseudo.?coherent|derivedinternalhom|derivedrhomalgebramodule` (case insensitive)
  on upstream WeilConjectures: only the pseudo-coherence comment in
  Cohomology/DirectImage/FiniteFreeComplex.lean. The same conceptual search on Mathlib
  AlgebraicGeometry found no declaration. A broader RHom search also found upstream
  etale/constructible RHom material, which uses different coefficients and categories.
- Project search and signature reading: `AffinePseudoCoherentRHomQuasiCoherent.lean`
  supplies an affine representative computation; `RHomSupportedQuasiCoherent.lean`
  supplies local boundedness and support for general complexes. Neither supplies this
  global algebra-valued statement. Read `coord/upstream-overlaps.md`; no relevant overlap.

No mathematical mismatch found; the Lean and node record are retained verbatim. I changed
only this report by adding the independent reading. The declaration docstring follows all
three node proof steps with their cited dependencies. Its sole proof is `sorry`; there is
no definition, hollow data, auxiliary proved assertion, hidden let, or hidden show binder.
All four imports supply used notions; every line is at most 100 characters. The recorded
signature equals the module signature after the specified whitespace normalization.
Local lcompile succeeded in 8.8 seconds, exit code 0, without warnings. The delivery dry
run and final delivery run supply the required server compilation and mechanical checks.
