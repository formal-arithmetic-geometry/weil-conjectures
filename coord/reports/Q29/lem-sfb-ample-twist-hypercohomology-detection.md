## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleTwistHypercohomologyDetection` states
`AlgebraicGeometry.exists_nonzero_hypercohomology_ample_twist`, with `sorry` as its
whole proof. The source read is Stacks Project, perfect.tex, Tag 0BQR,
`lemma-nonzero-some-cohomology`, including its complete proof (lines 4068–4106).
There is no statement correction, new definition, or dependency repair.

The inherited BLOCKED ending concerned Q65's completed stage-1 split. I read the
current node, the Q65 report and ledger, and queue.tsv. Q65's report explicitly
says no Lean was written; the live item has no lean or reviewed_lean record and
is queued for stage 2. No released repair note exists. This delivery preserves
the entire accepted stage-1 split and changes only `lean`.

Hypotheses and clauses, checked against the node:

- A scheme X is `(X : Scheme.{u})`.
- The invertible O_X-module is `(L : X.Modules) [L.IsInvertible]`. This is the
  recorded locally free rank-one definition, not a replacement definition.
- Ampleness is `(hL : Scheme.Modules.IsAmple X L)`. It includes quasi-compactness
  and the affine nonvanishing-locus cover; no additional separatedness,
  noetherian, finite-type or quasi-compactness hypothesis is added.
- K in D_QCoh(O_X) is `(K : schemeDerivedCategory X)` and
  `(hK : schemeDerivedQCohProperty X K)`: all integer cohomology sheaves are
  quasi-coherent. No boundedness hypothesis or truncation is present.
- K not isomorphic to zero is `(hne : ¬ IsZero K)` in the shared derived category.
- Existence of an integer m >= 0 is `∃ m : ℕ`. Naturals encode precisely the
  permitted nonnegative exponents, including zero. The exponent is not required
  to be strictly positive.
- The degree p is `(p : ℤ)`, including negative degrees.
- The ordinary power is `L.tensorPow m`; `DerivedCategory.singleFunctor ... 0`
  places that very module in degree zero in the shared O_X-module carrier.
- `K ⊗ (DerivedCategory.singleFunctor ... 0).obj (L.tensorPow m)` uses the
  imported global `schemeDerivedTensorMonoidal` instance: the canonical K-flat
  derived tensor, with no arbitrary monoidal structure parameter.
- RΓ(X,E) is exactly `(schemeDerivedGlobalSections X).obj E` from the recorded
  global-derived-Hom dependency. Its values are in D(A), A = O_X(X).
- H^p is `(DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj ...` and
  nonvanishing is `¬ IsZero` of that A-module. This is also nonvanishing of its
  underlying abelian group.
- The explicit `HasDerivedCategory.{w}` and `HasDerivedCategory.{wA}` binders
  are the shared localization size choices required by these definitions, not
  additional geometric hypotheses. Their hom universes remain independent.
  Every universe and variable is explicitly bound; `autoImplicit` is false.

Recorded statement dependencies used, with signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, locally affine
  locally ringed spaces, and their morphisms.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and `.tensorPow` (including
  its zero/successor definitions).
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` and `.schemeDerivedQCohProperty`.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `AlgebraicGeometry.schemeDerivedTensorMonoidal`, the global instance.
- `WeilConjectures.AlgebraicGeometry.GlobalDerivedHom`:
  `AlgebraicGeometry.schemeDerivedGlobalSections`, its K-injective-resolution
  comparison, and the recorded `schemeGlobalDerivedHom` definition.

Mathlib's `DerivedCategory.singleFunctor` and `.homologyFunctor` signatures and
docstrings were read in Basic.lean and HomologySequence.lean. The former is the
single in the stated integer degree, and the latter the descended cohomology
functor. No helper declaration is needed.

Every already stated proof dependency is imported without `public` unless
already publicly imported as a statement dependency: AmpleSeparated,
DerivedCategory.Basic, PresheafModuleStalkFunctor, Modules.QuasicoherentKernel,
Modules.QuasiCoherentCokernelImage, Mathlib Modules.Tilde,
SectionClearingDenominatorsQCQS, SectionRestrictionSTorsion,
KFlatIndependentCoefficients, ModuleStalkExact and
RingedSiteKInjectiveResolutionsOfUniverses. The dependency
`lem-sfb-qc-separated-quasicoherent-complex-model` is a proof-only prerequisite
with no recorded module yet, so there is no import to add for it. Its mathematical
role is retained explicitly in the theorem's six-step proof docstring. It is
not needed to type this statement and is not added as a statement dependency.

Edge cases checked before writing:

- Empty X: its module/derived category is zero, so the nonzero-K premise excludes
  the case without a Nonempty assumption on the scheme.
- K = 0: excluded by precisely `hne`, with no hidden nonzero coefficient premise.
- m = 0: `L.tensorPow 0` is the structure-sheaf unit. It is allowed, as in 0BQR.
- On an affine scheme with L = O_X, a nonzero module in any integer degree is
  detected with m = 0 in that degree; negative degrees are not excluded.
- Arbitrarily unbounded complexes remain admitted by `schemeDerivedCategory`;
  no spectral-sequence convergence or cohomological bound is assumed.
- Arbitrary characteristic and nonnoetherian base rings are admitted.

Searches actually made in this session:

- msearch.py LeanFinder: “A nonzero unbounded derived complex with quasi coherent
  cohomology has nonzero hypercohomology after some positive power of an ample
  invertible sheaf”. Eight hits: derived t-structure IsGE/IsLE criteria and Q
  preservation; none involves ampleness or detection by twists.
- msearch.py Loogle: `"IsAmple", "cohomology"`: zero hits.
- msearch.py grep: `ample.*cohomolog|cohomolog.*ample|nonzero_some_cohomology`:
  two unrelated comment hits, ComplexShape.lean and GroupWithZero/Action/Defs.lean.
- msearch.py LeanSearch: “Ample positive tensor twists detect nonzero unbounded
  quasi coherent derived complexes”. Eight hits on derived localizations,
  factorization and quasicoherent-data constructors; no detection theorem.
- rg over both lean/WeilConjectures and lean/Sheaf using
  `ample.*cohomolog|cohomolog.*ample|ample.*detect|nonzero_some_cohomology`
  and this node's id: nearby CoherentSerreVanishing requires coherent sheaves
  and large twists, so is different; ProjectiveNegativeTwistsGenerator refers
  to this result only in its proof docstring and states a finite projective-space
  weak-generator theorem. No declaration already states this item.

Validation: scompile.py compiled this module both as a sandbox module and at its
library module path, each separately within the 60-second limit, with no errors
or warnings. The first parse failure was repaired by opening the shared tensor
notation namespace; the final file contains no diagnostic commands.

No STATEMENT-DISPUTED finding or source error.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
