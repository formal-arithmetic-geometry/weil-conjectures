## Worker report

The module `Sheaf.SecTraceFormula.TwoTermNormalizationLocalityEquivariance` states
all clauses of `lem-trf-two-term-normalization-locality-equivariance` in four theorems.
All theorem proofs are `sorry`; the helper definitions contain real data and no sorry.
The node statement and all dependency records are unchanged.

### Hypotheses and clauses

- `R : Type u`, `[CommRing R]` is the arbitrary commutative coefficient ring.
  The independent universe `v` of modules is preserved. Localized models have an independent universe `w`, and the
  coefficient ring `A` satisfies `[IsLocalization p.primeCompl A]`; no smallness or equality of universes
  is imposed. The usual fraction model fits by choosing `w = max u v`.
- A two-term cochain complex is the recorded `Arrow (ModuleCat R)` encoding:
  `left` is degree minus one, `right` is degree zero and `hom` is its differential.
  The eight finite/projective instances are exactly the assumptions on the four terms.
  `TwoTerm.determinant` is precisely det(E^0) tensor Dual(det(E^-1)).
- `DegreewiseSurjective a` and `QuasiIso a` are the recorded dependency predicates,
  with bijectivity on H^-1 and bijectivity modulo boundaries on H^0.
- `Normalization a` just packages the already characterized maps: `gammaNeg` and
  `gammaZero` satisfy `IsDeterminantExactSequenceMap`; `assembly`, `element`, `inverse`
  satisfy the recorded `IsKernelNormalizedAssembly`. Uniqueness in the dependency
  pins the two gamma maps, so they are the common maps used by that predicate.
  A normalization is supplied as a named choice of the existing construction, not an
  extra mathematical restriction on a. No arbitrary map replaces a canonical map.
- Localized models `Pp`, `Qp`, with coefficient ring `A` satisfying `[IsLocalization p.primeCompl A]`,
  have explicit compatible restricted R-actions. The ring localization is a model of `R_p`, exactly as in the dependency
  localization theorem, and includes `A = Localization.AtPrime p`. The four localization maps `fPn`,
  `fPz`, `fQn`, `fQz` satisfy the existing `IsLocalizedModule` universal property.
  The equations `hP`, `hQ`, `hn`, `hz` state exactly that the differentials and
  `ap` are the localized maps. These are representation data for the named
  localizations, not extra restrictions: fractions supply such data for every prime.
  The conclusion holds for every representation, as does the dependency
  `Module.determinantExactSequence_localization`.
- `determinant_line_localization` covers every finite-projective E, independently of a.
  `DeterminantLocalization` pins its determinant map on the exterior inclusion and
  requires `IsLocalizedModule`; its dual map is pinned by evaluation at every localized
  determinant vector. `LineLocalization.pure` pins the tensor map and its `localized`
  field asserts that it is a localization. These fields encode the canonical
  identification D(E_p) with D(E)_p, not just the existence of some isomorphism.
- `normalization_localization` quantifies over every ideal `p` with `[p.IsPrime]`.
  Its first two conjuncts assert the localized map is degreewise surjective and a
  quasi-isomorphism. Its next twelve conjuncts assert finite generation and freeness
  of P^-1_p, P^0_p, Q^-1_p, Q^0_p and the two localized kernel terms.
- The witnesses `kneg`, `kzero` have inclusion formulas n maps to fP(n) and satisfy
  `IsLocalizedModule p.primeCompl`; these canonically identify ker(a_p) with (ker a)_p.
  Their differential square also identifies the kernel complexes.
  Scalar actions on the kernels are induced by the explicitly supplied ambient
  R-actions and scalar towers; no new instance or scalar restriction is postulated.
- The witnesses `lP`, `lQ`, `lN` have the preceding canonical exterior/dual/tensor
  characterizations. With localized normalization `np`, the final five conjuncts are,
  respectively, localization of gamma^-1, gamma^0, Gamma, delta, and T. The equations
  on original elements specify the maps on every fraction by the localization
  universal property; preservation of an invertible denominator forces its inverse.
- `maps_eq_of_prime_localizations` has arbitrary modules M,N in independent universes,
  with no finite/projective hypotheses. Equality of `LocalizedModule.map` at every
  prime implies equality of the original linear maps. Mathlib already gives the
  underlying maximal-prime criterion (`LinearMap.eq_of_localization_maximal`);
  this is its every-prime formulation as the explicit clause of the present node.
- `normalization_equivariance` includes the same assumptions on a and a', finite
  projectivity for all eight terms, `uIso : P' ≅ P`, `vIso : Q' ≅ Q`, and the square
  `uIso.hom ≫ a = a' ≫ vIso.hom`, exactly au=va' in function order.
- `cneg`, `czero` are linear equivalences whose underlying vectors are the restrictions
  of u in the two degrees; the following equation is the kernel chain equation.
  `DeterminantIso.exterior` fixes all six induced determinant maps by exterior functoriality.
  `lineIso dneg dzero = TensorProduct.congr dzero.map dneg.map.symm.dualMap`
  is exactly D(w)=det(w^0) tensor (det(w^-1)^-1)^vee.
- The final five conjuncts of `normalization_equivariance` are the two degreewise gamma
  identities, D(c)delta'=delta, D(u)Gamma'=Gamma(D(v) tensor D(c)), and
  T_a D(u)=D(v) T_a'. Equations on all pure tensors assert equality of the full maps
  since pure tensors span. Ordinary tensor symmetry is used, with no Koszul sign.

### Dependency declarations read and used

- `Sheaf.SecTraceFormula.TwoTermDeterminantEncoding`: `Module.TwoTerm.determinant`,
  `kernelDeterminant`, `kernelDifferential`, `DegreewiseSurjective`, `QuasiIso`.
- `Sheaf.SecTraceFormula.TwoTermKernelNormalization`:
  `Module.IsKernelNormalizedAssembly`, `Module.two_term_kernel_normalization`.
- `Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence`:
  `Module.IsDeterminantExactSequenceMap`, `existsUnique_determinantExactSequence`,
  `determinantModule_localization`, `determinantExactSequence_localization`,
  `determinantModule_finite_projective` (full signatures and docstrings read).
- `Sheaf.LinearAlgebra.ProjectiveDeterminantModule`:
  `Module.determinantModule`, `ExteriorAlgebra.scalarExtensionMap`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, `mk`,
  `mkLinearMap`, `IsLocalizedModule`, `IsLocalizedModule.map` and its composition laws.
- `Mathlib.RingTheory.Localization.Module`: `LocalizedModule.map`,
  `IsLocalizedModule.mapExtendScalars`.
- Proof imports include the recorded finite standard free cover and the spectrum
  basic-open/unit-ideal criterion. `lem-trf-projective-determinant-chart-descent`
  has no Lean record or closed upstream audit in the read repository; its needed
  determinant localization interface is already public in the exact-sequence dependency,
  so there is no missing notion and no duplicate dependency module.

### Sources and edge cases

Read Stacks `more-algebra.tex`, section-determinants-complexes (0FJI),
lemma-det-ses-functorial (0FJC), and lemma-homotopic-surjections (0FJK), including the
first diagram and final localization paragraph. Also read the latest blueprint
`lem-trf-local-term-locality` proof to verify the recorded ancestry.

Checked: zero modules and empty wedges (the determinant is R); zero ring (all unital
modules vanish, so empty Spec does not defeat equality detection); nonconstant local
ranks; nontrivial invertible determinant lines; arbitrary characteristic including 2;
independent coefficient/module universes. Identity isomorphisms give identity transport;
no bases, trivialization or constant-rank hypothesis is added. The negative dual is the
dual of the inverse, so it has the required direction. The chain differential may be
noninjective and nonsurjective: only the acyclic kernel differential is invertible.
No statement correction or disputed statement.

### Searches

The sandbox `searches.jsonl` records the actual msearch runs:

- LeanFinder, “Kernel normalized determinant maps of two term finite projective complexes
  commute with prime localization and chain isomorphisms”: 8 results, led by
  `IsLocalizedModule.map_iso_commute` and projective-resolution naturality; no full match.
- LeanFinder, “Kernel normalized determinant line maps commute with prime localization
  and chain isomorphisms”: 8 results, including `LinearMap.toKerIsLocalized`,
  `toKerLocalized_isLocalizedModule`, `ker_localizedMap_eq_localized'_ker`.
  Read their signatures; they give kernel localization only, not the determinant result.
- LeanSearch, “Localization and equivariance of kernel normalized determinant maps for
  two term finite projective complexes”: 8 results, led by
  `LinearMap.localized'_ker_eq_ker_localizedMap`, categorical localization declarations
  and `LinearEquiv.det`; no full match.
- Loogle, `LocalizedModule.map, LinearEquiv, ExteriorAlgebra.map`: 0 results.
- Loogle, `"eq", "localization"`: 12 Ore-localization equality results, no full match.
- msearch grep, `det.*localiz|localiz.*det|det.*naturality`: 13 hits, scalar matrix
  determinant/localization norm statements and unrelated categorical localizations.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for determinant localization/equivariance and the item id: no declaration of the
  entire item; the existing socle, exact-sequence and kernel-normalization declarations
  above were reused. The exact id grep in upstream returned no matches.
- Direct Mathlib search found `LinearMap.eq_of_localization_maximal` in
  `Mathlib.RingTheory.LocalProperties.Submodule`, read in full; it underlies the
  arbitrary-module equality clause, rather than the determinant comparison clauses.

### Validation

Every compile uses the prescribed `scompile.py` wrapper with the default 60-second limit.
The successful default-limit compile and delivery dry-run are recorded below.

The final scompile.py invocation returned exit 0 with no errors or warnings in both
the sandbox check and final library module check. No timeout was raised.

`deliver2.py --no-push` returned OK: commit d7f87c70fae passed the server
preflight and compiled. The final module header also lists all four statements.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
