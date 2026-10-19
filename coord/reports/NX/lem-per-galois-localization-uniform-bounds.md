## Worker report

The module `Sheaf.Paper.GaloisLocalizationUniformBounds` states
`AlgebraicGeometry.Etale.galois_localization_uniform_bounds`, with one `sorry` and no
new definitions or auxiliary assertions. It follows ILO XVII 7.6.3--7.6.7,
printed pp. 311--313, read from the supplied PDF using pdftotext. The statement
retains the original node verbatim. Two definition nodes are added to stmt_deps to
separate the plain constructions from the theorem declarations that prove their
properties. The support node records the existing perEtaleSupportKernel,
perEtaleClosedSupport and perEtalePull definitions; the evaluation node records the
existing etaleEvaluationBiduality definition. The localization and locally-closed-
inheritance theorems remain proof-only dependencies.

Hypotheses and objects, clause by clause:

- Prime ell and Lambda=F_ell: `(ℓ : ℕ) [Fact ℓ.Prime]`, with the prime field represented
  by `ULift.{u + 1} (ZMod ℓ)` in its sheaf-value universe. The scalar algebra uses
  `[Algebra (ZMod ℓ) A]`; the lift changes size, not the coefficient ring.
- Noetherian scheme: `(X : Scheme.{u}) [IsNoetherian X]`.
- Commutative Noetherian Lambda-algebra: `(A : Type (u + 1)) [CommRing A]
  [IsNoetherianRing A] [Algebra (ZMod ℓ) A]`. This is the established coefficient
  universe for arbitrary small-etale module values, not a finite ring hypothesis.
- Small-etale module derived categories are the recorded `DerivedCategoryModule A X`,
  transparently `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`.
- `_hdual` asserts existence of a bounded constructible Q; for every bounded
  constructible M, derived Hom(M,Q) is bounded constructible and the canonical
  evaluation transpose is an isomorphism. The existing `etaleEvaluationBiduality` map first swaps D(M) and M
  by the signed derived tensor symmetry, evaluates M against D(M), then transposes
  under D(M) tensor - adjoint to Hom(D(M),-). No arbitrary biduality map is assumed.
- `(i : Z ⟶ X) [IsClosedImmersion i]`, `(j : U ⟶ X) [IsOpenImmersion j]`, and
  `_hij : Set.range i.base = (Set.range j.base)ᶜ` give exactly complementary immersions.
  No additional Noetherian assumptions on Z or U are needed (they follow from X).
- `Scheme.GaloisPartition` is the existing finite locally closed connected reduced
  stratification with connected Galois finite-etale covers. `P.modules A` uses
  filtered colimits of finite extensions of local systems trivialized on each cover,
  without finite generation. `P.boundedDerived A` requires all cohomology in that class
  and vanishing outside a finite interval. These are used directly, not copied.
- Constructibility uses `DerivedCategory.boundedConstructible (ModuleCat A) X`:
  the canonical bounded t-structure and `Scheme.IsConstructibleSheaf` on every
  cohomology sheaf. On a Noetherian scheme, locally closed strata are constructible,
  so the recorded upstream finite-constructible-stratification presentation is the
  node's finite locally closed presentation. Geometric stalk finiteness means
  finitely generated modules, not finite underlying sets. This applies to arbitrary A.

Conclusions, clause by clause:

- (1), class preservation: `∀ P : Scheme.GaloisPartition U, ∃ Q d, ∀ K, ...` sends
  `P.boundedDerived A K` to `Q.boundedDerived A (Rj_*K)`. Here Rj_* is
  `(lowerStar (ModuleCat A) j).rightDerivedFunctor`, the ordinary derived direct image;
  on the bounded inputs it agrees with its bounded-below specialization.
- (1), upper bounds: the same Q and `d : ℕ` work for all integers n, with
  `DerivedCategory.IsLE K n → DerivedCategory.IsLE (Rj_*K) (n + (d : ℤ))`.
- (1), constructibility: a separate universal clause sends every bounded constructible
  K on U to a bounded constructible image on X. It is not restricted by membership in
  a fixed partition class.
- (2), class preservation: `∀ P, ∃ PZ PU d, ∀ K, P.boundedDerived A K → ...` asserts
  both `PZ.boundedDerived A (Ri!K)` and `PU.boundedDerived A (j*K)`.
  Ri! is `(perEtaleClosedSupport A i j).rightDerivedFunctor`, with the actual sheaf
  kernel `kernel (upperStarLowerStarAdjunction (ModuleCat A) j).unit` followed by i*.
  The open restriction is `perEtalePull A j`, exactly the functor induced on derived
  categories by the exact inverse image.
- (2), upper bound for Ri!: the same `d : ℕ` works for all n and all K in the class.
- (2), every cohomological bound for j*: both `IsLE K n → IsLE (j*K) n` and
  `IsGE K n → IsGE (j*K) n`, for all integers n. Together these preserve arbitrary
  cohomological intervals and boundedness.
- (2), constructibility: a separate clause for every bounded constructible K asserts
  bounded constructibility of both Ri!K and j*K.
- Every output partition and bound is chosen before K and n. No invertibility of ell,
  excellence, finite-dimensional scheme, or finite generation in D^b_P is assumed.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
- Mathlib.AlgebraicGeometry.Noetherian: `AlgebraicGeometry.IsNoetherian`.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: `Etale.DerivedCategoryModule`,
  Mathlib `DerivedCategory.homologyFunctor`, and its standard boundedness predicates.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification:
  `Scheme.FiniteLocallyClosedStratification` (the parent of the Galois partition).
- Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules: its generic
  `SheafOfModules.IsLocallyConstantFiniteTypeModules` and publicly exposed upstream
  `Scheme.IsFiniteLocallyConstantSheaf`, `Scheme.IsConstructibleSheaf`. The latter
  is the exact small-etale ModuleCat presentation used by boundedConstructible.
- Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`, as used in the upstream stalk
  finite-generation interface.
- Mathlib.CategoryTheory.Limits.HasLimits and Filtered.Basic: `Cocone`, `IsColimit`,
  `IsFiltered`, as used in GaloisPartition.modules.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses: publicly exposes the ordinary
  `Etale.derivedHom` and `Etale.derivedTensorHomAdjunction` from
  WeilConjectures.SixFunctors.Etale.Derived.Hom, whose full definitions were read.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction` (the recorded definitions).
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `constantSheaf`, used by the partition
  constant-trivialization predicate `Sheaf.IsConstant`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules` was read;
  the item uses the dependency's documented six-functor ModuleCat-valued presentation.
- Added existing dependency def-per-galois-partition-modules, module
  Sheaf.Paper.GaloisPartitionModules: `Scheme.GaloisPartition`, `.modules`,
  `.FiniteExtensions`, `.boundedDerived`.
- Added definition node def-per-etale-support-functors, existing declarations in
  Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization:
  `Etale.perEtaleSupportKernel`, `Etale.perEtaleClosedSupport`, and
  `Etale.perEtalePull`. The theorem `Etale.perEtaleClosedSupport_additive` remains
  proof-only in lem-per-etale-internal-hom-localization.
- Added definition node def-per-etale-evaluation-biduality, the existing
  `Etale.etaleEvaluationBiduality` in Sheaf.Paper.DualizingLocallyClosedInheritance.
  Its body is the canonical transpose of signed evaluation. The theorem
  exists_dualizing_of_isImmersion remains proof-only.

Proof-only imports follow every stated proof dependency's recorded module, including
Mathlib matches. The finite tensor-generator lemma has no Lean declaration yet and is
therefore not imported; its proof step is still in the theorem's complete proof docstring.

Edge cases checked: X empty (empty partitions and the zero derived category); U empty
(Rj_* and j* zero, closed support the identity); Z empty (closed support zero, open
restriction an equivalence); either immersion an identity; zero complexes (all bounds);
nonreduced X or Z (only partition strata required reduced); ell equal to a residue
characteristic (no invertibility assumption); A the zero ring; arbitrarily generated
stalks in W_P; negative n, n=0, and d=0. Existential natural bounds include zero and
exclude no case. Finite filtrations in the imported class include length zero.

Searches for an existing statement:

- msearch leanfinder, query "Galois partition uniform bounds derived open direct image
  closed support dualizing complex": eight unrelated partition/support topology hits;
  no uniform Galois localization theorem. An earlier query "Uniform Galois partition
  bounds for derived open direct image and closed support under a dualizing complex"
  likewise returned unrelated compact/support lemmas.
- msearch loogle, query "DerivedCategory, IsNoetherian, IsClosedImmersion": no hits
  (IsClosedImmersion was unknown to that search index). Earlier query
  "AlgebraicGeometry.Etale, DerivedCategory": no hits.
- msearch grep, query "GaloisPartition|dualizing|upperShriek": generic duality and
  homology files, no statement matching this item. Earlier query
  "GaloisPartition|galois_partition|closedSupport": only LocallyFinsupp hits.
- rg of upstream WeilConjectures for GaloisPartition/galoisPartition and the exact node
  id: no matching theorem. rg of lean/Sheaf found the existing partition definition,
  tensor closure, exact refinement, and condition-(B) lemmas. The existing support
  and symmetry interfaces were found and reused. No new definition node is needed.
- Every search result is retained in searches.jsonl in the sandbox. The interrupted
  msearch process had completed; its persisted results were inspected before proceeding.

No statement fault or STATEMENT-DISPUTED finding.

## New nodes

`def-per-etale-support-functors` is an existing-definition record for the kernel of
the open restriction unit, its closed inverse image, and the termwise derived inverse
image. Its source is ILO XVII 7.6.10, p. 313; LeanFinder, Loogle, and grep searches
found no competing Mathlib or upstream declaration. It records the declarations in
Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization without introducing a module.
`def-per-etale-evaluation-biduality` is an existing-definition record for the canonical
evaluation transpose from ILO XVII Definition 0.8 and Proposition 7.6.3, p. 311.
The same three searches found no competing declaration; it records
Etale.etaleEvaluationBiduality in Sheaf.Paper.DualizingLocallyClosedInheritance.
Neither node records a theorem or a chosen isomorphism.

## Second reading by NX

The dispatcher explicitly prohibits starting another agent; the maintainer performs the
independent review of this delivery. This section records the worker's second pass with
both node and final signature open, and does not claim an independent worker review.
I matched the prime-field and Noetherian hypotheses, the actual evaluation-transpose
map, complementary immersions, both partition-class conclusions, both nonnegative
uniform upper bounds, both sides of the exact restriction bounds, and each of the three
unconditional bounded-constructibility conclusions. The conclusion quantifier order
keeps Q, PZ, PU and d independent of K. No mismatch required changing the node's statement.
The two added stmt_deps cite the definition nodes used directly by this module; the
localization and inheritance theorem nodes are retained only in the proof narrative
and imports.

Validation: prescribed scompile.py compiled the sandbox module in 5.5 s and the
library module in its private overlay in 5.4 s, with no errors or warnings. The
first expanded evaluation expression timed out; using the already landed named
canonical component repaired the elaboration without changing the hypothesis.
