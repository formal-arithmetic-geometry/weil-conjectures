## Worker report

The delivery states `AlgebraicGeometry.ProEtale.finiteClassicalUnboundedComparison`
in `Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison`. Its single proof
is `sorry`, as required for stage 2. No definitions, new nodes, dependency changes,
or statement corrections are introduced.

Hypotheses and clauses, read against the node:

- `k : Type u`, `[Field k]`, and `hbase : Finite k ∨ IsAlgClosed k` render
  precisely the finite-or-algebraically-closed base-field assumption.
- `ℓ : ℕ`, `[Fact ℓ.Prime]`, and
  `hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ))` render primality and invertibility in k.
- `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` give finite commutative
  coefficients. `hA : ∃ r : ℕ, 1 ≤ r ∧ (ℓ : A) ^ r = 0` is exactly the
  annihilation condition including its positive exponent. No nonzero-ring assumption.
- `X : Scheme.{u}`, `[X.Over (Spec (CommRingCat.of k))]` give the k-scheme;
  `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism give finite type.
  No separatedness or nonemptiness is imposed.
- The ordinary module-sheaf presentation is `Sheaf site (ModuleCat.{u + 1} A)`.
  `FiniteCoefficientEtaleDerivedCategory X A` is the recorded abbreviation for
  its unbounded etale derived category. The pro-etale category is the corresponding
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))`.
  These are ordinary constant-coefficient modules, with no adic completion or
  constructibility restriction. The dependency's `finiteCoefficientEtaleRealization`
  and `finiteCoefficientRealization` identify these presentations with modules over
  its specified etale constant and pro-etale continuous-function ring sheaves.
  In particular the presentation does not replace the stipulated coefficient sheaf
  by another mathematical object. A discrete topology is implicit in constant
  coefficients, so no independently chosen topology is needed in this signature.
- `comparisonUpperStar (ModuleCat.{u + 1} A) X` is the exact inverse image of
  the recorded site comparison, before coefficient realization. Its
  `mapDerivedCategory` is the exact termwise unbounded functor.
- The first conjunct quantifies over every etale derived object M and asserts
  `IsClassicalComplexFor X A` of its inverse image. The existing predicate
  quantifies over every integer q and every affine pro-etale presentation, asserting
  invertibility of the canonical continuity map for H^q. It is the fixed-ring
  presentation of `IsClassicalModuleComplex` from the recorded classical-definition
  dependency; no essential-image definition replaces classicality.
- The second conjunct quantifies over every pro-etale derived object K satisfying
  that predicate and asserts `IsIso` of the actual counit of
  `(comparisonAdjunction (ModuleCat.{u + 1} A) X).mapDerivedCategoryRightDerivedAdjunction`.
  Its right adjoint is `(comparisonLowerStar _ X).rightDerivedFunctor`, computed
  by K-injective resolutions. This is a specified canonical adjunction, not an
  arbitrary adjunction or an arbitrary isomorphism. There is no lower or upper bound.
- The final conjunct asserts `∃ M, Nonempty (nu^* M ≅ K)` for every classical K.
  Quantifying over ambient K with its classicality hypothesis expresses objects
  of the strictly full classical subcategory without adding another definition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; `QuasiCompact` from its imported
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`. Finite type is their conjunction.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the exact underlying category
  of `FiniteCoefficientEtaleDerivedCategory`. The recorded derived-categories
  module `WeilConjectures.AlgebraicGeometry.DerivedCategories` was read through
  `scompile.py --source`; it documents precisely this encoding. Its side copy is
  already imported by `ProEtaleFiniteModules`, so the duplicate upstream module
  is not additionally imported.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientEtaleDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientRealization_isEquivalence_ring`, and the etale realization.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, which is exactly
  `comparisonAdjunction (ModuleCat A) X`. This module is publicly reexported by
  `ProEtaleFiniteModules`.
- `Sheaf.SixFunctors.ClassicalDefinition`:
  `IsClassicalModuleSheaf` and `IsClassicalModuleComplex`. Its import exposes the
  same affine-presentation predicate `IsClassical` on underlying set sheaves.
  The existing fixed-commutative-coefficient form `IsClassicalComplexFor` is used
  from `Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions`, whose full current
  source was also checked with `scompile.py --source`. Both are the recorded
  dependency's existing interfaces, not a newly introduced copy of a definition.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, used by the canonical right-derived construction.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`, whose
  implementation derives the homotopy adjunction using exact inverse image and
  K-injective right derivability. Its counit is the one in the statement.

All recorded proof-dependency modules with project declarations are imported
nonpublicly: ClassicalDerivedEquivalence, ProEtaleClassicalBounds,
UnboundedClassicalTruncation, BoundedBelowInjectiveResolution, the upstream
ExactFunctor interface, KInjectiveTotalDerived,
RingedSiteKInjectiveResolutionsOfUniverses, BoundedBelowProEtaleComparison,
and ProEtaleClassicalSheaves. The site-comparison module is already public.
The remaining Mathlib leaves (K-injective Hom localization, exact module
sheafification and the derived cohomology isomorphism criterion) are in the
import closure. The theorem docstring carries all six natural-language proof steps.

Source check: read the current blueprint unit `sk-lem-geo-affine-local`, its
opening proof paragraph, and the current `sk-prop-pe-unbounded-classical` unit.
Read Bhatt--Scholze PDF pp. 37--39 using pdftotext: Proposition 5.2.6(3),
Remark 5.2.8, Definition 5.3.1 and Proposition 5.3.2. The finite primary case
is the stipulated locally finite-cohomological-dimension specialization. No
node fault or disputed statement was found.

Edge cases checked before and after writing: empty X, zero ring A, zero complex,
a sheaf in a single arbitrary integer degree, bounded-below complexes, complexes
unbounded below, finite fields and algebraically closed fields, disconnected X,
and r=1. No positivity of dimension, nonzero coefficients, boundedness,
constructibility, finite generation of cohomology, or separatedness entered.
The site retains object universe u+1 and morphism universe u. Fixed-ring module
values are in u+1, as prescribed by the existing ordinary module interface.

Searches performed on 2026-10-18:

- msearch LeanFinder: "The unbounded derived etale proetale inverse image has
  classical cohomology and its counit is an isomorphism on classical complexes".
  Eight results, concerning light condensed sequential counits, representations,
  sheaf equivalences and etale algebras; no matching statement.
- msearch Loogle: `"proetale"`. Twelve results on the big pro-etale topology,
  precoverage and its stability/subcanonicality; no matching comparison theorem.
- msearch grep: `classical.*cohomology|cohomology.*classical`. One Mathlib hit
  in ElladicCohomology.lean, an explanatory future-work comment; no declaration.
- msearch LeanSearch: "The unbounded derived inverse image from etale to proetale
  sheaves is essentially surjective onto complexes with classical cohomology".
  Eight results on generic equivalences and derived localization essential
  surjectivity; no matching site-comparison statement.
- rg in WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for the
  node id, canonical comparison names, classical counits and the chosen theorem
  name. Existing bounded-below ClassicalDerivedEquivalence and unbounded
  full-faithfulness/direct-image comparisons are components, not the three
  unbounded classical-image conclusions of this item. The chosen name is unused.

Validation: scompile.py compiled the sandbox and final module individually,
with the prescribed 60-second limit. Both passed in about 2 seconds, with no
errors or warnings. Delivery preflight and its final compile follow below.

## Self-check by Q70

Resumed the saved packet on 2026-10-18 and retained its Lean source unchanged.
Opened the current node and all six statement-dependency records. Rechecked the
finite-type classes, the fixed-ring etale derived category, the finite-coefficient
realization interfaces, both classicality interfaces, the original-site module
adjunction, and the unbounded derived-adjunction construction against their sources.
The field, prime, invertibility, finite-ring, annihilation and finite-type hypotheses
match the node; the three conjuncts give classical image, the canonical counit
isomorphism and essential surjectivity, respectively. All integer degrees and
unbounded complexes remain included. No mismatch or source change was found.

The item copy differs from the shared node only in `lean`; its recorded signature
is verbatim, all variables and universes are explicit, every line is at most
100 characters, and the only theorem proof is `sorry`. The prescribed dry run
passed preflight and its per-file compile (commit 34e3eb7229); no errors or
unexpected warnings were reported. This is the resumed worker's self-check; the
maintainer supplies the independent review.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
