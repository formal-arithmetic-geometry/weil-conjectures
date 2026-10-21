## Worker report

The module `Sheaf.Paper.TorsionAcyclicNormCoefficientTest` states
`AlgebraicGeometry.ProEtale.torsionAcyclic_normCoefficient_test` with `sorry`.
Two real helper definitions in the same owning module name the canonical limit
section and spell out the quantified conclusion. There are no proofs, new DAG
nodes, dependency repairs, or statement corrections.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Distinct primes p and ell: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]`
  and `hpℓ : p ≠ ℓ`.
- The characteristic-p field k: `(k : Type u) [Field k] [CharP k p]`.
- The finite normed extension E/Q_ell: `[NormedField E]`,
  `[NormedAlgebra ℚ_[ℓ] E]`, `[FiniteDimensional ℚ_[ℓ] E]`.
  A compatible multiplicative norm on a finite extension of Q_ell gives exactly
  its extended norm topology; no completeness instance is required as a binder.
- The algebraic closure with extended norm: `[NormedField Ω]`,
  `[NormedAlgebra E Ω]`, `[IsAlgClosure E Ω]`. There is no completeness binder
  on Ω and no finite-subextension restriction on its sections.
- The small directed poset with least element: `I : Type u`, `PartialOrder I`,
  `OrderBot I`, `IsDirected I (· ≤ ·)`. The node's 0 is written `⊥`.
- The inverse system of affine schemes is represented by its coordinate-ring
  diagram `R : I ⥤ CommRingCat.{u}`, with stages `Spec (R.obj i)` and transition
  `Spec.map (R.map (homOfLE h))` for h : i ≤ j. This is the contravariant
  equivalence between affine schemes and commutative rings, so includes every
  tower in the node, up to its canonical affine identifications.
- The k-structures and compatibility are the natural transformation
  `κ : (Functor.const I).obj (CommRingCat.of k) ⟶ R`.
- Regular stages: `hregular : ∀ i, IsRegularScheme (Spec (R.obj i))`.
- Finite-type stages: `hfiniteType` gives `LocallyOfFiniteType` and
  `QuasiCompact` for each structural `Spec.map (κ.app i)`.
- Finite locally free transitions: `hfiniteFlat` gives `IsFinite` and `Flat`
  for each transition. These are equivalent to finite locally free here:
  regular stages are locally Noetherian; their affine coordinate rings are
  Noetherian; a finite flat module over a Noetherian ring is finitely presented
  and hence locally free of finite rank. Conversely finite locally free is
  finite and flat. No transition is required to be globally free, surjective,
  or of constant rank.
- The initial section f0 is `f₀ : R.obj ⊥`, using `Scheme.ΓSpecIso` to identify
  coordinate rings and global sections. Its pullbacks are exactly
  `(R.map (homOfLE bot_le)).hom f₀`; `hregularElement` puts each of these in
  `nonZeroDivisors (R.obj i)`.
- The affine limit is exactly `Spec (colimit R)`. `HasColimit R` only supplies
  Mathlib's choice of the colimit, which exists for these small diagrams; it
  is not a mathematical restriction on the diagram. `normTestLimitSection`
  applies the canonical coprojection to f0 and then `Scheme.ΓSpecIso.inv`.
- W and j are `((Spec (colimit R)).basicOpen (normTestLimitSection R f₀))`
  and its `.ι`.
- For every s ≥ 1: `htorsion : ∀ s : ℕ, 1 ≤ s → ...`.
- The constant Z/ell^s sheaf as a module over itself is the recorded
  `constantSheaf`, valued in `ModuleCat (ULift (ZMod (ℓ ^ s)))`, applied to
  the regular module `ModuleCat.of A A`. `ULift` only implements the coefficient
  size convention, without changing any algebra or any section.
- Degree zero is `(DerivedCategory.singleFunctor _ 0).obj`.
- The hypothesis is `IsIso` of the actual
  `ProEtale.derivedUpperStarLowerStarAdjunction ... j` unit, evaluated at that
  degree-zero constant module. These are sheaves of modules over the constant
  ring, in the ordinary unbounded derived category; the functors are the
  existing total derived functors, not adic or completed derived functors.
- The conclusion is the conjunction of `NormTestLisseOpenUnit` for
  `Profinite.continuousCoefficientRingObj E` and for
  `Profinite.continuousCoefficientRingObj Ω`. This established common-universe
  construction has sections `ULift C(P,F)` on every profinite P, with pointwise
  ring operations and restrictions by precomposition, exactly the all-continuous
  construction in `ContinuousMapCondensedRing`, specialized to v = u. It is not
  `padicAlgClRingObj` or a finite-subextension-valued sheaf.
- That predicate quantifies over every `(V : Scheme) (v : V ⟶ X)` with
  `[WeaklyEtale v] [IsAffine V]`, the affine objects of the recorded small
  pro-etale site, and every internal module N over `condensedRingObj Λ V`.
- The lisse condition is the existing `IsLisseCoefficientModule Λ N`, which
  quantifies over a pro-etale cover and finite free ranks allowed to vary.
- The base-changed open j' is `(V.basicOpen (v.appTop.hom f)).ι`, the canonical
  principal-open presentation of W ×_X V, with the actual pulled-back section.
- The conclusion is `IsIso` of
  `(CondensedRing.derivedUpperStarLowerStarAdjunction Λ j').unit.app
  ((DerivedCategory.singleFunctor _ 0).obj N)`. It is the actual derived unit
  with its specified map, not existence of an unrelated isomorphism.
  Pullback for these coefficients is exact, so its left derived version is
  canonically the j'^* in the node; direct image is computed on K-injectives
  by the existing ordinary unbounded derived functor.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`:
  `AlgebraicGeometry.IsRegularScheme` (locally Noetherian and stalkwise regular).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `QuasiCompact`; `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`;
  `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `Scheme.ΓSpecIso`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` records generic
  `DerivedCategory` and its standard variants; its etale-specific abbreviations
  are not used for this pro-etale statement. The ordinary generic category and
  `DerivedCategory.singleFunctor` are instantiated on the appropriate module
  category through the published pro-etale framework.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, with its all-continuous
  sectionwise construction. The established scheme-universe API
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` publicly exposes
  `Profinite.continuousCoefficientRingObj` and its canonical commutative
  ring-object structure for this same construction; it is used to match the
  existing internal-module universe convention.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj`, the underlying object of the recorded `coefficientRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  the total derived functors and the publicly exposed canonical
  `CondensedRing.derivedUpperStarLowerStarAdjunction`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `IsLisseCoefficientModule`.
- For the finite coefficient hypothesis,
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`:
  `ProEtale.derivedUpperStarLowerStarAdjunction`.

All recorded proof-dependency modules are imported privately when they have a
recorded module. Mathlib matches for completion, extension norms, affine qcqs,
and spectral spaces are also imported. The still-unstated proof inputs
`det-lem-bounded-continuity-sections` and
`lem-sfb-norm-completion-positive-cohomology-mono` have no modules to import;
no missing statement-level notion is hidden by that fact. The eight-step
natural-language proof is in the theorem docstring, including the separate
completion-monomorphism obligation.

Edge cases: the least element prevents an empty indexing poset, as in the node;
a one-stage system is allowed. Zero rings and empty affine schemes have not
been excluded. The nonzerodivisor hypothesis uses its usual definition even
in the zero ring. Unit f0 gives the identity open. Zero-rank free modules are
included by the existing lisse definition and can be supplied as N. No
connectedness, positive-rank, nonempty-scheme, nontrivial-divisor, or completeness
hypothesis was introduced. Neither E nor Ω is replaced by finite-valued maps.

Searches performed using msearch.py:

- LeanFinder: “Finite torsion open restriction isomorphisms imply acyclicity
  for continuous norm topological l adic coefficient lisse modules” returned
  eight unrelated results (Nobeling successor, light condensed modules,
  solidity, adic completeness/completion). No matching criterion.
- Loogle: `IsIso, Adjunction.unit` returned zero hits, with unknown identifier
  `IsIso`; no declaration was inferred from that failed name lookup.
- LeanSearch: “Finite torsion open unit isomorphisms detect acyclicity for
  continuous l adic coefficient modules” returned eight results concerning
  open groups of units, discrete condensed adjunctions, continuous H0 and
  algebraic adic completion. None states this criterion.
- Mathlib grep:
  `(torsion|adic|Condensed).*(acyclic|localCohomology)|(acyclic|localCohomology).*(torsion|adic|Condensed)`
  returned five comments in `Algebra/Homology/LocalCohomology.lean`, no match.
- Project rg over `lean/WeilConjectures` and `lean/Sheaf` for norm-coefficient
  names and torsion acyclicity found the downstream
  `RootCoordinateSupportedVanishing` citation and unrelated torsion-acyclicity
  modules, but no declaration of this criterion. A subsequent exact-name/node-id
  search found no declaration in either source root. Read the downstream module
  to check that its coefficients use the same all-continuous ring API.

The previous worker's stale-assignment objection concerns `reviewed` of stage 1.
The node has no `lean` and no `reviewed_lean`; its stage-1 split review therefore
is not a reason to split again or to stop its stage-2 statement. The node's
statement, proof, dependencies, and all review fields are unchanged.

Validation: scompile.py compiled the original statement cleanly in both sandbox
and library modes. The delivered version also includes the recorded private
proof imports and is compiled again, then checked by deliver2.py --no-push.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
