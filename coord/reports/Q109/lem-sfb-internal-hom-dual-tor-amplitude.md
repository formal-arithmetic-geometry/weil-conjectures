## Worker report

The module `Sheaf.Paper.InternalHomDualTorAmplitude` states
`AlgebraicGeometry.ProEtale.internalHom_dual_tor_amplitude` and defines two concrete
helpers used to render the source notion. `FiniteProjectiveCondensedModule` says that a
coefficient module is a retract of `Mod.finiteFree` (the finite-projective clause). The
noncomputable `scalarExtensionComplex` applies the point-to-chart module functor termwise
to a coefficient complex, with its zero-morphism witness explicit. The
`relativeInternalHomDual` definition is exactly
`RHom_B(P,B)`, with `B` represented by `Mod.regular (condensedRingObj Λ.X S)`.

The theorem renders the hypotheses and clauses as follows.

* `ℓ : ℕ` with `[Fact ℓ.Prime]` is the fixed prime; `k : Type u` with `[Field k]`,
  `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]` is a positive-characteristic
  field with characteristic different from `ℓ`.
* `S : Scheme.{u}` with `[S.Over (Spec (.of k))]`,
  `[IsSeparated (S ↘ Spec (.of k))]`, `[LocallyOfFiniteType (S ↘ Spec (.of k))]`, and
  `[QuasiCompact (S ↘ Spec (.of k))]` is a separated finite-type `k`-scheme.
* `Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})` and
  `[IsCommMonObj Λ.X]` render a commutative condensed coefficient ring; its coefficient
  sheaf is `condensedRingObj Λ.X S`.
* `P` is an object of the derived category of module objects over that coefficient sheaf.
* `hP` quantifies a pro-etale `Scheme.Cover`. For every cover member it supplies a
  coefficient cochain complex `F`, strict finite bounds `c,d`, degreewise finite-projective
  (finite-free retract) terms, and an isomorphism from the restriction of `P` to
  `DerivedCategory.Q` of the termwise scalar-extension complex. The explicit
  `PreservesZeroMorphisms` witness is only the categorical data required by
  `Functor.mapHomologicalComplex`; it does not add a mathematical restriction.
* The first conclusion quantifies every degree-zero sheaf `N` and every `q` outside
  `[a,b]`, asserting `IsZero` of the `q`-th homology of
  `CondensedRing.derivedTensor Λ.X S` applied to `P` and the single complex on `N`.
* The second conclusion uses `relativeInternalHomDual Λ S P` and asserts the same
  vanishing outside `[-b,-a]`.
* The final implication `IsEmpty S → a = 0 ∧ b = 0` renders the empty-scheme clause
  (the required interval is `[0,0]`).

The recorded dependency declarations used are:

* `sk-def-sfb-dc-setting`: `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`
  from `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
* `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
* `sk-def-localizing-closure`: `CategoryTheory.localizingClosure` and
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale` from
  `Sheaf.Paper.LocalizingClosure`.
* `def-pc-perfect-ring-complex`: `DerivedCategory.IsPerfectRingComplex` from
  `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`.
* `def-weil-pbc-strict-perfect-coefficient-package`:
  `SheafOfModules.StrictPerfectCoefficientRepresentationOfUniverses` and its package
  interfaces from `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`.
* `sk-def-sfb-derived-tensor-hom`: `CondensedRing.derivedTensor` and
  `CondensedRing.derivedHom` from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` (with the tensor
  module imported transitively).
* `sk-def-sfb-constructible`: `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, and `ConstantModelConstructibleFiniteTor` from
  `Sheaf.Paper.CondensedConstantConstructibility`.

Edge cases checked before writing were the empty scheme (the explicit `[0,0]` clause),
zero finite-free rank (`Mod.finiteFree` with `n = 0`), complexes with a single nonzero
term, and negative/zero cohomological degrees. The interval conclusion retains the
required inequality `a ≤ b` and reverses it exactly for the dual.

Searches made:

* `msearch.py ... leanfinder "finite Tor amplitude of a locally constant perfect complex
  and its derived internal Hom dual on a pro-etale site"`: only generic derived-category
  support and projective Tor lemmas; no matching global sheaf statement.
* `msearch.py ... loogle "DerivedCategory.finiteTorAmplitude, CondensedRing.derivedHom,
  CondensedRing.derivedTensor"`: no hits (the queried combined identifier is absent).
* `msearch.py ... grep "internalHom_dual_tor_amplitude|finiteTorAmplitude|
  relativeInternalHomDual" WeilConjectures`: no hits.
* `rg` over `WeilConjectures/` and the existing `lean/Sheaf/` tree for the theorem and
  helper names: no prior declaration; the dependency modules above were the only matching
  notions.

No statement correction, `STATEMENT-DISPUTED` flag, new DAG node, or dependency-module
repair was needed.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review, 2026-10-18)

The delivered theorem took an arbitrary commutative condensed ring `Λ`. That drops the node's
hypothesis that `Λ` is one of the admissible coefficient rings `A, ℤ_ℓ, 𝒪_E, ℚ_ℓ, E, ℚ̄_ℓ`
[sk-def-localizing-closure] (delivery-errors H3, a hypothesis dropped). The reviewer added the
hypothesis `_hΛ` in the exact form used by the landed det-sf-comp-composition-interchange
(`properOpenInterchange`), writing `Λ` for `Mon.mk Λ` because `Λ` is a bundled `Mon` here. The
module now also imports `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` and
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`. The record now lists the three
helper definitions in `lean.declarations`. Nothing else changed. The fixed file compiles
per-file with `nt_compile.py` (exit 0).
