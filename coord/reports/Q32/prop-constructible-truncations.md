## Worker report

The module `Sheaf.Paper.ConstructibleTruncations` states
`WeilConjectures.constructibleTruncations_exists`, with one postponed theorem and three
fully defined helpers packaging its clauses. It uses the current intrinsic integral,
raw rational localization, and general common-stage categories. The natural-language
statement, statement dependencies and proof plan of the item are unchanged.

Hypothesis and clause correspondence:

- The tuple p,a,q,k₀,k is `D : FiniteFieldDatum.{u}`; its fields include primality,
  positive exponent, q=p^a, cardinality, and the chosen algebraic closure.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`.
- The fixed closure is `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`,
  `[IsAlgClosure (Padic l) Ω]`; `v` is independent of the scheme universe `u`.
- A finite field contained in Ω is `E : AlgebraicallyClosedCoefficients.Index l Ω`.
  Its canonical `Coefficient.{u} l Ω E` model is transported by `Shrink.algEquiv`
  from the actual subfield. Quantifying over these indices includes every finite
  coefficient field contained in the chosen closure. It imposes no equality of
  the closure and site universes. Stage is the recorded raw rational category,
  with the recorded intrinsic integral objects and finite-torsion reductions.
- Y is `Scheme.{u}` with `Y.Over (Spec (.of D.k))` and both
  `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism. These are
  precisely finite type; neither separatedness nor descent from a k₀-scheme is assumed.
- The two choices of Λ are handled simultaneously: `t E : TStructure (Stage ... E)`
  for every finite field E, and `s : TStructure (generalAlgebraicallyClosedConstructibleCategory ...)`.
- Each t-structure supplies the actual `truncLE m`, `truncGE m`, counit, unit,
  connecting map and distinguished triangle `triangleLTGE (m+1)`. The type
  `TStructure` asserts shift stability, orthogonality and truncation triangles;
  Mathlib constructs these truncation functors from precisely those axioms.
- The first two conjuncts of `ConstructibleTruncations` identify *every* indexed
  aisle with `sfRationalStandardClass` / `sfCommonStageStandardClass`. Thus they
  are the standard truncations, rather than arbitrary bounded t-structures.
- The next two conjuncts assert `(t E).bounded K` for every finite-stage object
  and `s.bounded K` for every common-stage object.
- Finite scalar extension and the coefficient tower are `stageTransition ... E L h`.
  This is the normalized actual rational scalar extension with the recorded scalar
  associators and unit. `ConstructibleTruncationCompatibility` asserts uniquely
  characterized natural isomorphisms for both truncations, for every integer m.
  The upper comparison preserves the canonical counit; the lower comparison
  preserves the canonical unit. Uniqueness is the universal characterization of
  standard truncation comparisons, not an arbitrary choice of isomorphism.
  It makes their identity/composite/natural-transformation compatibilities canonical,
  as expressed by the already recorded t-exact comparison lemma; in particular
  the scalar associator and unitor comparisons agree throughout a tower.
- Agreement at every common finite presentation is the same compatibility package
  for each `GeneralAlgebraicallyClosedCoefficients.inclusion E`. This applies to
  functors and morphisms, not just to object representatives.
- Cohomology is defined literally by `constructibleTruncationCohomology t i :=
  (t.truncLE i ⋙ t.truncGE i) ⋙ shiftFunctor _ i`. Hence its object is exactly
  `(τ≥i(τ≤i K))[i]`. The compatibility package also asserts the natural
  isomorphism of these cohomology functors with each specified functor.
- Every automorphism is `h : Y ≅ Y` (no requirement that h respect the k-structure).
  The final two conjuncts use the actual recorded `rationalDerivedPullback ... h.hom`
  and `commonStageDerivedPullback ... h.hom` and assert both truncation and
  cohomology comparisons. There is no arbitrary substitute pullback functor.
- The existential `units : ∀ y : Y, Invertible (l : Y.residueField y)` is a
  *conclusion*, needed to instantiate the recorded pullback APIs. It is not an
  added hypothesis: l≠p implies nonzero in the characteristic-p residue fields,
  hence invertible. The package defines a local instance from the supplied data;
  the theorem proves existence of it. No proof/data is hidden behind sorry in a def.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its defining import:
  `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, and `finite_coefficientExtensionRing`.
- Mathlib `FieldTheory.IsAlgClosed.Basic` / `AlgebraicClosure`: `IsAlgClosure`,
  `AlgebraicClosure` (arbitrary fixed closure is used, not just the latter model).
- The scheme-property convention node has no declaration; the standard Mathlib
  `Scheme`, `Scheme.Over`, `LocallyOfFiniteType`, `QuasiCompact` implement its finite-type convention.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, underlying all positive reductions.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`, including common finite reduction bounds.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`,
  `stageSystem`, `stageTransition`, `inclusion`,
  `generalAlgebraicallyClosedConstructibleCategory`; the coefficient indices and
  universe transports are `AlgebraicallyClosedCoefficients.Index` and `Coefficient`.
- Mathlib `DerivedCategory.homologyFunctor` is used by the standard-class definitions,
  giving precisely the cohomological inequalities required for the standard pair.
- The repaired standard-pair binding uses `Sheaf.Paper.SfConstructibleHeart`:
  `sfIntegralStandardClass`, `sfRationalStandardClass`, `sfCommonStageStandardClass`.
  Only these *definitions* occur in the statement. The chosen t-structures and
  existence/heart theorems of that downstream module are not used.
- Mathlib `TStructure`, `truncLE`, `truncGE`, `truncLEι`, `truncGEπ` and shifts
  provide the standard categorical constructions and comparison equations.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `commonStageDerivedPullback`, with their prescribed integral and scalar formulas.

Edge cases checked before writing: empty Y (the units function is empty and the
zero categories are covered); zero complexes and cohomology; all negative, zero
and positive cutoffs and i, with the cohomological i-shift rather than -i;
identity automorphisms and coefficient inclusions; arbitrary scheme automorphisms;
non-flat reduction maps are not coefficient-field tower transitions. There is no
flat-cohomology hypothesis. Independent Ω and site universes are retained using
the existing coefficient-size transports. The theorem has no hypothesis at a
finite torsion level n=0; those levels enter only through the recorded n≥1 reductions.

Searches (all through the prescribed tools or read-only sources):

- `msearch.py leanfinder`: "bounded t structure truncations constructible l adic
  derived category commute scalar extension pullback". Eight unrelated general
  homological results; none states this package on the raw rational/common-stage categories.
- `msearch.py leansearch`: "standard t structure truncations commute t exact functor".
  General `TStructure.truncLT`, `truncGE` and complex truncation constructions;
  reuse their definitions, no instance of the present coefficient categories.
- `msearch.py loogle`: `CategoryTheory.Triangulated.TStructure.truncLT,
  CategoryTheory.Triangulated.TStructure.truncGE`. General truncation identities,
  natural maps and triangles; no coefficient-specific statement.
- `msearch.py grep`: `truncLT|truncGE`, `CategoryTheory/Triangulated/TStructure`.
  General Mathlib truncation APIs and the induced-t-structure interface.
- `rg` over Mathlib and project sources for truncation/cohomology interfaces;
  `rg` on WeilConjectures and lean/Sheaf for `constructible.*[Tt]runc`,
  `[Tt]runc.*[Cc]onstructible`, and `prop-constructible-truncations`.
  Upstream `SixFunctors/ProEtale/Adic/Truncation.lean` is not an exact match:
  its own implementation note explicitly uses the ambient Qbar-adic sheaf category,
  omits the rational E-stage, and does not use the common finite-stage category.
  Upstream `CategoryTheory/DerivedCategory/Constructible.lean` only supplies
  finite étale coefficient truncation stability. Neither is re-recorded as this node.
- Existing `SfConstructibleHeart` gives exactly the intrinsic *standard classes*,
  so the older recorded standard-pair interface is rebound to those rather than
  writing duplicate definitions. The item itself also needs scalar and actual
  pullback comparisons, absent from those heart declarations.

No statement dispute or correction. The only postponed proof is the named
`constructibleTruncations_exists`, whose docstring gives the existing proof route.

## Dependency modules

`def-weil-constructible-standard-tstructure`: lean-only §1(B) repair, with
`existing: true`, to the already published `Sheaf.Paper.SfConstructibleHeart`
standard-class definitions. Its previous module lives on the legacy integral,
rational and common-stage categories and therefore cannot type the currently
recorded intrinsic derived operations. Bool true/false gives the two classes and
n=0 gives the standard pair; all integer n give its shifts. The recorded source
statement is unchanged. No new module or copy of any notion is introduced.
There is no dependency on `def-weil-constructible-heart` or its downstream
existence assertions: the consumer supplies existential t-structures, and uses
only the three cohomological predicates already defined in that module.

The binding repair was also checked against the current server source through
`scompile.py --source Sheaf.Paper.SfConstructibleHeart`; the three predicate
signatures and their cohomology/isomorphism-closure bodies match the local source.

## Validation tool failure

The prescribed scompile.py checks were started for this file. An earlier process
terminated with exit 143 without Lean diagnostics. The current full-source retry,
started at about 15:39 UTC on 2026-10-17, still had no compiler result at 15:58 UTC.
The prescribed deliver2.py --no-push invocation is also stalled in its two-file
compile (the module and existing-declaration probe), before any preflight verdict.
There is no Lean error available to repair and no successful compile or delivery
is claimed. The server source-read wrapper succeeds immediately and confirms the
repaired dependency interface. No direct compiler invocation, limit increase,
shared-file edit, Git mutation, or pushed delivery was attempted.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
