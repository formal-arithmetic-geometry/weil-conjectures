## Worker report

Q108, stage 2, lem-sp-integral-local-model-finite-matrix-reduction.

The delivery states the simultaneous derived matrix model in
`Sheaf.Paper.IntegralLocalModelFiniteMatrixReduction`, with primary declaration
`AlgebraicGeometry.ProEtale.IntegralMatrix.integral_local_model_finite_matrix_reduction`.
It also supplies a sectionwise interface for the scalar-local-model clause of the
existing dependency sk-def-sfb-constructible; see Dependency modules below. Every
helper definition has actual data; the main theorem alone has `sorry`. Its docstring
contains all eight proof steps and their DAG dependencies.

### Hypotheses and conventions

- The prime ell is `l : ℕ` with `[Fact l.Prime]`. The finite extension is `E : Type r`
  with `[Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  `Scalars l E` is a universe lift of `Padic.coefficientExtensionIntegers l E`,
  not a new valuation ring. A uniformizer is not an argument: the assertion is
  independent of its choice and all quotients use ell, allowing ramification.
- `S : Scheme.{t}` is arbitrary. `C : Type r` with `[SmallCategory C]`,
  `_site : C ≌ S.ProEt` and `_topology` specify the fixed small site and its transported
  pro-etale topology. This is a common containing universe for objects, homs and
  coefficients, not an equation between the scheme universe `t` and `r`.
  A small skeleton can have its hom types lifted to this common universe; no geometric
  hypothesis or change in topology is imposed. We work on that chosen site throughout.
- `J` is its topology. The `hD` family selects ordinary derived categories for abelian categories
  in the common universe, including the site and all its slices, at the explicitly
  bound morphism universe `w`.
  These are localization-size conventions, not extra hypotheses on L or S.
- `Residues l E n` is the actual quotient of the valuation ring by `(ell)^(n+1)`,
  lifted to the same value universe. Natural-number index `n` denotes the paper's
  positive index `n+1`; there is no missing positive level and no extra level zero.
  `coefficient`, `completion`, `scalarMap`, `projection` and `quotient` use the existing
  `WeilConjectures.CompletedSite` tower, its inverse limit and its canonical cone.
- `L : Modules J (completion l E J)` is a genuine module sheaf. `_hL` is
  `HasFiniteScalarConstantLocalModel`: locally, it is extension of the constant
  sheaf of a finitely presented scalar A-module. It quantifies over covering sieves,
  including empty covering sieves. `HasFiniteScalarConstantModelOn` identifies each
  specified covering-object model, without replacing its scalar module by an internal
  finiteness predicate on a condensed module.

### Conclusions, clause by clause

1. The theorem's first conjunct is `∀ n, Finite (Residues l E n)`. It makes no
   unramifiedness assumption.
2. The next conjunct quantifies over **every specified local model** `U, N`, with
   `HasFiniteScalarConstantModelOn ... L U N`. Thus the initially given cover and
   scalar modules may be retained. It chooses finite ranks `a b : ℕ`, one matrix
   `d : Matrix (Fin b) (Fin a) (Scalars l E)`, and a scalar augmentation `p`.
   `Function.Injective (Matrix.toLin' d)`, `Function.Exact ... p`, and
   `Function.Surjective p` express exactly the scalar short exact sequence.
3. `model` is constant module realization followed by ordinary extension along the
   actual constant-A-to-B map. The isomorphism `eN` identifies its restriction with
   the specified `L.over U`. The `ShortComplex` built from the restrictions of
   `model.map d` and `model.map p ≫ eN.hom` is `ShortExact`. These are extension of
   the same scalar sequence, not existentially chosen unrelated free sheaves.
4. `Nonempty (SimultaneousModels ... d)` gives one family of derived isomorphisms
   `comparison n`, for every positive level on this very same U. `reduction` is the
   universal derived scalar extension of `L[0]` along the actual limit projection.
   `overDerived` is exact derived slice restriction, to the *restricted ring*.
   The target is `DerivedCategory.Q.obj` of the restricted constant realization of
   `matrixComplex (reduced d n)`. `matrixComplex` is the ordinary mapping cone of
   the degree-zero map between the two scalar free modules.
5. The `left` and `right` basis fields and the differential/support conjuncts specify this
   complex in degrees -1 and 0. In the specified free bases, the differential on
   each constant vector is precisely `Matrix.toLin' (d.map scalarQuotient)`, with
   zero terms outside those degrees. Consequently the isomorphism is an isomorphism
   of derived objects, not merely an assertion about their cohomology groups.
6. `transition` explicitly composes the normalized extension unit with the canonical
   coefficient associator from `SuccessiveDerivedQuotient.Normalization`, followed
   only by the equality supplied by the inverse-limit cone.
   It is the actual quotient-induced map. `derivedRestrictionOverIso` interchanges
   exact scalar restriction and slice restriction canonically. `localizeSquare`
   lifts the ordinary identity-on-sections interchange through the specified
   homotopy localization factorizations. `composeFactors` pastes those factorizations.
   `derivedRestrictionOverGeneral` specializes it to the actual restrictions.
   `restrictedTransition` composes the original transition with this comparison.
   The `termwise` field is a chain map between the actual matrix complexes with restricted
   target scalars. The two section equations prescribe entrywise
   `scalarReduction` on **all** constant vector generators on slice objects. Since
   these are sheafifications of constant free modules, these equations determine
   the termwise quotient maps. The final transition-square equation identifies their localization
   with the actual derived transition under `comparison`. Quantification is over
   every `m ≤ n`, including `m=n`, with no cover refinement depending on n.
7. `scalarKernel` is the kernel of the reduced scalar linear map; `scalarCokernel`
   is the free target modulo its range. For every n the theorem asserts `Finite`
   and `Module.FinitePresentation` for **both** modules. The two `Nonempty` isomorphisms
   identify degree -1 and degree 0 homology of the restricted derived reduction
   with the restricted constant sheaves of those exact scalar modules.
8. The third main conjunct states `IsZero` of global cohomology in all degrees
   `i ≠ -1`, `i ≠ 0`. The last gives covering-sieve constant models with
   `Module.Finite` for cohomology in each of degrees -1 and 0. The stronger same-cover
   assertion, with finite and finitely presented modules, was already supplied in
   the second main conjunct.

### Dependency declarations used

All original statement-dependency records and declaration signatures/docstrings were
read. The module imports the recorded statement modules publicly and the available
proof-dependency modules as plain imports. In particular:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` /
  `Padic.finite_coefficientExtensionRing`, with the public coefficient-extension
  definitions `Padic.coefficientExtensionIntegers`.
- Mathlib `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`,
  `CategoryTheory.constantSheaf`, `SheafOfModules`, and `DerivedCategory`.
- `Sheaf.CategoryTheory.RingedSiteModules` / `CategoryTheory.ringedSiteModules`:
  the ordinary category is `SheafOfModules`, not a substitute sheaf category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` /
  `SheafOfModules.cochainModulesMonoidal` and the sheafified tensor conventions.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` /
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`, and its public sectionwise
  `SheafOfModules.derivedChangeRingIndependentCoefficients` / `changeOfRings` interface.
- `Sheaf.Paper.SmoothPurityCoefficientTowers` /
  `AlgebraicGeometry.ProEtale.spCoefficientTowers`: positive indexing and ell-power
  quotients. Its common-site presentation is the already landed
  `Sheaf.Paper.CompletedIntegralOnSmallSite` /
  `WeilConjectures.CompletedSite.constant`, `.tower`, `.ring`, `.constantMap`.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor` /
  `CategoryTheory.commutativeSiteConstantModuleFunctor`, the actual constant-module
  sheafification (used termwise as well as on kernel/cokernel modules).
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral` /
  `CategoryTheory.ringedOverFunctor_exactGeneral` (the exact restriction is
  passed through Mathlib `Functor.mapDerivedCategory`); `overComplex` directly uses
  the exact slice restriction functor mapped to homological complexes.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientData` /
  `SheafOfModules.SuccessiveDerivedQuotient.Presentation` and `.Normalization`,
  obtained from `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization` /
  `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`,
  owned by `lem-sfb-successive-derived-quotient-normalization`.
  The universal localization property and the pure tensor/unit normalization
  determine these choices up to the canonical isomorphisms used downstream.
- `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification` /
  `SheafOfModules.restrictedTensorScalars`, the ordinary exact scalar restriction.

The existing landed helper nodes for these canonical constructions have been added
to stmt_deps. No new definition node is required: the remaining declarations are
named parts of the item's own matrix-model construction and are listed in its
lean.declarations.

### Edge cases checked before and after writing

- Empty S/empty covering sieves: the local condition and local conclusions are
  sieve statements; they do not demand a nonempty cover or a nonzero object.
- N=0 and L=0: ranks may both be zero (`Fin 0`), and the matrix and augmentation
  may be zero. No positivity of ranks occurs.
- Free N: rank a can be zero; the degree -1 kernel is retained as a possibly zero
  module and its sheaf is still identified.
- Torsion N, e.g. A/(pi): no torsion-free hypothesis occurs, and degree -1 homology
  is explicitly allowed. Nothing erroneously asserts an underived quotient alone.
- Ramified ell: ideals are powers of ell, not powers of a chosen uniformizer with
  the same exponent. Finiteness is asserted for these actual quotient rings.
- Positive minimal level: n=0 means ell^1. Identity transitions are included by
  h : m ≤ n with m=n. All transition choices belong to one simultaneous structure.
- Arbitrary S: no Noetherianity, separation, quasi-compactness or characteristic
  assumption is added. The coefficient extension field's size is independent of
  the scheme's size. All universes and section variables are explicitly bound;
  autoImplicit is disabled.

### Searches

- Prescribed msearch leanfinder: `Derived reductions of integral local constant
  sheaves computed by one finite matrix at all finite coefficient levels`.
  Eight results concerned Profinite.NobelingProof constructions; none gave the
  simultaneous derived isomorphisms and quotient squares.
- Prescribed msearch loogle: `Module.FinitePresentation, CochainComplex.mappingCone,
  constantSheaf`. No matches (constantSheaf was unrecognized by that service).
- Prescribed msearch grep: `finite.*matrix|matrix.*reduction`, ModuleCat subtree.
  No matches.
- Prescribed msearch leansearch: `finite matrix derived reduction of a locally constant
  sheaf over complete discrete valuation ring quotient`. Eight hits included condensed-module functors,
  matrix finiteness and finite DVR quotient facts, not this theorem.
- rg searches in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  matrix/reduction/finite-local-model patterns: no equivalent declaration. The
  existing constant-module, completed-small-site, scalar-restriction and universal
  derived-extension interfaces were reused.
- Read the Stacks source for 093J and 093M, and the current blueprint under
  `literature/blueprint/latest/` for the reduction/constructibility paragraph.

No statement correction or mathematical dispute is claimed. The node's TeX statement,
proof and proof dependencies are preserved.

## Dependency modules

`sk-def-sfb-constructible` has a lean-only companion interface under §1(B).
`Sheaf.Paper.SectionwiseFiniteConstantLocalModel` publicly imports the current landed
`Sheaf.Paper.FiniteConstantRingedLocalModel`, retaining Q120's
`HasFiniteConstantRingedLocalModel` and all seven earlier declarations. The node's
`lean.declarations` preserves these eight names in order and appends
`HasFiniteScalarConstantModelOn` and `HasFiniteScalarConstantLocalModel`.
The small-site form is needed beside the existing scheme-site form: this item uses
its chosen small site and completed coefficient sheaf at its own coefficient universe.
The added predicates express the same scalar finite-presentation clause on that site.
The coefficient morphism and ordinary extension are the canonical existing ones;
no arbitrary tensor or sheafification functor is introduced. Only the dependency
node's lean field is changed, with a note explaining this companion form.

## Returned delivery repairs

- F1: inline the normalized extension unit and coefficient associator in `transition`.
  Remove the import and statement dependency for
  `lem-weil-pbc-flat-coefficient-reduction-adjunct`; all required data come from
  the recorded definition `def-weil-pbc-successive-derived-quotient-data`.
  The genuine existence theorem `lem-sfb-successive-derived-quotient-normalization`
  is imported and cited directly because `presentations` and `normalization` choose
  its universally characterized presentations and normalized comparisons; it was
  previously available only transitively through the removed flat-adjunct import.
- F2: remove the unused `PerfectConstantLocalChainRepresentative` import and
  `lem-sfb-perfect-constant-local-chain-representative` statement dependency.
- F3: rebase the dependency interface on Q120's current landed
  `FiniteConstantRingedLocalModel` module and preserve all eight existing declarations,
  adding the two small-site predicates beside them. The genuine
  `lem-pe-restricted-kflat-tensor-identification` dependency is retained.

## Second reading by Q108

I reread the full signature against every clause of the node, including the matrix
support, restricted coefficient rings, the canonical derived interchange, quotient generators,
and the cohomology conclusions. The checks above are the author's audit. Per this
dispatcher's instructions no other agent was started; independent review is the
maintainer's review of the delivered branch.

## Validation

Both repaired delivery modules compile cleanly with `scompile.py` against the live
published library, with the companion interface supplied before its consumer.
The final library compiles took 27.8 s for the interface and 14.7 s for the main
module. No errors or unexpected warnings were reported. The node signatures are
verbatim substrings of their modules, all Lean lines are within 100 characters,
and the dependency record retains all eight current landed declarations plus the
two companion predicates. Final delivery preflight is run by `deliver2.py`.
