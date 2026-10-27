## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectOpenRetract` states
`AlgebraicGeometry.AlgebraicSpace.exists_perfect_open_retract`, with the sole proof
left as `sorry`. It introduces no definitions. The mathematical statement is unchanged.
Source checked: Stacks, `spaces-perfect.tex`, Tag 09IX,
`lemma-direct-summand-of-a-restriction` (local lines 3659–3674). The source explicitly
allows an arbitrary base scheme and says that a perfect object on a quasi-compact open
is a direct summand of the restriction of a global perfect object.

Hypothesis and clause correspondence:

- The size convention is rendered by explicitly bound universes `u w` and
  `[HasDerivedCategory.{w} X.SmallModules]`, `[HasDerivedCategory.{w} U.SmallModules]`.
  Here `w` is the localization morphism universe and is not equated with `u`.
- The scheme S and spaces over S are `{S : Scheme.{u}} (X U : AlgebraicSpace S)`.
  S has no quasi-compactness, separatedness or Noetherian assumption.
- Every open cover of |X| has a finite subcover is
  `hXqc : CompactSpace (Point X.obj.obj)` in the established point topology.
- Quasi-compactness of the absolute diagonal is
  `hXqs : IsAbsolutelyQuasiSeparated X`. This is the existing affine-test criterion
  equivalent to absolute quasi-separatedness (Stacks 0AHR); it does not impose a
  quasi-separatedness assumption on S or replace absolute by relative quasi-separatedness.
- The open subspace inclusion is `(i : U ⟶ X)` with
  `hi : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) i.hom.hom`.
  This is exactly the scheme-test predicate used by the recorded `OpenSubspace` definition.
  Specifying the inclusion of U is the equivalent morphism presentation of an open subspace;
  no arbitrary-map substitute, specified atlas, or extra etaleness assumption is used.
- Its quasi-compactness is `hUqc : CompactSpace (Point U.obj.obj)`. Because X is qcqs
  and i is an open immersion, this is also the usual quasi-compact-open condition.
- The given object of D(O_U) is `A : U.DerivedModules`. The category is the existing
  localization of module sheaves on the equivalent small affine etale ringed model,
  not the derived category of QCoh. Its coefficients are the actual regular functions,
  with section universe u. The module equivalence is the existing chart restriction.
- Perfectness of A is `hA : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  U.smallStructureSheaf A`. This predicate gives, on covering sieves, a bounded complex
  whose terms split from finite free structure modules, with bounds and ranks allowed
  to vary locally. The identical predicate is used for the existential global Q.
- The contextual category C_X is the recorded `X.DerivedQCoh`, defined using
  `X.derivedQCohProperty`; it is not an additional assumption or conclusion of 09IX.
  No hypothesis asserting quasi-coherence of A has been added: perfection supplies it.
- The conclusion chooses `Q : X.DerivedModules` and its perfectness proof, then
  `s : A ⟶ (derivedTensorPullback i).obj Q` and
  `r : (derivedTensorPullback i).obj Q ⟶ A` with `s ≫ r = 𝟙 A`.
  Lean composition is left-to-right, so this is precisely r after s equals id_A.
- The symbol i* is the existing canonical `derivedTensorPullback i`. On an open
  immersion it equals exact etale restriction, rather than an arbitrary derived functor:
  `moduleTensorPullback_etale_restriction` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction` identifies
  ordinary tensor pullback with literal small-site restriction, normalized by
  `a tensor m` mapping to `a m`. The recorded `spaceEtaleTensorPullback_exact` and
  `spaceEtaleDerivedRestriction_existsUnique` in
  `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus` identify its total left
  derivation with the exact termwise restriction. Open immersions are etale on every
  scheme test. Using this already defined canonical pullback requires no new theorem
  or choice of functor in the delivered module.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `EtaleSite`, `structureSheaf`, `Modules`,
  `pullback` and `etalePullback`. Their full definitions use scheme-test squares and
  regular-functions restriction; no declaration is copied.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`; Mathlib's module sheaf and linear morphism
  structures were also read.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with exactly
  Mathlib's `SheafOfModules.IsQuasicoherent` and the slice sheafification instances.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsLocallyStrictPerfectComplexOfUniverses`,
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses`, and
  `SheafOfModules.StrictPerfectCoefficientRepresentationOfUniverses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, whose
  `IsRepresentableWith` predicate supplies the inclusion formulation above.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`; the adjunction preserves the prescribed chart-limit image.
- The already landed definition nodes `def-sfb-space-absolute-quasi-separated`,
  `def-sfb-space-small-ringed-model`, `def-sfb-space-derived-module-calculus`,
  `def-sfb-space-derived-tensor-pullback` are added to stmt_deps because the signature
  uses their canonical interfaces. Their declarations respectively are
  `IsAbsolutelyQuasiSeparated`; `SmallModules`, `smallStructureSheaf`,
  `smallModuleEquivalence`; `DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`;
  and `derivedTensorPullback`, in their recorded modules. All were read in full.

Plain proof imports include every currently stated proof-dependency module:
`DerivedEtaleZariskiEquivalence`, `AffinePerfectSupportExtension`, `PerfectImpliesQCoh`,
and `ReducedClosedSubspaceSupport`. The strict-perfect package is already a public
statement import. No Lean record is currently available for
`lem-sfb-space-qc-open-enlargement-induction`, `lem-sfb-space-perfect-objects-compact`,
`lem-sfb-etale-detects-perfect`, or `lem-sfb-space-distinguished-derived-gluing`, so
there is no module to import for those proof dependencies. They are retained unchanged
in proof_deps and described explicitly in the theorem's five-step proof docstring.
They are not required to type the statement.

Edge cases checked before writing: U empty, X empty (hence also U empty), A zero,
i the identity, disconnected opens, and a non-quasi-separated base S. No nonemptiness,
connectedness, positive rank, global boundedness, or base quasi-separatedness assumption
occurs. For U=X the identity retraction works; for empty U and A=0 the zero global
perfect object works. The splitting equation has the correct order. All universe and
object binders are explicit and `autoImplicit` is disabled.

Searches performed with `msearch.py`:

- LeanFinder: "A perfect complex on a quasi compact open algebraic subspace is a retract
  of the restriction of a perfect complex on the whole space". Eight unrelated hits,
  chiefly scheme section localization lemmas; no algebraic-space perfect extension.
- Loogle: `"Perfect", "Retract"`. Zero hits.
- LeanSearch: "Perfect complex on a quasi compact open extends as a direct summand of a
  global perfect complex". Eight hits concerning affine-open covers, scheme restrictions
  and complex truncation; none states 09IX.
- Mathlib grep: `perfect.*(retract|summand|restrict)|[Pp]erfectComplex`. Seven hits in
  perfect pairings/root systems; no matching statement.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` for the same pattern, the
  node id, and `exists_perfect_open_retract`, plus `dag/lean_names_upstream.json`:
  scheme perfect-complex results, generic site retract lemmas and consumers mentioning
  this node, but no existing declaration of the algebraic-space assertion. The similar
  scheme open-stalk retract lemmas have different hypotheses and conclusions.

Validation: `scompile.py NO lem-sfb-space-perfect-open-retract` compiled the module
both in sandbox mode and under its intended library module name, with no errors or
warnings. The prescribed dry run and final delivery are run after this report.
No statement dispute, node correction, new definition, or dependency repair is needed.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
