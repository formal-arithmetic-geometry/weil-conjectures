## Worker report

Statement module: `Sheaf.Paper.LocalIntegralPerfectModelCohomology`.
The prescribed `scompile.py` successfully compiled it in both the sandbox and library
contexts on 2026-10-21, with no errors or warnings.

Clause correspondence:

- Prime ell and a finite extension E/Q_ell: `l`, `[Fact l.Prime]`, `E`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
- R and its uniformizer: the dependency's `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionIdeal l E 1`. The latter is the span of the dependency's
  chosen uniformizer. Its `(n + 1)`st power is the positive-level quotient ideal.
- Arbitrary schemes and a locally closed immersion: `{X S : Scheme.{u}}`, `g : S ⟶ X`,
  `[IsImmersion g]`. Mathlib's `IsImmersion.isImmersion_iff_exists` identifies this with
  closed immersion followed by open immersion, including the empty scheme.
- The actual small pro-etale site is `S.ProEt`, with object universe u+1 and Hom
  universe u. Coefficients and section modules lie in u+1. No object/Hom universe
  equality is imposed. Any given coefficient and scheme sizes can be embedded in such
  a common ambient universe.
- B_T is `adicLisseCompletedRing T (Padic.coefficientExtensionIdeal l E 1)`, the limit
  of `adicLisseRingSystem`, whose natural index n means exponent n+1. The rings at
  finite levels are sheafifications of constant commutative-ring presheaves.
- The existential ring-sheaf isomorphism c satisfies the equation for every quotient
  projection. The right side is inverse image of the projection followed by the
  recorded `proEtaleConstantInverseImageMap`. Thus c is uniquely fixed as the canonical
  coefficient comparison, rather than an arbitrary identification.
- `localIntegralModelRestriction` is the existing `proEtaleRingModulePullback` followed
  by `SheafOfModules.localizedSystemRestriction`, definitionally the actual overFunctor.
  The imported pullback and localized-restriction instances already assert exactness
  separately; the theorem also asserts additivity and finite exactness of their composite.
- `localIntegralScalarRealization` is constant module sheafification
  (`adicLisseConstantModules`), ordinary scalar extension (`completedAdicChange`) along
  the canonical `CompletedConstantReduction.base`, then actual slice restriction.
  It is T_U on objects and maps, not a chosen functor with unspecified action.
- The existential exactness witnesses occur in the conclusion, so they add no hypothesis.
  They allow the subsequent termwise induced derived functor to be written directly.
- K is in the unbounded derived category of actual B_X-module sheaves. P is a cochain
  complex of R-modules; `a b`, `P.IsStrictlyGE a`, `P.IsStrictlyLE b`, and `_hP` express
  boundedness and finite projectivity of every term. No boundedness/completeness is
  assumed for K. No assumption on dimension, residue characteristic or Noetherianity
  of either scheme appears.
- The given `α` identifies the exact derived restriction of K with the localization of
  the termwise T_U realization of P.
- For every `q : ℤ`, `Module.FinitePresentation R (P.homology q)` is the first conclusion.
  The second is `IsIso` of the explicit map
  F(H^q K) -> H^q(F_D K) -> H^q(Q(T_U P)) -> H^q(T_U P) -> T_U(H^q P).
  Its first arrow is `mapDerivedCategoryHomologyFunctorIso`; its middle arrow is
  cohomology of the supplied α; the remaining arrows are the localization homology
  comparison and `mapHomologicalComplexHomologyIso`. Hence it specifies the induced
  isomorphism rather than merely existence of unrelated isomorphic objects.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing the actual coefficient
  constructions in `CoefficientExtension` and the DVR theorem in `ExtensionIntegersDvr`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- Mathlib `ClosedImmersion`, `OpenImmersion`, `Immersion`: `IsClosedImmersion`,
  `IsOpenImmersion`, `IsImmersion` and its closed/open factorization.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  `proEtaleConstantInverseImageMap`, and the site/model module inverse image construction.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `overFunctor`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, homology.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, whose bounded finite-projective witnesses are
  written explicitly for the supplied P.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing sheaf
  tensor at independent site universes; ordinary change of rings is the recorded tensor.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`: `proEtaleRingModules` and actual
  `proEtaleRingModulePullback` with its additive/exactness instances.
- `Sheaf.Paper.AdicLisseModule`: `adicLisseConstantModules`, `adicLisseRingSystem`,
  `adicLisseCompletedRing`, `adicLisseForget`.
- `Sheaf.Paper.CompletedAdicCoefficientDatum`: `completedAdicChange`, characterized
  on objects and maps by the sheaf tensor scalar-extension witness.
- `Sheaf.Paper.CompletedConstantSheafReduction`: `CompletedConstantReduction.base`;
  the limit projections uniquely determine this base map.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: `localizedSystemRestriction`
  and its separate additive/exactness instances.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryHomologyFunctorIso`, with its chain-level normalization.
- The stated proof dependency modules are imported without `public`; generic exact
  functor factorization and complex homology are Mathlib declarations, not restated.

Edge cases inspected: empty schemes and empty/initial site objects; P=0; degrees outside
[a,b]; torsion cohomology of a nonzero perfect complex; q=0 and arbitrary negative q;
X=S and identity immersion; open and closed special cases; unbounded and noncomplete K.
Finite presentation concerns the scalar module even on an empty slice. No faithfulness
of realization is used, so the empty-slice case does not infer scalar finiteness from
sheaf finiteness. Instead finiteness follows from the Noetherian scalar ring and finite
terms. No claim of global constructibility is included.

Sources read: blueprint main-20261015, sk-lem-integral-models, the stacks comparison
proof; Stacks proetale.tex lemma-closed-immersion (09AA), sites-modules.tex
lemma-constant-exact (093J) and lemma-completion-flat (093M).

Searches actually run via msearch.py:

- leanfinder: "Cohomology of a bounded finite projective scalar complex under completed
  constant sheaf extension and locally closed pro etale restriction is finitely
  presented". Eight generic finite-presentation hits, no match for this statement.
- loogle: "CategoryTheory.Functor.mapDerivedCategory, DerivedCategory.homologyFunctor".
  Zero hits.
- grep: "local.*integral.*perfect|completed.*cohomology". Zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, localIntegralPerfect,
  local_integral_perfect and completed cohomology. Related completed coefficients
  and constructible pullback interfaces found, but no statement of this node.
- Further rg searches identified the already existing canonical base map, actual
  pullback and slice restriction, so no second construction of any of these was made.

No statement correction or disputed mathematical assertion is proposed.

## Second reading by Q84

Self-audit of the statement, not an independent agent review (the dispatch brief forbids
starting agents). The correspondence above was checked against the full node statement
and the relevant dependency sources. Exactness is asserted, not added as a hypothesis;
canonical quotient projections and the explicit cohomology map retain the specified
objects and map. Independent maintainer review remains required. The resumed audit also checked every
statement dependency against its current record and source, the direction and normalization
of `mapDerivedCategoryHomologyFunctorIso`, and the closed/open factorization of
`IsImmersion`. No mathematical mismatch was found. The compiler exposed an ambiguous
auxiliary universe in slice restriction; both helper abbreviations now explicitly use
`localizedSystemRestriction.{u + 1, u, 0}`. This retains the site object universe u+1,
its morphism universe u, and the coefficient universe u+1. It imposes no equality between
the site universes and changes neither the statement nor any coefficient construction.


## Validation

The saved packet was retained. The initial required delivery dry run failed before
elaborating this module because compiled artifacts were absent from the published
dependency closure. Explicit private imports of the reported dependencies let the
prescribed wrapper rebuild the required artifacts. Those imports introduce no declarations
or additional hypotheses. No live source, build artifact, or launcher tool was edited.

After the universe repair, `scompile.py Q84
lem-sfb-local-integral-perfect-model-cohomology
lean/Sheaf/Paper/LocalIntegralPerfectModelCohomology.lean` succeeded in the sandbox
(12.4 seconds) and library (6.2 seconds) contexts, with no errors or warnings.
The packet node differs from the current shared node only in `lean`; all Lean lines
are at most 100 characters. The theorem remains the single postponed proof.

The final `deliver2.py --no-push` passed the maintainer preflight and per-file
compilation (dry-run commit df55b1818f3). The final self-check confirmed that the
recorded signature is verbatim and no field outside `lean` changed.
