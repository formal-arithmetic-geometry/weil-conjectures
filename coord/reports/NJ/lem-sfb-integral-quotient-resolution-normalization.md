## Worker report

The module `Sheaf.Paper.IntegralQuotientResolutionNormalization` states
`AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_resolution_normalization`.
Its only postponed proof is this theorem. The five abbreviations expose the existing
section-ring reconstruction, underlying ring sheaf, finite section ring, fixed
internal/section equivalence, and constant integral ring. They construct no replacement
coefficient, map, module category, tensor, or resolution.

The live stage-1 split was read in full. This delivery preserves its statement, proof,
proof dependencies and all other fields, adding only `lean` and four already-landed
statement dependencies used for canonical maps. No stage-1 split is attempted.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is
  `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  `Padic.coefficientExtensionIntegers l E` is the recorded valuation subring, already
  a commutative ring; `Padic.coefficientExtensionUniformizer l E` is its recorded
  chosen uniformizer. No extra ring, uniformizer, DVR or finiteness hypothesis is added.
- A positive integer `j` is indexed by `n : ℕ` with `j = n + 1`. This covers exactly
  all exponents at least one. The first conjunct is `IsNoetherianRing A`; the following
  universal clause states `pi^(n+1) ≠ 0` and `Finite (coefficientExtensionRing ... (n+1))`.
- The scalar finite free resolution is written as `Function.Injective` of
  `a ↦ pi^(n+1) * a`, `Function.Exact` of this map followed by the actual
  `Ideal.Quotient.mk (coefficientExtensionIdeal ... (n+1))`, and surjectivity of that
  quotient. Both terms are literally `A`, with its regular action, so these are free
  modules of rank one and the sequence is precisely the displayed resolution in
  degrees -1 and 0. This does not replace the resolution by an arbitrary perfectness
  assertion or a choice of free modules.
- Every scheme is quantified as `∀ T : Scheme.{u}`; the site is exactly
  `Scheme.ProEt.topology T`, with site objects in `Type (u+1)` and arrows in `Type u`.
  Abelian sheaves and ring sections use universe `u+1`. No site-universe equality,
  qcqs, nonemptiness, boundedness, completeness or geometric hypothesis is imposed.
- `condensedRingObj (integral l E) T` is the existing pulled-back continuous integral
  ring. `condensedRingObj (finite l E n) T` is the existing actual pulled-back finite
  quotient. `coefficientMap (reduction l E n) T` is the actual map q, not an arbitrary
  map to an abstract quotient. `projection` is its scalar-restricted regular-module
  map, and `multiplication` is multiplication by the actual uniformizer power.
- `α` is a ring-sheaf isomorphism from the reconstructed section ring of the integral
  coefficient to `completedIntegralCoefficientSheafUnrestricted`. The latter is
  definitionally the limit of `integralCoefficientSheafSystem`, the positive tower of
  constant finite quotient ring sheaves with the actual quotient transitions.
- For each level, `c n` identifies the finite reconstructed ring with the constant
  finite quotient. The first condition, evaluated on every site object and every
  residue class `a`, says its inverse takes the constant sheafification unit of `a`
  to the existing `FiniteDiscreteOrdinary.canonicalAbelianMap` applied to the same
  class. This pins the finite identification to constant functions and rules out
  changing it by a finite-ring automorphism.
- The next condition is the exact equation
  `α.hom ≫ limit.π ... (op n) = sectionScalarMap q ≫ (c n).hom`, after forgetting
  commutativity. It identifies every actual finite projection, not just the objects.
  Since the finite identifications are normalized and limit projections are jointly
  monic, this specifies the canonical limit isomorphism uniquely.
- Flatness over the constant integral ring is `SheafOfModules.IsFlatOnSite` of the
  section regular module restricted along
  `integralConstantToCompletionOfUniverses ... ≫ α.inv`.
  The former map is the existing limit lift of actual constant quotient reductions.
  The projection equations and normalized `c n` identify this transported scalar
  structure with the canonical constant-scalar structure on R: at each finite
  projection a constant `a` maps to the same residue of `a`. Thus the scalar structure
  is fixed, rather than supplied as an arbitrary algebra map or an extra hypothesis.
- Injectivity is `Mono (multiplication ...)`. The actual quotient assertion is the
  existence of its zero-composite proof and the cokernel universal property
  `Nonempty (IsColimit (CokernelCofork.ofπ (projection ...) h))`. Together these say
  that the actual q induces `R/pi^j R ≅ S_j`. The section version is the short
  exactness of precisely this short complex mapped by `resolutionSectionEquivalence`.
- `resolution l E T n` is the existing cone on multiplication on the degree-zero
  regular module. It is the displayed two-term complex with differential `+pi^j`
  in degrees -1 and 0; its existing definition is not changed. Flatness of every
  internal term is the exactness of `tensorRight` of that term. Internal K-flatness
  uses the existing `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat` predicate.
- The section terms satisfy the recorded `SheafOfModules.IsFlatOnSite`, and the
  termwise image of the very same cone satisfies the recorded
  `CochainComplex.IsKFlatIndependentCoefficients` predicate. The functor used is
  exactly `InternalAbelianSheafModule.sectionModuleEquivalence`.
- The final existential is an augmentation from the existing cone to the restricted
  regular quotient module in degree zero. Its equation with `mappingCone.inr` says
  that on the unshifted degree-zero ring summand it is exactly `projection[0]`.
  `QuasiIso ε` and `QuasiIso` of its termwise section image state both versions of
  the same quasi-isomorphism. There is no unspecified unit multiple, sign, or choice
  of a comparison in place of q. These are ordinary unbounded cochain complexes;
  their quasi-isomorphisms become isomorphisms under the ordinary `DerivedCategory.Q`.
  No completion of that derived category is used or assumed.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting
  `Sheaf.NumberTheory.Padics.CoefficientExtension` and its integer ring, uniformizer,
  ideals, quotient rings and transitions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `AlgebraicGeometry.Scheme.ProEt.topology`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.condensedRingObj`, `coefficientRing` and the
  commutativity instance; imported through the coefficient dependency.
- `Sheaf.Paper.IntegralQuotientCoefficients`: `integral`, `finite`, `reduction`,
  `multiplication`, `resolution`, `projection`, their supporting structures and maps.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.regular`, `Mod.comap`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and its ordinary
  quasi-isomorphism localization; no derived-category existence assumption is needed
  for this statement about complexes.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` and the exposed `CategoryTheory.exactFunctor`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its public import exposing
  `CategoryTheory.MorphismProperty.kFlat` (specialized here to quasi-isomorphisms).
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionRingSheaf` and `sectionModuleEquivalence` in namespace
  `CategoryTheory.InternalAbelianSheafModule`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.limit`, `limit.π`;
  `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`. The size-convention dependency is rendered by
  explicit universes, without a second object or predicate.
- Added existing statement dependency `def-weil-completed-integral-coefficients`:
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `WeilConjectures.integralConstantToCompletionOfUniverses`, with the recorded
  completed limit, tower and finite constant ring sheaves it reexports.
- Added existing statement dependency `def-pe-finite-discrete-presentation-encoding`:
  `Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`,
  `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.canonicalAbelianMap`.
- Added existing statement dependency `def-sfb-section-scalar-map-data`:
  `Sheaf.CategoryTheory.InternalSectionScalarAdjunction`,
  `CategoryTheory.InternalAbelianSheafModule.sectionScalarMap`.
  This is the landed definition node owning the plain definition; the adjunction
  theorem is neither used nor chosen to construct this map.
- Added existing statement dependency `def-sfb-coefficient-map`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`,
  `AlgebraicGeometry.ProEtale.coefficientMap`. Its definition is
  `(upperStarFromPoint T).map a`, so `coefficientMap (reduction l E n) T` is the
  actual pulled-back quotient arrow.
  These four dependencies already have landed declarations. A read-only traversal
  of their statement/proof dependencies found no path back to this item.

The proof dependency imports follow the six-step proof in the live node, including
`ExtensionIntegersDvr`, the Mathlib PID and finite-valued-quotient results,
`IntegralNormalizedRestrictionSquares`, `IntegralPresentationEncoding`,
`ConstantCompletionEquivalence`, `FlatScalarCyclicResolution`,
`FiniteFreeMonoCokernelKFlat` and `InternalSectionTensorComparison`.
The theorem docstring spells out all six steps. The blueprint integral proof
paragraph (1) and Stacks `lemma-completion-flat` (093M), `lemma-constant-exact`
(093J) and `lemma-bounded-flat-K-flat` (06YQ) were opened and read.

Edge cases checked: level `n=0` is exponent one, and exponent zero is deliberately
outside the original claim. There is no assumption that T is nonempty; for the empty
scheme the zero regular module and its identity quotient satisfy the corresponding
categorical mono/cokernel and resolution conditions. The identity extension E=Q_l,
all primes including 2, arbitrary finite extensions and arbitrary schemes are included.
No sectionwise surjectivity of q is asserted: a sheaf cokernel is used, as required.
Flatness is over constant A, while flatness of the two terms is over R, as in the node.

Searches actually run with `msearch.py NJ lem-sfb-integral-quotient-resolution-normalization`:

- `leanfinder`: "The actual finite quotient map of pulled back condensed integers has
  a two term flat K-flat resolution and inverse limit presentation". Eight hits,
  including condensed free-module functors and AB4 properties; no whole-statement match.
- `loogle`: `"IsNoetherianRing", "mappingCone", "QuasiIso"`. Zero hits.
- `grep`: `mappingCone.*[Rr]esolution|integral.*quotient|uniformizer` in
  `Algebra/Homology`. Zero hits.
- `leansearch`: "The inverse limit of constant finite uniformizer quotients is flat
  and the actual projection has a two term K-flat resolution". Eight hits, including
  `AdicCompletion.flat_of_isNoetherian` and profinite limit descriptions. None states
  the sheaf theorem with its actual pulled-back quotient and both module presentations.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for integral quotient,
  resolution, uniformizer and normalization names. Existing arithmetic, scalar cyclic
  resolution, finite free cokernel and continuous coefficient comparisons were found
  and reused. `IntegralQuotientDirectImageComparison` includes the augmented cone
  clause, but also different direct-image data and omits this item's arithmetic,
  canonical limit identification, constant-scalar flatness and quotient assertion;
  it is not an exact existing match for the item. Searching the item id in
  `lean/WeilConjectures` returned no declaration. The proposed declaration and helper
  names have no existing project match.

No new nodes, dependency modules, statement correction, disputed statement, or known
node fault is present. The finite and integral isomorphisms in the theorem are
normalized conclusions, not hypotheses replacing the canonical constructions.

## Repair of returned delivery

The immutable-head review at `f4920bdbce7f` returned one H2 dependency-ownership
fault. Replaced `lem-sfb-internal-section-scalar-adjunction` in `stmt_deps` with
`def-sfb-section-scalar-map-data`, whose landed `existing: true` record owns
`CategoryTheory.InternalAbelianSheafModule.sectionScalarMap`. Also followed the
advisory by citing `def-sfb-coefficient-map` for the actual coefficient arrow.
Opened both owning node records and the definitions with their docstrings.
The module and its entire Lean record are unchanged. Compared the retained packet
with current main: only the authorized `stmt_deps` and `lean` fields differ.

## Second reading by NJ

Repair self-check with the node and module open: the binders still cover a prime,
a finite extension, every scheme, and all positive exponents through `n + 1`.
The arithmetic conjuncts assert Noetherianity, nonzero uniformizer powers, finite
quotients and the exact rank-one scalar resolution. The normalized finite maps
and limit-projection equation fix the actual quotient arrow. Constant-A flatness
uses the canonical limit lift followed by `α.inv`; this and `α` are section-side
assertions. The monomorphism, actual cokernel and mapped short exact sequence,
both flat-term and K-flat assertions, and augmentation with precisely the actual
projection as its degree-zero component retain all the reviewed clauses.
Both quasi-isomorphism assertions concern the same augmentation. Exponent one,
the empty scheme, the identity extension and the prime two remain covered.
The dependency repair changes ownership citations only: `sectionScalarMap` is a
plain definition, with no `.choose` of the adjunction theorem, and `coefficientMap`
is the recorded pullback of the actual reduction. No mathematical mismatch was
found in this repair self-check; the maintainer's independent immutable-head
review had already accepted all statement clauses.
