## Worker report

This delivery defines both tensor-form `smoothPurityTensorMap` and the three-factor
`smoothPurityMap` in `Sheaf.Paper.SmoothPurityMap`. I read the current DAG statement,
its fourteen statement dependencies and their recorded interfaces, the master
order-2012 definition, the main-20261015 order-2356 definition, and the node's
blueprint-update/review note. The latter requires retaining both composites.
There is no statement correction and no disputed statement.

Hypotheses and clauses:

- `P : PurityFiniteSetting.{u}` is the recorded global finite-field datum, prime
  different from the characteristic, finite coefficient extension in the fixed
  algebraic closure, positive quotient level, and the actual quotient coefficient
  ring. `P.Ring` is the quotient and `P.Coefficient` is its standard universe lift.
  The quotient-finiteness instance uses the existing theorem, including every
  positive level; no ramification-index divisibility is assumed.
- The `X.Over` and `Y.Over` instances give the k-structures. Their
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure-map instances
  express exactly the separated finite-type k-scheme hypotheses of this node.
- `f.IsOver` gives k-linearity. `IsSeparated f`, `LocallyOfFiniteType f` and
  `QuasiCompact f` express separated finite type. `d : ℕ` and
  `SmoothOfRelativeDimension d f` express smoothness of pure nonnegative relative
  dimension. No smoothness or dimension is imposed on the base structure map.
- The original input is `K : Scheme.proEtaleDerivedCategory Y P.Ring`, with the
  recorded `finiteTorConstructible ... Y K` hypothesis. This is the intrinsic
  bounded constructible finite-Tor category, not a mere etale-origin replacement.
  `sfIntrinsicDerivedEquivalence` changes the coefficient presentation canonically;
  the output is realized back in the same intrinsic category on X.
- `smoothPurityPullback` is the published exact fixed-scalar inverse image, which
  is the finite-level derived pullback. `smoothPurityExceptional` uses the
  dependency's actual `sfFiniteExceptionalAt` with its specified compactification.
  `smoothPurityExceptionalOver` supplies compactifiability by Nagata from the
  existing finite-type field hypotheses, without adding a compactification input.
- `diagonalDualizing` is the dependency's actual exceptional image of the
  coefficient unit. `diagonalDualizingObject` is precisely the uniquely normalized
  diagonal isomorphism Pi, including its specified coordinate/counit normalization.
  The code uses its inverse, not an arbitrary isomorphism between the endpoints.
- `smoothPurityTheta` uses the recorded canonical tensor mate
  `Etale.dualizingComplexTensorMap`. It first compares pullbacks and tensors,
  inserts the diagonal unit comparison, inserts the canonical
  `singleFunctorObjUnitIso` between the degree-zero coefficient unit and the
  monoidal unit, then uses the published `Etale.derivedTensorSymmetry` and the canonical mate.
  `smoothPurityPullbackComparison` and `smoothPurityExceptionalComparison` expose
  the existing pullback and exceptional-transport identities. Finally the
  comparison adjunction unit and the representative isomorphism put its target
  in the actual transported exceptional image of the original K. This is clause 2
  of the recorded cohomological-smoothness definition in fixed-ring coordinates.
- `smoothPurityTensorMapInPresentation` is literally tensor of the inverse Pi
  followed by this theta. The normalization theorem states equality with this
  explicit morphism for EVERY etale representative and EVERY representing
  isomorphism. Its unique solution defines `smoothPurityTensorMap`; callers
  supply only the original K and its finite-Tor condition, not a representative.
  This is the allowed use of a unique-object theorem: the postponed theorem
  determines the morphism itself by the displayed formula, rather than supplying
  unspecified data from a bare existence of an endpoint isomorphism. It is a
  well-definedness obligation for this node's very composite, with a full proof
  docstring, not a new independent mathematical notion.
- The recorded `diagonalTwist X d` is A_X(d)[2d], constructed from ordered shifted
  roots-of-unity lines. Its inverse shift by 2d is the canonical presentation of
  the unshifted A_X(d); this uses the inverse equivalence of the shift functor and
  chooses no line or orientation. `smoothPurityReassociation` uses tensor's
  second-variable shift comparison and cancellation of these opposite shifts.
  Its source is (M tensor A_X(d))[2d] and its target is M tensor A_X(d)[2d].
  The generic shift helper uses the upstream derived-category universe convention;
  its finite-module specialization preserves the original small-site sizes.
- `smoothPurityMap` first applies that tau and then `smoothPurityTensorMap`, so its
  arrow order is exactly tau, 1 tensor Pi inverse, theta. The public map and tensor
  form live in D(X_proet,A), with the actual small-site universes unchanged.

Recorded dependencies used include:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `.Ring`, `.Coefficient`.
- Mathlib `FiniteType`, `Proper`, `Smooth`, `Proetale`: the recorded finite-type,
  separatedness, smooth relative dimension and small pro-etale-site notions.
- `Sheaf.Paper.FixedFinitePositiveCoefficientTwist`: `diagonalTwist`.
- `Sheaf.Paper.PurityDiagonalDualizingObject`: `diagonalDualizing`,
  `diagonalDualizingComparison`, `diagonalDualizingObject`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`, which uses the
  recorded intrinsic finite-torsion constructibility predicate.
- The finite parts reexported by `DerivedPullbackTensorHom` and its coefficient
  presentation: `sfIntrinsicDerivedEquivalence`, `sfFixedDerivedPullback`,
  `sfDerivedComparisonPullbackIso`, and the K-flat derived tensor. `smoothPurityTensor` only caches the fixed-module
  instances of that existing bifunctor; it supplies no new tensor product.
  `smoothPurityComparisonTensor` similarly specializes the recorded monoidal
  comparison, using finiteness to provide Noetherianity internally.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`:
  `dualizingComplexTensorMap`, the exact mate used by
  `CohomologicalSmoothnessComparison.comparedTensorClause`. The cohomological
  smoothness theorem gives its invertibility on this smooth finite-Tor domain;
  the definition of a morphism needs its actual data rather than a new proof of
  invertibility. The legacy pro-etale comparison import is omitted because it
  duplicates the finite-coefficient comparison declarations already required by
  the diagonal interface. The canonical ordinary tensor mate is imported directly.
- The finite `ComparisonMonoidal` module supplies the canonical derived
  comparison of tensor products; `DerivedCategory.Monoidal.Shift` supplies the
  K-flat-normalized shift comparison used in tau.

Edge cases checked mathematically: d=0 (the empty ordered tensor and shift zero),
K=0, the empty source or base scheme, every n>=1 including ramified levels not
multiple of the ramification index, and arbitrary allowed site/coefficient sizes.
The formulas use only functorial unit, tensor and shift constraints in these cases.
They do not choose a generator of the Tate line or alter the finite-field datum.
The three `sorry`s are named proof obligations: unique-presentation well-definedness
for gamma, the identity `smoothPurityTensorPresentation` between the published
bifunctor and its monoidal presentation, and `existsUnique_smoothPurityTensorShift`.
The last specifies equality of the whole isomorphism, across its interface types,
with the concrete `smoothPurityTensorShiftGeneric`, which is built from the existing
`DerivedCategory.commShiftTensorLeft` and cancellation of shifts. It therefore
fixes the map itself. Its proof rewrites the tensor presentation and uses reflexive
heterogeneous equality; uniqueness follows from transitivity of that equality.
The natural-language proofs are in the theorem docstrings. No data are taken from
bare existence or a Nonempty isomorphism. The selected maps are fully determined
by their explicit displayed constructions.

Validation: scompile.py checked the complete module cleanly as both sandbox (8.9 s)
and library module (9.6 s), under the unchanged 60-second per-file limit. No compiler
warnings or errors remained. The tensor and shift aliases cache the existing
instances; no alternative categorical structure is introduced.

Searches actually run with msearch.py (Q61/item logging):

- LeanFinder: "smooth purity map derived pullback Tate twist shift exceptional
  inverse image tensor diagonal orientation": eight unrelated hits; no match.
- Loogle: "dualizingComplexTensorMap, diagonalDualizingObject": zero hits and
  unknown identifier dualizingComplexTensorMap in the Mathlib-only service.
- Mathlib grep: "smoothPurity|purityMap|diagonalDualizingObject": zero hits.
- LeanSearch: "canonical smooth purity map tensor inverse diagonal orientation
  exceptional inverse image": eight unrelated tensor/diagonal hits; no match.
- rg over upstream WeilConjectures and shared lean/Sheaf for smoothPurity,
  purityMap, this node id, dualizingComplexTensorMap and tensorObjShift. Read
  upstream EtaleCohomology/Purity/Smooth/Basic.lean: `smoothPurityIso` takes
  arbitrary orientation/tensor isomorphisms, and uses the etale category; its
  docstring explicitly says the canonical maps are unavailable there. It cannot
  be attached as this canonical pro-etale construction. The shared diagonal
  and canonical tensor interfaces, including the newer dependency repairs, are
  used instead. Also searched `dag/lean_names_upstream.json`; no exact binding.

## Second reading by Q61

Independent reading by the maintainer's reviewer (the delivered section was the
worker's own self-reread, H11; it is replaced by this reading). Node statement
(master order 2012 / main-20261015 order 2356) against `Sheaf.Paper.SmoothPurityMap`:

- Finite datum (p,a,q,k0,k), l != p, E/Q_l, n >= 1, Lambda = O_E/varpi^n:
  `P : PurityFiniteSetting.{u}`, `P.Ring`/`P.Coefficient`; finiteness by
  `Padic.finite_coefficientExtensionRing` for every positive level. Correct.
- X, Y separated finite-type k-schemes: `X.Over`/`Y.Over` with `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated` of the structure maps. Correct, nothing stronger.
- f separated, finite type, k-morphism, smooth of pure relative dimension d >= 0:
  `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`, `d : ℕ`,
  `SmoothOfRelativeDimension d f`. Correct.
- K in D^b_ctf(Y_proet, Lambda): `K : Scheme.proEtaleDerivedCategory Y P.Ring` with
  `finiteTorConstructible ... Y K` (= intrinsic bounded constructibility ⊓ finite
  Tor amplitude, the recorded def-weil-finite-tor-amplitude declaration). Correct.
- M = Lf^*K: `sfFixedDerivedPullback P.Ring f` of the realization of K. Correct.
- omega_f = Rf^! Lambda_Y: `diagonalDualizing f` = `sfFiniteExceptionalAt` (recorded
  def-weil-exceptional-inverse-image) of the comparison image of the degree-zero unit;
  compactification by Nagata from the finite-type field hypotheses. Correct.
- Pi_f: `diagonalDualizingObject d f aY` (recorded thm-pur-diagonal-dualizing-object,
  the uniquely normalized iso omega_f ≅ diagonalTwist X d); the composite uses `.inv`,
  the direction 1 ⊗ Pi_f^{-1}. Correct.
- theta_{f,K}: comparison of pullback and tensor, ν^* of [unit iso Rf^!(Λ)→Rf^!(𝟙),
  `Etale.derivedTensorSymmetry`, `Etale.dualizingComplexTensorMap` (transpose of
  projection-map inverse, counit, left unitor = clause 2 of def-pur-co-smoothness)],
  then the comparison adjunction unit and e into the recorded exceptional image of K.
  This is the same map whose ν^*-image `comparedTensorClause` (recorded Lean of
  def-pur-co-smoothness, used by thm-pur-cohomological-smoothness) asserts invertible.
- tau: `smoothPurityReassociation` = second-variable tensor-shift compatibility
  (`DerivedCategory.commShiftTensorLeft`) followed by cancelling T[-2d][2d], with
  T = `diagonalTwist X d` = Λ(d)[2d] and Λ(d) presented as T[-2d]. I checked by compile
  that `ProEtale.derivedTensor C X = curriedTensor _` holds by `rfl` and that
  `smoothPurityTensorShiftGeneric` itself witnesses the HEq existence with `HEq.rfl`,
  so `existsUnique_smoothPurityTensorShift` is true and selects exactly that iso.
- gamma^sm and gamma: `smoothPurityTensorMap` is the unique g equal to
  (1 ⊗ Pi^{-1}) ≫ theta in every étale presentation (K0, e); presentation
  independence holds by naturality via the canonical presentation Rν_*K (counit
  invertible since K has a bounded étale representative), so the ∃! theorem is true
  and its data is not hollow. `smoothPurityMap` = F(tau) ≫ gamma^sm. Arrow order
  tau, 1 ⊗ Pi^{-1}, theta. Correct.

Edge cases: d = 0 (T = degree-zero unit, shift 0), K = 0, X or Y empty (hom sets
subsingleton, all ∃! still hold), n = 1 and ramified levels, universes: everything in
the recorded universe u / u+1 of the dependencies, generic helpers universe-polymorphic.
Searches: rg for smoothPurity/purityMap/dualizingComplexTensorMap in shared lean/Sheaf
and upstream WeilConjectures: only this module and the recorded dependencies.
Statement field verbatim; 23 declarations all listed; lines ≤ 95 chars; only the
item's `lean` field changed. nt_compile: module clean (6.7 s), no error or warning.
Change made: this section only.
