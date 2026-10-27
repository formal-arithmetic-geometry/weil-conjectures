## Worker report

The module `Sheaf.RingTheory.FinitePresentationFieldExtensionNeighbourhood` states
`AlgHom.exists_finitePresentation_away_of_fieldExtension`, with `sorry` as its
entire proof. No definitions, helper theorems, new nodes, dependency repairs, or
statement corrections are introduced. The copied node differs only in `lean`.

I read the item's full statement, source, all six proof steps, statement
dependencies and proof dependencies. I read each statement dependency's recorded
declaration and docstring in the source. I also read the source statements at
Stacks `varieties.tex`, label `lemma-change-fields-flat` (Tag 0C4Y), and
`algebra.tex`, label `lemma-finite-presentation-independent` (Tag 00R2). The node
is explicitly an agent-written conditional consequence, not a claim that 0C4Y
itself states finite-presentation neighbourhood descent. I read the current
blueprint's `lem-sc-mult-n-etale-kernel` statement and proof in
`literature/blueprint/latest/blueprint/sec-abelian-varieties/sk-prop-av-ntorsion-etale/`.
Its geometric-fibre argument provides the recorded ancestor context; no unit
statement or proof is changed.

Clause-by-clause correspondence:

- The field `k`, extension field `K`, and specified extension map are
  `{k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]`.
  There is no algebraicity, finiteness, separability or characteristic condition.
- The rings `A` and `B` and their given `k`-algebra structures are
  `{A : Type w} {B : Type z} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]`.
  The specified homomorphism is `(α : A →ₐ[k] B)`. No independent `A`-algebra
  structure on `B`, and therefore no extra compatibility hypothesis, is imposed.
- Every `C_K` and `B_K` is the actual Mathlib tensor product, `C ⊗[k] K`
  and `B ⊗[k] K`. The canonical inclusion `b ↦ b ⊗ 1` is
  `algebraMap B (B ⊗[k] K)`, and similarly for `C`.
- The neighbourhood-surjectivity principle explicitly assumed by the node is
  the hypothesis `hdescent`, not omitted because its dependency is already a
  theorem. It quantifies `C`, its commutative ring and `k`-algebra structures,
  arbitrary additive groups `M N` with `C`-module structures, and the linear map
  `(φ : M →ₗ[C] N)`. It includes no finite-generation or finite-presentation
  assumption on `C`, `M` or `N`.
- In that principle, `(v : C ⊗[k] K)`, `(P : Ideal (C ⊗[k] K)) [P.IsPrime]`
  and `v ∉ P` state exactly the upstairs element, prime and exclusion. The
  next implication is surjectivity of
  `LocalizedModule.map (Submonoid.powers v) (φ.baseChange (C ⊗[k] K))`.
  Its conclusion is `∃ d : C, algebraMap C (C ⊗[k] K) d ∉ P ∧` surjectivity
  of `LocalizedModule.map (Submonoid.powers d) φ`.
- This is the exact scalar-extension interface of the recorded dependency
  `LinearMap.exists_localizedMap_away_surjective_of_fieldExtension`.
  For `S = C ⊗[k] K`, it represents `M ⊗[k] K` by `S ⊗[C] M`; the canonical
  identification sends `(c ⊗ λ) ⊗ m` to `(c • m) ⊗ λ`, with inverse sending
  `m ⊗ λ` to `(1 ⊗ λ) ⊗ m`. It respects the `S`-action, and `φ.baseChange S`
  sends a pure tensor to the tensor with `φ m`, so it is precisely `φ ⊗ id_K`
  under that identification. The same identification commutes with localization.
  No arbitrary map, selected isomorphism or new scalar-extension notion is used.
- The test rings and modules in `hdescent` have universe `max u v w z`, a common
  universe at least as large as the input rings and both fields. Thus the
  quantification is not vacuous, and permits lifted arbitrary test modules with
  no rank restriction. Polynomial rings on finitely many variables over `A`,
  their relation ideals and finite free modules can all be transported to this
  universe by `ULift`. This is the standard common-universe rendering of the
  node's universally quantified principle, not a smallness hypothesis on the
  inputs; `u`, `v`, `w` and `z` remain independent.
- The specified prime upstairs is `(qK : Ideal (B ⊗[k] K)) [qK.IsPrime]`.
  The node's `q` is auxiliary notation for its contraction. Its only occurrence
  in the assertion is `s ∉ q`, rendered without an additional prime parameter as
  `algebraMap B (B ⊗[k] K) s ∉ qK`. This is definitionally the contraction condition.
- `(u : B ⊗[k] K) (hu : u ∉ qK)` retains the chosen principal neighbourhood.
- `(hfinite : α.toRingHom.FiniteType)` is exactly finite type via `α`, using the
  dependency's recorded `RingHom.FiniteType`.
- `(Algebra.TensorProduct.map α (AlgHom.id k K)).toRingHom` sends
  `a ⊗ λ` to `α a ⊗ λ`, hence is the node's `α ⊗ id_K`.
  Composing it with `algebraMap (B ⊗[k] K) (Localization.Away u)` gives exactly
  the structure map `A_K → (B_K)_u`. Its `RingHom.FinitePresentation` is `hfp`.
  Mathlib defines `RingHom.FinitePresentation f` as the recorded
  `Algebra.FinitePresentation` for `f.toAlgebra`; this is just the existing
  predicate on the specified map, with no second definition.
- The conclusion `∃ s : B, ... ∧ ...` gives the downstairs element, exclusion
  from the contracted prime, and finite presentation of the composite
  `(algebraMap B (Localization.Away s)).comp α.toRingHom`. This is precisely
  `B_s` as an `A`-algebra via `α`. No uniform neighbourhood or finiteness of
  `B` as a module is asserted.
- Every subscript localization uses the actual Mathlib construction
  `Localization.Away` for rings and `LocalizedModule.map (Submonoid.powers ...)`
  for module maps. These are localization at all nonnegative powers, as stated.

Dependency declarations used:

- `def-pc-field-extension`: `Algebra`, in `Mathlib.Algebra.Algebra.Defs`,
  specialized to fields. The source signature and its structure map were read.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and the bilinear `mk`
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`; `LinearMap.rTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.Map`. The canonical equivalent
  scalar-extension model uses `LinearMap.baseChange` from
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, exactly as its recorded consumer
  module does; that definition and pure-tensor formula were read.
- `def-weil-pbc-module-localization`: `LocalizedModule` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, its fraction description,
  and the module-map interface re-exported through
  `Mathlib.RingTheory.Localization.Module`.
- `lem-sc-module-surjectivity-field-extension-neighbourhood`:
  `LinearMap.exists_localizedMap_away_surjective_of_fieldExtension`, in
  `Sheaf.RingTheory.ModuleSurjectivityFieldExtensionNeighbourhood`. I read its
  full signature and docstring. The new module publicly imports it, and the
  explicit assumed assertion `hdescent` uses the identical constructions.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`, in
  `Mathlib.RingTheory.FiniteType` (publicly imported by `FinitePresentation`).
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`, with
  its existing `RingHom.FinitePresentation` wrapper, in
  `Mathlib.RingTheory.FinitePresentation`.

The plain proof imports retain the node's stated proof dependencies:
`Mathlib.Algebra.MvPolynomial.Basic` for `MvPolynomial`;
`Mathlib.RingTheory.Flat.Basic` for flatness of vector spaces and
`Module.Flat.lTensor_exact` / `rTensor_exact`;
`Mathlib.RingTheory.MvPolynomial.Localization` for
`IsLocalization.Away.mvPolynomialQuotientEquiv`;
`Mathlib.RingTheory.Localization.Ideal` for the localization-of-quotient
instance. `Algebra.FinitePresentation.ker_fg_of_mvPolynomial` is already in
its public finite-presentation import. These declarations and source signatures
were inspected. The module's theorem docstring gives all six proof steps,
including finite extraction of relations and application of the assumed
principle to the map from a finite free module to the relation ideal.

Edge cases checked before writing:

- `K = k` is allowed; the theorem becomes ordinary localization descent along
  the identity extension. No nontrivial-extension assumption is present.
- `B = 0` has no prime `qK`, as appropriate. No unnecessary nonzero instance
  on `A`, `B` or a test ring was added.
- `u = 0` is excluded by `hu`, since zero belongs to every ideal. If `u` is a
  unit, the upstairs hypothesis is global finite presentation, an allowed case.
- Zero modules and the zero linear map are allowed in `hdescent`, and arbitrary
  infinitely generated modules are included. A map to zero is surjective and
  can use `d = 1`, consistent with the prime exclusion.
- Presentations with zero variables or zero relations, and free source module
  of rank zero in the proof, are not excluded by any binder.
- Arbitrary characteristic and nonalgebraic field extensions are included.
- Independent universe sizes for `k`, `K`, `A`, `B` are retained; test objects
  occupy a common upper universe and cannot disappear because the base field
  is larger than the universe of quantification.

Searches actually run with `msearch.py Q56` for this item:

- `leanfinder`: `For a finite type algebra, finite presentation after a field
  extension on a principal open descends near the contracted prime`.
  Eight hits: localization preservation, localization spanning covers,
  essential finite type, and restriction of scalars. None is this conditional
  neighbourhood descent statement.
- `loogle`: `Algebra.FinitePresentation, Localization.Away`.
  Eleven hits, including `instFinitePresentationAway`,
  `Algebra.FinitePresentation.of_span_eq_top_target` and its auxiliary result,
  plus smooth/etale locus results. These assume finite presentation before
  localization or a spanning family; none gives the item's assertion.
- `grep`: `finitePresentation.*(desc|local|tensor)|FinitePresentation.*(desc|local|tensor)`
  in `RingTheory`. Twenty-five hits, including
  `Mathlib/RingTheory/Finiteness/Descent.lean` and
  `Finiteness/FinitePresentationLocal.lean`. I read the global faithfully flat
  descent candidate: it assumes finite presentation of the entire scalar
  extension, not of a single principal open. The standard-cover candidate
  requires a spanning cover. Neither is an exact match.
- `leansearch`: `finite presentation descends to a neighbourhood after extension
  of ground fields`. Eight hits on base change, ring-map finite presentation,
  local properties and module finite presentation, with no exact match.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  finite-presentation neighbourhood names, and finite-presentation field-extension
  names found no existing statement. Nearby `IsEtaleAtFieldExtensionDescent`
  already assumes global finite presentation and is not this node. A name-clash
  search over Mathlib, both project library roots and `dag/lean_names_upstream.json`
  for `exists_finitePresentation_away_of_fieldExtension` found no declaration.

Validation: `scompile.py Q56` compiled the delivered file both as its sandbox
module and at its intended library module path, cleanly (1.7 and 2.4 seconds).
There were no errors or warnings. All variables and universes are explicit;
there is no `let`, local notation, local instance, private helper or proof
other than the single expected `sorry`. No statement dispute or node fault was
found. The requested example module has been withdrawn in the current tree;
its node now points to `WeilConjectures.CategoryTheory.CompactObject`, whose
full source was read for the current module/header convention.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
