## Worker report

Bind this node to the existing public theorem
`WeilConjectures.GeneratorReduction.primitiveReductionTranspose` in
`Sheaf.SixFunctors.GeneratorReductionStatement`, lines 635–644. No Lean module is added.
The declaration and its proof-plan docstring were read, together with the definitions
of its conclusion and all four coefficient arrows. The current server source was also
read using `scompile.py --source Sheaf.SixFunctors.GeneratorReductionStatement` and agrees
with the local source at these declarations. Its proof remains `sorry`, as stage 2 requires.

The node is the single-operation part of the already stated generator theorem. The
existing theorem states `B.primitiveFormulas ...` for `B.length ≤ 1`; instantiate `B`
with a tensor of two input leaves, a pull of one input, a proper push of one input,
or an open extension of one input. Leaves contribute `True` to the recursive predicate,
so there is precisely one nontrivial primitive formula. The extra zero-operation
cases of the word encoding are vacuous, not additional geometric assertions.

### Hypotheses and objects

- The global finite-field datum and coefficient choice are the existing
  `FiniteFieldDatum` and `FiniteFieldDatum.CoefficientDatum` from
  `Sheaf.Paper.FiniteFieldFiber`. Their fields fix `p,a,q,k₀,k`, the algebraic closure,
  the prime `l`, and `l ≠ p`. Finite-type schemes over `k` can be supplied using
  `GeneratorReduction.FiniteTypeFamily W D.k`, whose structure maps are locally of
  finite type and quasi-compact. As with the geometric operations themselves, the
  existing primitive theorem is stated in ambient schemes: its specialization to
  this fixed geometric context requires no change of any object or map. It does not
  assert a preservation result outside the domain in the node.
- The existing theorem's explicit coefficient arguments are `l`, `[Fact l.Prime]`,
  `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]`.
  The integer ring, chosen uniformizer, positive quotient rings and quotient
  homomorphisms are the constructions in `Sheaf.NumberTheory.Padics.CoefficientExtension`
  and `CoefficientExtensionFinite`. Every `n : ℕ` in the system means exponent `n+1`;
  no positive coefficient level is omitted.
- `W : S → Scheme.{u}`, `location : I → S`, and
  `K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))`
  give all input schemes and integral objects. The categories use the actual
  `Scheme.ProEt.topology`, completed coefficient sheaf, and vertical ringed sequence
  site. A strict-system derived object is `coefficientSequenceDerived l E X`, not
  a sequence of unrelated derived objects.
- `IntegralSystemRealization.calculus l E X` is the fixed
  `pullbackTensorCalculus`, chosen from the recorded coefficient evaluation calculus.
  Its `.reduction`, `coefficientSequenceLimit`, `.adjunction.unit`, and
  `.adjunction.counit` are exactly R, L, u and e. The reduction model retains one
  flat-term K-flat representative and its strict quotient transitions.
- `o : GeneratorReduction.Operations l E` packages presentations of the actual
  operations. Its `system` is the recorded `IntegralSystemRealization.Operations`;
  `ringed` is `RingedModels`; `realization` is `RealizationModel` from
  `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`. In particular the ordinary
  direct-image/limit comparison is fixed on projected sections, and the derived
  pullback comparison is fixed on whole good representatives. These are canonical
  construction data, not a hypothesis supplying the transpose equality to be proved.
  The composition, open and unit-normalization fields are the surrounding generator
  package; no generator arrow can be arbitrarily supplied.
- `Word.pull f hs ht hq B` binds `IsSeparated f`, `LocallyOfFiniteType f`, and
  `QuasiCompact f`. `Word.push` also binds `IsProper f`. `Word.open j hj hq B`
  binds `IsOpenImmersion j` and `QuasiCompact j`. These render exactly the map
  conditions relevant to each primitive. `Word.systemValue` uses exact system
  pullback, the universal right-derived direct image with its actual adjunction,
  exact system open extension with its open adjunction, and the closed derived tensor.
- `_hAdm` requires `Admissible` of every integral input. This expands to
  `finiteTorConstructibleIntegral` and `SystemAdmissible` of its reduction.
  The former includes `sfIntegralConstructible`, hence quotient-tower completeness
  and constructibility. The latter retains normalization, compatible etale origins,
  constructibility and support/Tor bounds at every positive level.
- `_hIntermediate` requires `Word.admissible` at every actual system vertex, using
  the same `lo hi torLo torHi : ℤ` as `_hAdm`. `SystemAdmissible` explicitly contains
  `lo ≤ hi`, `torLo ≤ torHi`, support contained in `Set.Icc lo hi`, and
  `HasProEtaleTorAmplitude ... torLo torHi`. Thus intervals are common to both
  tensor inputs and the output, as well as all unary inputs and outputs. Compatible
  origins are `Nonempty (IntegralSystemRealization.Origins ...)`, whose retained
  level antecedents, origin squares and transition squares were read. The theorem
  does not silently replace these by unconnected existential antecedents at each level.

### Each conclusion and its coordinates

1. **Tensor.** In the tensor branch of `Word.primitiveFormulas`, the asserted equality is
   `tensorR ... K L = calculus.reduction.map ((tensorD ...).inv.app (K,L)) ≫
   calculus.adjunction.counit.app (...)`. Here `tensorD` is the inverse of
   `pullbackTensorIntegralTensorModel`. The map `tensorR` is independently defined
   using the ordinary tensor reduction and inverse reduction of the actual
   completion unit, with the specified closed-tensor coordinate transport. It is
   not defined by the equality being asserted.
2. **Pullback.** The pull branch asserts the same equality with `pullR`, `pullD`,
   and the system pullback of the reduced input. `pullD` is the inverse of
   `pullbackTensorIntegralPullbackModel`. `pullR` uses inverse reduction of the
   actual quotient-completion unit followed by
   `o.realization.reductionPull f`; its whole-representative normalization is part
   of the recorded bridge, independently of `pullD`.
3. **Proper direct image.** The push branch asserts the equality with `pushR` and
   reduction of the identity of `integralPush`. The integral object is definitionally
   `R ⋙ S_p ⋙ L`, namely `integralSystemDerivedDirectImage`, so the specified defining
   `d_S` is identity in precisely these strict-system coordinates. `pushR` is the
   actual system counit. Its finite evaluations are scalar adjoints of the actual
   total-limit projections by `CoefficientDerivedSystemReduction.counit_projection`.
4. **Defining tower coordinates.** For tensor and pullback the above inverse `d` maps
   are the canonical Roos realizations, not unspecified endpoint isomorphisms.
   `pullbackTensorIntegralTensorModel_existsUnique` and
   `pullbackTensorIntegralPullbackModel_existsUnique` fix them on every good
   representative by the full strict finite-operation tower and its Roos comparison.
   The strict quotient transitions occur in `pullbackTensorTensorTower` and
   `pullbackTensorPullbackTower`. The calculus's `counit_projection` fixes the finite
   scalar-extension adjunct of the actual total-limit projection. Thus the
   coordinate description in the node is the normalization of these specified
   declarations, and is not a separate assertion identifying arbitrary arrows from
   equality of their evaluated images.
5. **Open extension.** The open branch asserts
   `openR = R.map openDInv ≫ e`, and both inverse laws for `openD` and `openDInv`.
   `openR` is the inverse of the actual inverse-open-adjunction mate
   `RealizationModel.openReduction`. `openD` is `L.map` of that mate followed by
   inverse of the actual reconstruction unit. In the theorem's complete domain
   these are the `r_j,d_j` of the recorded open comparison.
   The first requested displayed open equality is the literal definition
   `openDInv = u.app (ringedOpen.obj K) ≫ L.map (openR ... K)`;
   the inverse laws make this the inverse of the specified `d_j`. Substituting it
   in the asserted transpose equality and expanding `Functor.map_comp` gives
   exactly the second requested three-factor equation
   `R.map u ≫ R.map (L.map r_j) ≫ e = r_j`, with Lean's left-to-right composition.
   No replacement of the actual reconstruction unit by a freely chosen isomorphism occurs.
6. **Naturality and whole systems.** All equations in `primitiveFormulas` have Hom
   types in `coefficientSequenceDerived`; no finite evaluation is applied to their
   conclusions. Tensor's realization is a natural isomorphism in the product
   category, and pullback's is a natural isomorphism of unary functors. Completion
   units, reduction comparisons, proper counits and open mates are natural.
   `inverseOrZero` is used only to totalize inverses outside the admissible domain;
   on the stated domain these are the genuine inverses and inversion preserves
   naturality. Hence the equalities are natural in every input (separately in the
   two tensor slots). The existing proof docstring explicitly requires equality on
   strict representatives and excludes any use of derived evaluation faithfulness.

### Recorded dependencies read and reused

The following are the node's recorded interfaces (including their transitive public
constructions), not new private copies:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and `.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the imported ring/uniformizer/quotient data.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and `.topology`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, `CoefficientDerivedSystemReduction`,
  `CoefficientDerivedSystemCalculus`, and their fixed adjunction/projection/model fields.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearSections.semilinearDerivedSections`,
  with the actual simultaneous system-site calculus and adjunction normalization.
- `def-weil-scheme-morphism-properties` is explicitly a convention record with no
  declaration: use the Mathlib properties in `Word`'s constructors, as its note directs.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`,
  importing the global `integralCompletedTensor` and `integralDerivedPullback` used here.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage` and
  `sfDirectImageReductionComparison`; the existing generator module supplies the
  simultaneous strict-system coordinate presentation `integralSystemDerivedDirectImage`.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`:
  `IntegralOpenReduction.integralOpenReductionComparison`, its `Comparison`, `r`, `d`,
  actual-unit normalization and strict model; the generator module uses the
  canonical adjoint-normalized presentation of those same maps.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`; the whole semilinear-system
  formulation uses `IsNormalizedCoefficientSequence` of the evaluation calculus.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, used by `Origins`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`, publicly
  importing `finiteTorConstructibleIntegral` and the pro-etale Tor-amplitude definitions.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`: `basicOperationsCoefficientReduction`;
  the generator's canonical comparison definitions express the relevant primitive maps.
- `Sheaf.SixFunctors.IntegralSystemOperations`:
  `IntegralSystemRealization.Operations`, `Direct`, `Open`, their actual adjunctions,
  evaluations, `System`, `Integral`, `calculus` and `pull`.
- `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`:
  `CanonicalBridge`, `OrdinaryLimitModel`, `RealizationModel`, and `RingedModels`.

Proof-only nodes `lem-pur-completed-primitive-counit-comparison` and
`lem-pur-integral-operation-roos-effectivity` were also read at their recorded modules.
`lem-coef-sequence-adjunction-cochain-transposes` has no recorded Lean declaration yet.
An existing-declaration attachment adds no imports. In particular the parent generator
node and this primitive theorem are already in the same module; inserting a self-import
when registering this proof dependency would be wrong. The parent can directly use the
existing earlier declaration when its proof is later filled.

### Edge cases

Checked zero inputs and empty schemes: no nonzero-object, nonempty-scheme or inhabited
index hypothesis is imposed. Empty and identity opens use the same actual mates and
units; their formulas are the adjunction triangle equations, and the empty case is in
the zero category. Identity pullback and proper maps retain the canonical unit/counit
normalization. The lowest index `n=0` means `A₁`, not the zero quotient. Equal bounds
`lo=hi` and `torLo=torHi` are allowed; normalization includes equal levels. Independent
index universes `s` and `i` are explicit; the scheme's site still has object universe
`u+1` and morphism universe `u`, not an imposed equality of those two universes.
The ambient existing theorem also allows repeated input labels; tensor has both input
slots even when they name the same object. No assertion is made by testing only finite
components of a derived morphism.

### Searches

- `msearch.py leanfinder`, query “The specified coefficient comparisons for completed
  pullback tensor proper direct image and open extension equal the counit transpose
  of their inverse derived limit realization”: eight unrelated general sheaf
  pullback/counit hits; no Mathlib statement of these completed operations.
- `msearch.py loogle`, query
  `CategoryTheory.Adjunction.counit_naturality, CategoryTheory.Adjunction.left_triangle_components`:
  zero hits for that combined query.
- `msearch.py grep`, query `primitive.*(reduction|transpose)|reduction.*counit`,
  subdirectory `CategoryTheory`: zero Mathlib hits.
- `msearch.py leansearch`, query “The coefficient reduction comparison of completed
  integral sheaf operations is the counit transpose of the inverse quotient tower
  realization”: eight general constant-sheaf/sheafification/counit hits, no exact match.
- `rg` on `lean/WeilConjectures` for the item id and for primitive/reduction/counit
  patterns found no matching declaration (the latter returned only unrelated counits).
  `rg` on `lean/Sheaf` for `primitiveReductionTranspose|primitiveFormulas` found the
  exact existing primitive theorem and its defining predicate in
  `Sheaf.SixFunctors.GeneratorReductionStatement`. The upstream-name inventory has
  no matching primitive theorem. This existing match is why no new file is written.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag is needed.
Only the item's `lean` record changes. The source is the maps-used sentence of
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`,
read in full, together with the node's seven-step strict-representative proof.

Validation: a module-mode scratch probe importing only the existing module was compiled
using `scompile.py`. It checked the theorem, `Word.primitiveFormulas`, and `openDInv`
successfully against the published library, with no warnings. The scratch probe is not
a delivered module. The delivery wrapper also checks the existing declaration itself.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
