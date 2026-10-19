## Worker report

Repair of the returned immutable head e8bc1f01c945. The retained sandbox had only
an existing:true binding to the old upstream WeilSheaf/WeilComplex interface and
an incorrect equivalence claim. The current shared item has no Lean record. This
packet replaces that binding with an actual module, WeilMixedUpperBounds.lean,
and repairs AdicPunctualWeights.lean under §1(B). The natural statement is unchanged.

H3 is repaired by using precisely `sfCommonStageWeilSheaf D l hl Y₀ Qbar` and
`sfCommonStageWeilComplex D l hl Y₀ Qbar` from
`Sheaf.Paper.SfWeilSheafComplex`. These are the full heart-carrier subcategory and
the fixed-pair category over the recorded common-stage constructible category.
Neither the old pro-etale Qbar-sheaf model nor its derived category of Weil
sheaves occurs in the delivered code. In particular no triangulated structure
on the fixed-pair category is assumed.

H4 is repaired by generalizing the TWO existing embedding parameters in
`Sheaf.Paper.AdicPunctualWeights` from `Qbar ≃+* ℂ` to `Qbar →+* ℂ`, retaining
the SAME named predicates and their bodies. The eigenvalue predicate is unchanged.
`SfIsMixed` and `SfComplexIsMixedOfWeightsAtMost` and the closure theorems actually
call that module's `SfIsMixedOfWeightsAtMost`, whose cokernel clause actually
calls `SfIsPunctuallyPureOfWeight`. The earlier report's claim that the old
upstream predicates used this declaration was false and is withdrawn.

Hypotheses and clauses, checked against the item's full statement:

* Finite-field datum, algebraic closure of the base field, and geometric rather
  than arithmetic Frobenius: `D : FiniteFieldDatum.{u}` and
  `D.geometricFrobenius Y₀`. The datum fixes p, a, q, k₀ and k with q=p^a.
* Coefficient prime and closure: `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`,
  `Qbar : Type v`, `[Field Qbar]`, `[Algebra (Padic l) Qbar]`,
  `[IsAlgClosure (Padic l) Qbar]`. Scheme universe u and coefficient-closure
  universe v remain independent.
* Finite-type X₀ over k₀: `Y₀ : Over (Spec (.of D.k₀))`,
  `[LocallyOfFiniteType Y₀.hom]` and `[QuasiCompact Y₀.hom]`. There is no
  separatedness, lissity, semisimplicity, or extra invertibility hypothesis.
  Finite type on the geometric fibre is obtained by the actual pullback.snd
  instances inside the cohomology definitions, not assumed as new data.
* The field embedding is exactly `(iota : Qbar →+* ℂ)`. A unital homomorphism
  of fields is injective; surjectivity is not required. An isomorphism as in
  the dependency's original statement is included by `iota.toRingHom`.
* Constructible Weil sheaf F: the parameter is the recorded full heart-carrier
  category, not an unrelated category with the same informal name.
* The finite filtration is the reused `SfIsMixedOfWeightsAtMost`: `m : ℕ`,
  `G : Fin (m+1) → sfCommonStageWeilSheaf ...`, arrows `φ i : G i.castSucc ⟶
  G i.succ`, `IsZero (G 0)`, an isomorphism of the last term to F, and
  `∀ i, Mono (φ i)`. Successive monomorphisms identify these terms with
  subsheaves of F; allowing the endpoint isomorphism does not fix an
  artificial subobject representative.
* Each quotient is the categorical `cokernel (φ i)` in that same abelian Weil
  heart, with `∃ v : ℝ, v ≤ w ∧ SfIsPunctuallyPureOfWeight ... v`.
* Punctual purity is exactly `∀ y α, SfPunctualEigenvalue ... F y α →
  ‖iota α‖ = (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (v / 2)`.
  Closed points, actual degree-zero local geometric Frobenius, extension of
  its operator to Qbar, and all eigenvalues are those of the recorded
  dependency. The bound uses equality at a real pure weight v≤w, not just
  an inequality on all eigenvalue norms.
* “Mixed for some w” is the definition `SfIsMixed := ∃ w : ℝ,
  SfIsMixedOfWeightsAtMost ... F w`.
* A bounded constructible Weil complex K is precisely an object of the
  recorded `sfCommonStageWeilComplex`; boundedness is inherited from the
  constructible carrier, not asserted by a second derived-category choice.
* Its cohomology is the explicit `sfWeilCohomology D l hl Qbar Y₀ b` functor.
  The underlying endofunctor is the recorded
  `constructibleTruncationCohomology t b = (t.truncLE b ⋙ t.truncGE b) ⋙
  shiftFunctor _ b`, with t the recorded common-stage standard t-structure.
  `sfWeilCohomologyFrobenius` uses `constructible_pullback_t_exact` for the
  actual geometric Frobenius. The two comparison isomorphisms are chosen from the
  named `sfWeilFrobeniusTruncLE_existsUnique` and
  `sfWeilFrobeniusTruncGE_existsUnique` theorems, with their explicit counit
  and unit equations. These specialize and transport the published t-exact
  comparison to the actual fixed-pair pullback without expensive unfolding
  of alternative prime-invertibility instances. The cohomology comparison
  is their composite with the published representative-normalized shift
  `fieldCommonWeilFrobeniusShift` and ordinary functor associators. No bare
  unspecified natural isomorphism or arbitrary shift is chosen. `IsoAlgebra.mapOfNatIso`
  makes the Weil structure the comparison followed by H^b(theta), and maps
  underlying arrows by H^b. `ObjectProperty.lift` restricts its range to the
  recorded Weil heart, using the named theorem `sfWeilCohomology_mem` only
  for the heart-membership proof. All object and morphism data are explicit.
* The complex bound is `∀ b : ℤ, SfIsMixedOfWeightsAtMost ...
  ((sfWeilCohomology ... b).obj K) (w + (b : ℝ))`. The degree shift is plus b.
* Subobjects: `SfIsMixedOfWeightsAtMost.of_mono` takes any monomorphism
  `i : G ⟶ F` and transfers the bound from F to G.
* Quotients: `.of_epi` takes any epimorphism `p : F ⟶ G` and transfers the
  bound from F to G.
* Extensions: `.of_mono_cokernel` takes a monomorphism `G ⟶ F` and bounds
  on G and its cokernel, concluding the same bound for F. In the recorded
  abelian heart this is exactly the extension clause. Each closure theorem
  has a whole `sorry` proof, with the intersection/image/splicing proof
  written in its source-and-blueprint docstring.

Dependencies read and used:

* `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilForget`,
  `sfCommonStageWeilFrobeniusPullback` and the finite-stage construction.
* `Sheaf.Paper.AdicPunctualWeights`: `SfPunctualEigenvalue`,
  `SfIsPunctuallyPureOfWeight`, `SfIsMixedOfWeightsAtMost`, as repaired.
* `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageStandardTStructure` and
  `sfCommonStageHeartProperty`, on exactly the intrinsic category recorded
  by `Sheaf.SixFunctors.SfCategories` (`def-sf-categories`), whose full
  statement and module were read. These are provided by the imported
  coefficient/heart modules; no new copy is made.
* `Sheaf.Paper.ConstructibleTruncations`: `constructibleTruncationCohomology`.
  `prop-constructible-truncations` is added to stmt_deps as an already landed
  node, to make the cohomology construction's ownership explicit.
* `Sheaf.Paper.ConstructiblePullbackTExact`:
  `constructible_pullback_t_exact`, `ConstructiblePullbackComparison.cohomology`,
  and its normalization clauses (used in the new helper theorems
  describing exactly their normalized specialization). Its already landed node
  `lem-a1-constructible-pullback-t-exact` is added to stmt_deps.
* `Sheaf.Paper.FieldWeilShriekShiftData`: the uniquely normalized
  `fieldCommonWeilFrobeniusShift`, fixed by signed integral Roos reindexing,
  rationalization and finite-stage descent. Its landed node
  `def-zl-field-weil-shriek-shift-data` is added to stmt_deps. Only its
  Frobenius shift is used; compact-support adjoints are not parameters here.
* `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso` from
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`, and Mathlib's
  `ObjectProperty.lift`, monomorphisms, epimorphisms and cokernels.

The setup node's upstream `WeilSheaf.IsGeometricallyConstant` and
`WeilSheaf.IsUnramifiedAtInfinity` signatures/docstrings were inspected; this
item uses its base-field/Frobenius conventions and neither affine-line
predicate. Its old-model module is not needed as an import. Likewise
`def-weil-complex-weights` has no Lean record and its closed audit points to
old-model upper-weight characterizations. The current server source of
`WeilConjectures.WeilSheaf.ComplexWeights` was read via `scompile.py --source`;
it explicitly says its lower/duality half is unavailable. None of its
old-model predicates is used to type our complex bound. This delivery states
only the upper clause owned by the present item, not a substitute for that
other node's Verdier-dual definition.

Edge cases checked by unfolding the displayed definitions: m=0 permits zero
sheaves with no quotient tests; zero sheaves are punctually pure at every
weight because their local spectrum is empty. Thus empty schemes and every
real upper bound remain possible. Zero cohomology in any integer degree
satisfies the condition; all integer degrees (including negative ones) are
quantified. Non-strict arrows permit repeated filtration terms; there is no
false strictness requirement when a quotient is zero. Closure allows identity
maps, zero subobjects and zero quotients, and does not require a split
extension. The embedding is used only by evaluation and its norm, with no
inverse or surjectivity.

Searches, including this repair:

* `msearch.py ... leansearch "finite filtration of a sheaf by punctually pure
  quotients and complex cohomology weights"`: eight generic filtration and
  sheaf-colimit hits, including `IsFiltration` and `IsModuleFiltration`;
  no Weil-weight match.
* `msearch.py ... leanfinder "cohomology functor of a t-structure commutes with
  a t-exact functor"`: eight generic homological/triangulated functor hits;
  no fixed-pair Weil cohomology functor.
* `msearch.py ... loogle "WeilSheaf.IsMixedOfWeightsAtMost,
  WeilComplex.IsMixedOfWeightsAtMost"`: no hits, unknown upstream identifier.
* `msearch.py ... grep "IsMixedOfWeightsAtMost|IsPunctuallyPureOfWeight"`:
  no Mathlib hits.
* `rg` in the permitted upstream tree found old-model definitions in
  `DeligneLaumon/Reduction/Weights.lean`. Their full binders, filtration and
  cohomology definitions and closure statements were read; they are not
  matches on the categories required by this item.
* `rg` in `lean/Sheaf` found the recorded `AdicPunctualWeights` definitions;
  these are reused and generalized rather than duplicated. Searches for
  `sfCommonStage.*cohomology`, `cohomology.*sfCommonStage`, `SfIsMixed` and
  `sfWeilCohomology` found no existing cohomology-on-Weil-pairs functor or
  complex mixed bound; similarly named point-cohomology declarations have
  different domains. Existing truncation and t-exactness helpers are reused.

No mathematical dispute or natural-statement correction is needed. The six
postponed theorems in the item's module are the uniquely normalized
upper/lower Frobenius truncation
comparison existence theorems, `sfWeilCohomology_mem`, and the three named
closure theorems. No definition contains sorry data.

## Dependency modules

`def-weil-punctual-weights`: its fixed-pair sheaf category and eigenvalue
interface were usable, but its restriction to a field isomorphism into ℂ
excluded the field embeddings expressly permitted by the item. The same
AdicPunctualWeights module is supplied with both predicate parameters
changed to ring homomorphisms. All other mathematical data and formulas
are retained. This is the requested §1(B) generalization; the original
isomorphism case is included by coercion/`toRingHom`. Only this dependency's
`lean` field changes. No new definition node is needed.

## Second reading by Q52

This is a separate author rereading; the dispatcher prohibits starting a
second agent. Independent maintainer review remains required. I reopened the
natural node, the retained returned record, the current base records, the
fixed-pair definition, the punctual module and the entire new module.

The first returned mismatch was substantive: the old source's category was
not the recorded one. I checked every domain in the final declarations:
all sheaves, intermediate filtration terms and cokernels are the actual
sfCommonStageWeilSheaf; all input complexes are sfCommonStageWeilComplex.
The new cohomology functor lands in their full heart-carrier subcategory.
The carrier is the recorded two-truncation-and-shift cohomology, and its
Weil structure uses the original K.str through mapOfNatIso. This is not
D^b of Weil sheaves, and there is no identification of its Hom groups with
Ext of Weil sheaves. The finite-type assumptions consist of exactly local
finite type and quasi-compactness over the fixed finite field; the copied
punctual module and the new module impose no separatedness.

The second mismatch was the false assertion about the purity dependency.
I traced the final calls, rather than comparing informal predicate names:
SfComplexIsMixedOfWeightsAtMost and the closure theorems call
SfIsMixedOfWeightsAtMost, whose cokernel test calls the repaired recorded
SfIsPunctuallyPureOfWeight. That predicate calls the unchanged
SfPunctualEigenvalue and has the exact residue-cardinality norm equality.
Both predicate parameters now accept Qbar →+* ℂ. No use of an inverse
embedding, no different local Frobenius, and no alternate purity predicate
remains. The original isomorphism case still has the same formula.

Reading the source's clauses in order, I checked the natural length, the
initial zero term, the last-term isomorphism, every monic filtration arrow,
and every cokernel's independent real weight v≤w. The zero-length case is
included. The existential predicate quantifies over real w, and the complex
predicate quantifies over all integer b with bound w+b. Its H^b carrier is
truncated in degree b and shifted by b into the heart, so the signs agree
with cohomological indexing. The three theorem directions match exactly
subobjects, quotients and extensions. Their proof docstrings give respectively
intersection, image and splicing, and their bodies are sorry as stage 2 requires.

I also checked the definition-data boundary: cohomology's carrier, structure
isomorphism and action on arrows are supplied by the recorded functors and
normalized comparison. The two comparison existence-and-uniqueness proofs
and heart membership are named postponed proofs; the former determine the
chosen isomorphisms uniquely by the displayed equations.
The upper and lower t-exact comparisons have explicit uniqueness and
unit/counit normalizations, and the shift is the published uniquely
representative-normalized one. The cohomology isomorphism is their actual
whiskered composite. Thus no arbitrary Nonempty isomorphism or shift
structure is used. The specialization helpers are needed to avoid costly
elaboration of two presentations of the same prime-invertibility instance;
they do not change the functor or add a mathematical hypothesis.
The dependency repair changes no eigenvalue data. The report now records
the two category/purity faults and their repairs instead of repeating the
returned five-line assertion of equivalence.

Validation: the two delivered modules compiled together in dependency order via
scompile.py, each individually under the 60-second limit, with no errors or
warnings. The normalized construction compiled as a library file in 19.4 s.
Diagnostic #check lines have been removed for the final packet. The complete
shift-data dependency closure was checked for a path back to this item; none
exists, so the added shift dependency introduces no dependency wait cycle.

Compatibility check: Mathlib RingEquiv.toRingHom_eq_coe and coe_toRingHom
confirm the standard coercion from a ring equivalence to a ring homomorphism.
Existing isomorphism-valued callers therefore retain the same norm formula.
