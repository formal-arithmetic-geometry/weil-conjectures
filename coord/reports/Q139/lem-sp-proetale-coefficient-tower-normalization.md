## Worker report

Item: lem-sp-proetale-coefficient-tower-normalization. Group Q139. Stage 2.

The module is `Sheaf.SecSmoothPurity.ProEtaleCoefficientTowerNormalization`.
Its main declaration is
`AlgebraicGeometry.ProEtale.proEtaleCoefficientTowerNormalization`.
It also states the geometric-action transport and the ordinary/derived scalar
transport. Every theorem has `by sorry`; every helper definition has real data.
The node's mathematical statement, dependencies and proof plan are unchanged.
No new definition node or dependency repair is needed.

Hypothesis and clause correspondence:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`, in all three statements.
- Commutative unital rings are `A B C : Type u` with `CommRing` instances.
  Finiteness is `[Finite A] [Finite B] [Finite C]`. Killed by powers of ell is
  the three binders `_hA`, `_hB`, `_hC`, each `∃ n : ℕ, ∀ a, (ℓ ^ n) • a = 0`.
  These are retained even though the coefficient identities hold more generally.
- The specified unital maps are `φ : A →+* B` and `ψ : B →+* C`; the direct
  map is `ψ.comp φ`. The geometric morphism is `{Z Y : Scheme.{u}} (q : Z ⟶ Y)`.
- The actual small sites are `T.ProEt` and `ProEt.topology T`. Their site object
  universe is u+1 and morphism universe u. Constant coefficient rings are the
  recorded `proEtaleConstantRing T A`, with `ULift A` in universe u+1.
  The ordinary unbounded derived categories are `proEtaleDerivedCategory T A`.
  No constructibility, finite Tor amplitude or boundedness condition is imposed.
- The three specified c_R are literally `proEtaleCoefficientInverseImageMap q R`.
  Its definition is inverse image of the constant-section rho followed by the
  adjunction counit; it is not an arbitrary ring isomorphism. The first three
  conjuncts assert `IsIso` for A, B and C.
- The next two conjuncts are the displayed coefficient squares, in Lean's
  left-to-right composition convention: `u.map φ_Y ≫ c_B = c_A ≫ φ_Z`, and
  `u.map ψ_Y ≫ c_C = c_B ≫ ψ_Z`. The maps φ_T, ψ_T are the actual recorded
  `proEtaleConstantRingMap` applied to the specified homomorphisms.
- `coefficientTowerGeometricTransport` supplies a natural isomorphism from the
  recorded `proEtaleConstantRingPullback A q` to inverse image followed by
  restriction along c_A inverse. Its two section equations are precisely
  `m tensor r ↦ c_A inverse(r) m` and `m ↦ m tensor 1`.
  `pure` is the existing sheafification image of the sectionwise tensor.
  The last conjunct identifies the action-defining
  `proEtaleRingDirectImageMap ... (proEtaleConstantRingComparison q A)`
  with the specified `proEtaleCoefficientDirectImageMap q A`.
  Thus these are the stated geometric operations and scalar actions, not just
  unrelated isomorphic objects. Their exact termwise derived pullback is already
  the definition of `proEtaleConstantRingDerivedPullback` in the dependency.
- `coefficientTowerScalarTransport` supplies the natural isomorphism from extension
  along `u.map φ_Y`, followed by relabelling along c_B, to relabelling along c_A
  followed by extension along φ_Z. Its two section equations are
  `m tensor s ↦ m tensor c_B(s)` and `m tensor t ↦ m tensor c_B inverse(t)`.
  The coefficient squares make the source and target balancing relations agree.
  The theorem applies for any pair A,B, hence also B,C and A,C as required.
- Scalar transport includes an actual derived natural isomorphism `eD`.
  Its final equation on every cochain complex P fixes that comparison by the
  existing `reductionScalarComplexCounit` and the termwise localization factors
  `coefficientTowerRelabelFactors`. The right-hand side is the localization of
  the termwise ordinary comparison e, using `NatIso.mapHomologicalComplex`.
  It therefore specifies the canonical transport, rather than merely asserting
  existence of an isomorphism between the derived functors. The equation is
  valid on all complexes, so in particular on flat-term K-flat representatives.
- `coefficientTowerPresentation T a` packages the already published
  `reductionChange`, its fixed object/map equations from `reductionChangeExistence`,
  and `reductionDerivedChange` with its universal `reductionDerivedCounit`.
  Its `universal` field is `reductionDerivedUniversal`. There is no new choice.
- `CoefficientTowerNormalizationData T` is just the recorded `Normalization`
  on that exact presentation family. Its internal `EssentiallySmall` witness
  is `essentiallySmallSelf`; this is derivable size bookkeeping, not a hypothesis.
- The main theorem's final conjunct covers exactly the two sites by
  `∀ T, T = Y ∨ T = Z → ...`. It asserts existence of normalized data ν for
  the published presentations, and for every unbounded N identifies the ν
  associator with `scalarExtensionFunctor_composition φ ψ T` as an actual morphism
  in the C-module derived category. The only endpoint transport is the canonical
  `eqToHom` induced by `scalarExtensionFunctor_ringMap_comp φ ψ T`, which identifies
  φ_T ≫ ψ_T with (ψ.comp φ)_T. Its direction is successive-to-direct.
- The ν data retain every representative clause of the recorded dependency:
  `computed` gives the direct/first K-flat counit isomorphism,
  `intermediate_computed` gives the second computation on the extended complex,
  and `representative` is the commuting equation through those canonical counits.
  `ordinary_hom` is `(x tensor b) tensor c ↦ x tensor ψ(b)c` and `ordinary_inv`
  is `x tensor c ↦ (x tensor 1) tensor c`. These apply to P in every degree.
  The scalar-first convention writes them as `c tensor (b tensor x)`.
- Naturality in N is part of `ν.derived`, a natural isomorphism; naturality in
  coefficient maps is `ν.coefficient_naturality`. `ν.associative` gives iterated
  compatibility and `ν.unit_comp` fixes the unit. The equality to alpha identifies
  the specified comparison with this normalized family, not with an arbitrary iso.
- Every comparison is a morphism in the target module category, so it retains
  the C_T action. Commutativity explains the scalar-first representation of the
  paper's right-factor action. No flatness or finite projective dimension of φ
  or ψ, and no boundedness of P or N, occurs anywhere in a hypothesis.

Dependency declarations used (their source signatures and docstrings were read):

- def-weil-pbc-proetale-modules:
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `FiniteCoefficientModules` and
  its coefficient ring construction. This is the dependency's continuous-function
  presentation, canonically identified with the constant-ring presentation by
  the proof dependency `finiteCoefficientConstantComparison` in
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`. We use the actual constant
  rings as required by the item's statement and by det-sp-scalar-extension-functor.
- def-weil-pbc-proetale-operations:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `proEtaleConstantRingComparison`, `proEtaleConstantRingPullback`,
  `proEtaleConstantRingPushforward`, `proEtaleConstantRingDerivedPullback`;
  the publicly imported `ProEtaleOperations` supplies `proEtaleRingModules`,
  `proEtaleRingDirectImageMap` and the actual tensor action construction.
- def-weil-proetale-inverse-image:
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `proEtaleSheafInverseImage`, `proEtaleModuleInverseImage`,
  `proEtaleCoefficientInverseImageMap`, `proEtaleCoefficientDirectImageMap`,
  `proEtaleConstantRing`. These retain the original small site's distinct sizes.
- det-sp-scalar-extension-functor:
  `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`, `scalarExtensionFunctor`,
  `scalarExtensionFunctor_composition`, `scalarExtensionFunctor_ringMap_comp`.
  Read also its unique K-flat characterization in
  `scalarExtensionFunctor_composition_existsUnique`.
- lem-sfb-successive-derived-quotient-normalization:
  `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`,
  `successive_derived_quotient_normalization`, publicly importing the owning
  `SuccessiveDerivedQuotientData` module with `Presentation`, `Normalization`,
  `pure` and all the representative and tensor-formula fields used here.
- def-pc-kflat-complex:
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, used by ν.computed,
  ν.intermediate_computed and ν.representative without a new predicate.
- def-pc-flat-sheaf-modules:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite`, used by those same fields termwise.

All stated proof dependencies have plain imports of their recorded modules.
The remaining adjunction-conjugate and unit-uniqueness dependencies have Mathlib
matches in `Mathlib.CategoryTheory.Adjunction.Mates`, imported as a proof dependency.
The seven steps of the node's proof are written in the main theorem's docstring;
the transport theorems give the relevant detailed balancing arguments as well.

Searches for an existing statement:

- msearch.py leanfinder: "Inverse image constant ring tower transport and equality
  of balanced derived scalar extension associator". Eight hits, including
  `ModuleCat.extendScalarsComp` and `Algebra.TensorProduct.cancelBaseChange`:
  ordinary tensor comparisons, not this specified pro-etale derived normalization.
- msearch.py loogle: "SheafOfModules.pullback, ModuleCat.extendScalarsComp".
  Zero hits.
- msearch.py leansearch: "Inverse image constant ring comparisons preserve
  coefficient towers and balanced derived scalar extension associativity".
  Eight unrelated scalar-tower hits; no match.
- msearch.py grep: `constant.*(pullback|inverseImage)|extendScalarsComp` in
  CategoryTheory. One hit, Mathlib/CategoryTheory/Sites/ConstantSheaf.lean:158,
  commuting constant sheaves with equivalences, not the full item.
- rg in lean/WeilConjectures and lean/Sheaf for constant inverse-image/tensor
  normalization: inspected the existing scalar associator and successive quotient
  data, ScalarAssociatorConjugate, ProEtaleScalarTensorNormalization and
  ScalarInverseImageTowerDiagram. These provide ingredients or different squares,
  not equality of the specified balanced coefficient associator with alpha.
- grep of the item id in lean/WeilConjectures found no declaration. Searches for
  all nine proposed names in lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no existing declarations.

Source checked locally: sites-cohomology.tex, lemma-derived-pullback-composition
(Tag 0D6D). Its proof explicitly takes a flat-term K-flat representative, computes
both pullbacks on it and uses preservation of flat-term K-flat complexes. This
matches the coefficient-change specialization here. Also read the recorded
constant-section construction and normalized adjunction/associator docstrings.

Edge cases: empty Z and empty site objects (all ring-sheaf sections there are
unique); C = 0, and also A = 0 when unital maps exist; identity coefficient maps;
Y = Z (the final disjunction still covers that one site); n = 0 in a torsion
hypothesis (only the zero ring satisfies it); nonflat Z/ell² -> Z/ell; arbitrary
unbounded complexes. No nonempty-scheme, nonzero-ring or flatness hypothesis is
introduced. The inverse tensor formula inserts 1, which remains valid in zero
rings. No node fault or statement dispute was found.

Validation: scompile.py compiled the final expanded module, in both sandbox and
library-module modes, cleanly within 60 seconds. Earlier universe errors were
repaired by fixing all four universes and the explicit smallness witness at the
Normalization projection; the site object and morphism universes were preserved.

## Second reading by Q139

This is an in-session second pass, not a claim of an independent worker review:
the dispatcher explicitly forbids starting another agent, and the maintainer
provides independent review. I reread the node and complete delivered file.

The initial draft needed an explicit derived scalar transport equation: I added
eD and its universal-counit/termwise-factor compatibility to
coefficientTowerScalarTransport. The formulas now specify both directions and
retain the target action. I checked the direction of every composition: the
coefficient square is u(phi) then c_B, and the associator comparison is tau then
transport along phi_T psi_T = (psi phi)_T, ending at the prescribed alpha.

The three finite, prime-power-torsion hypotheses are present in the main theorem;
each pairwise transport theorem keeps the corresponding hypotheses. Both Y and Z
and all unbounded N occur in the final conjunct. The existing Normalization fields
state both pure-tensor formulas, termwise-flat K-flat computation, the composite
unit and all naturality/coherence clauses. No per-degree replacement of a derived
isomorphism is used: eD and the associator live in the derived categories.

I checked that the helper definitions merely expose data of recorded constructions:
they introduce no alternative ring sheaf, module category, tensor or resolution.
All implicit parameters and universes are explicitly bound, no local notation or
local instance is introduced, all lines are at most 100 characters, and all three
postponed proofs are whole named theorem proofs owned by this DAG node. No
mathematical change to the node, new node or dependency repair is required.
