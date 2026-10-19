## Worker report

Module: `Sheaf.Paper.DirectImageChangeRingTranspose`.
Main statement: `AlgebraicGeometry.ProEtale.directImageChangeRingTranspose`.
The theorem has `sorry` as its entire proof. Its five map helpers and one normalization predicate have actual data,
constructed from the recorded functors, canonical isomorphisms and Hom equivalences.
No node statement, dependency list or dependency binding changes.

The fixed coefficient tensor is written throughout as
`scalarExtensionFunctor φ T ⋙ scalarRestriction φ T`. This is precisely the
presentation `r_T T_T` specified in the node, including the action on maps
`v tensor_A^L id_B`. It does not introduce another tensor product. The six helpers belong to the canonical maps in this node and are all listed in
`lean.declarations`. The normalization predicate is asserted as the theorem's first
conjunct, rather than supplied as a hypothesis.

Hypotheses and clauses, matched against the node:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field of positive characteristic distinct from ell: `{k : Type u} [Field k]`,
  `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`. A field of positive
  characteristic has prime characteristic, so this is exactly the stated setting.
- Separated finite-type k-schemes: `{X Y : Over (Spec (.of k))}` together with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on both structure maps.
- The specified proper k-morphism: `(f : X ⟶ Y) [IsProper f.left]` in `Over`.
- Finite commutative coefficient rings: `{A B : Type u} [CommRing A] [CommRing B]`
  with `[Finite A] [Finite B]`.
- Both rings killed by powers of ell: `_hA` and `_hB`, each
  `∃ n : ℕ, ∀ x, (ℓ ^ n) • x = 0`.
- The unital ring map: `(φ : A →+* B)`.
- Ordinary uncompleted, unbounded categories: `proEtaleDerivedCategory X.left A`
  and its analogous constant-ring categories. These are the categories already used
  by the recorded scalar-extension interface. Neither a completion nor a full
  subcategory is introduced.
- Inverse image, direct image and counits: the published
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`, and
  `proEtaleRingDerivedAdjunction`, specialized at `proEtaleConstantRingComparison`.
  The imported `constantPullback` abbreviation is the same derived pullback.
- Canonical constant-ring identifications: `proEtaleConstantRingComparison f A`
  and its B version. The coefficient square is the actual theorem
  `proEtaleConstantInverseImageMap_naturality` at `RingHom.ulift φ`, with only
  definitional simplification and symmetry. No square compatibility is assumed.
- Restriction `r_T`: the existing `scalarRestriction φ T`, itself termwise exact
  restriction along the constant ring-sheaf map, descended to derived categories.
- Specified comparison d: `directImageChangeRingRestrictionDirectImage` specializes
  `proEtaleRingRestrictionDerivedDirectImage`; its unique derived-unit
  characterization is retained rather than choosing an isomorphism of endpoints.
- Unique B-linear gamma: `directImageChangeRingGamma` applies the canonical
  B-adjunction `homEquiv` to `tensorPullbackIso φ f` followed by
  `scalarExtensionFunctor φ X` of the A-counit. Bijectivity of this existing Hom
  equivalence supplies exactly the uniqueness requested, without an extra axiom.
- Tensor/pullback identification tau: `directImageChangeRingTensorPullback` retains
  the concrete composite b inverse at `T_Y K`, followed by restriction of theta.
  The first conjunct `IsDirectImageChangeRingTensorPullbackNormalized φ f.left`
  now explicitly asserts the missing Step-2 identification with the canonical map.
  For every K-flat P with flat sheaf terms it supplies a chain map t from ordinary
  A-pullback of restriction of `P tensor_A B_Y` to restriction of
  `(p_A^*P) tensor_A B_X`. Its first equation states in EVERY degree, for EVERY
  site object U and arbitrary local sections s of B_Y and x of P, that t sends the
  pullback-unit image of `s tensor x` to `c_B(p^{-1}s) tensor p^{-1}x`.
  The scalar image is the component of `proEtaleRingDirectImageMap` at U, exactly
  the adjoint of the fixed `proEtaleConstantRingComparison f B`; the x image is
  the unit of the normalized `proEtaleConstantRingAdjunction A f`.
  Its second equation is the derived localization square, using the published
  `scalarExtensionFunctorCounit` on P and on its pullback, and the actual
  `mapDerivedCategoryFactors` for scalar restriction and module pullback.
  The counits are invertible on these K-flat representatives; pullback preserves
  flat K-flat representatives by the existing tensor-pullback dependency.
  The square therefore pins tau to localization of the pure-tensor map.
- The restricted A-linear map: `directImageChangeRingRestrictedGamma` is exactly
  `(scalarRestriction φ Y).map gamma ≫ d.hom.app (T_X N)`, in Lean composition order.
- Projection-morphism conclusion: the second conjunct states that `homEquiv.symm`
  of this restricted map equals tau followed by the fixed-coefficient tensor
  functor applied to the A-counit. This is exactly the defining transpose
  `epsilon_A tensor id_B`, and bijectivity identifies the map with the projection
  morphism. It asserts no projection-formula invertibility.
- Naturality in N: the third conjunct quantifies over every `N'` and `v : N ⟶ N'`
  and writes the square from `r_Y T_Y R_A` to `R_A r_X T_X` explicitly.
- No boundedness, coefficient flatness or finite Tor dimension: there are no such
  binders or conditions on N or B. Finiteness and torsion are the node's own context.

Dependency declarations and source inspection:

- `sk-def-sfb-dc-setting`: read the current published source of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  through `scompile.py --source`, including the setting documentation. The setting
  is rendered by the same explicit field/Over/finite-type/separated binders; its
  chosen compactification and condensed-module categories are not needed in this
  lemma, which explicitly uses ordinary constant-ring categories. No setting
  predicate or private copy is defined.
- `def-weil-pbc-proetale-modules`: imported
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, reading
  `finiteCoefficientRingSheaf`, `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory` and the constant/realization interfaces.
  The constant-ring presentation used by the recorded operations and scalar
  extension is the existing presentation of these finite coefficient categories;
  the unique constant-preserving comparison and realization identify them.
- `det-sp-scalar-extension-functor`: imported
  `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`, using
  `AlgebraicGeometry.ProEtale.scalarExtensionFunctor`. Read its K-flat counit,
  representative and map declarations. They retain the right-factor B action.
  Its public dependency `Sheaf.SecSmoothPurity.OpenScalarExchange` supplies the
  existing `scalarRestriction`, `constantPullback`, and `tensorPullbackIso`.
- `def-weil-pbc-proetale-operations`: public dependency
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`; read
  `proEtaleConstantRingComparison`, `proEtaleConstantRingDerivedPullback`, and
  `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`'s
  `proEtaleRingDerivedAdjunction`, whose ordinary adjunction is fixed by the
  tensor-unit formula. Used the published ring-derived operations directly.
- `prop-weil-pbc-proetale-constant-ring-map`: public dependency
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`; read
  `finiteCoefficientInverseImageMap_isIso`,
  `finiteCoefficientInverseImageMap_constant`, and its empty-source clause. The
  operations' actual structure map is exactly their constant-preserving version.
- `lem-weil-pbc-ring-sheaf-change-adjunction`: imported
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`; used
  `proEtaleRingRestrictionDerivedPullback`,
  `proEtaleRingRestrictionDerivedDirectImage`, and its exact restriction functor.
  Read the full signature and proof docstring of `proEtaleRingSheafChangeAdjunction`,
  including the directions of b inverse and d in the adjunct equality.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: imported
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`; read
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.`
  `ringedTopoiCanonicalDerivedTensorPullback` and the public pro-etale specialization.
  The coefficient/pullback comparison is the published `tensorPullbackIso`, the
  inverse scalar-adjunction mate of b. The new first conjunct explicitly states
  its underlying pure-tensor normalization and localization square, as requested
  by the return; this identification is no longer left to its docstring.
- Proof-only dependencies: imported the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
  Their public tensor, localization and representative interfaces support Step 2
  of the natural-language proof. All already stated proof dependencies are present
  through these imports and the public statement dependencies.

Edge cases checked before writing and rechecked against the final signature:

- N = 0, empty source, and the zero coefficient ring are allowed; no nonzero or
  nonempty hypotheses occur. The constant comparisons handle empty-site zero rings.
- φ = id and f = id use the canonical scalar/pullback and normalized adjunction maps.
- Non-flat Z/ell^2 → Z/ell is allowed, including complexes unbounded in both directions.
- Arbitrary morphisms between unbounded inputs are included in the naturality clause.
- The actual small pro-etale site retains its distinct object and morphism universes
  (u+1 and u). No equality of these universes or smaller model site is imposed.
- The finite coefficient rings can be placed in the common universe of the existing
  recorded interface; the constructions use its standard ULift of constant rings.

Searches for an exact existing statement (fresh `msearch.py` searches, also recorded
in the sandbox's searches.jsonl):

- LeanFinder: "Restriction of scalars identifies derived direct image coefficient
  comparison with projection morphism via adjunction transpose". Eight generic
  module restriction and open-immersion adjunction hits, no derived coefficient mate.
- Loogle: `CategoryTheory.Adjunction.homEquiv, CategoryTheory.NatTrans`. Zero hits.
- LeanSearch: "Restriction of derived scalar extension direct image map is the
  projection morphism whose transpose is counit tensor identity". Eight ordinary
  scalar-restriction/module-adjunction hits, no target statement.
- Mathlib grep: `projection.*[Tt]ranspose|[Tt]ranspose.*projection` in CategoryTheory.
  Zero hits.
- Upstream grep by the item id: no occurrence. Checked the generic upstream
  `WeilConjectures/CategoryTheory/Adjunction/ProjectionMap.lean`, whose
  right-adjoint projection transpose is generic, not this coefficient restriction
  identity.
- Project/source rg for `directImageChangeRing|coefficientTensorPullback` and the
  item id: no existing declaration with these names or exact statement.
  Read `DirectImageScalarExchange`, `ProEtaleFixedScalarRestrictionDirectImage`,
  `EtaleProEtaleScalarMate`, `ProjectionFormulaArrows`, and the actual scalar
  inverse-image interfaces. They respectively state exchange, another presentation's
  restriction comparison, etale comparison, and general projection constructions;
  none asserts this node's restricted proper coefficient transpose identity.

Validation: the repaired module compiled through `scompile.py` in both sandbox
and library module positions, with no errors or warnings (4.5 s and 4.7 s).
Every variable and universe is explicit, and there are no `let` or `show` binders
in the normalization condition. The only postponed proof is
`directImageChangeRingTranspose`, whose docstring now explains how its Step 2
constructs t and obtains the displayed localization equation. There are no
statement disputes, new DAG nodes, or dependency repairs.

## Returned H3/H6 repaired

The returned immutable head was `50b93579b361`. The retained packet initially
passed the prescribed dry run (`5e4645dcba`), but its mathematical defect remained:
tau was defined by b inverse followed by r(theta), so its two conclusions alone
were formal mate and naturality identities. The repair uses the reviewer's
explicit alternative of characterizing the map on flat K-flat representatives.
It adds the normalization condition above as a CONCLUSION of the SAME theorem,
with real Prop data and no additional postponed helper theorem. The older two
conclusions, including every hypothesis, remain intact. The main theorem is now
`normalization ∧ transpose_identity ∧ naturality`.

This condition is not another arbitrary tensor comparison: its local equation
specifies every inverse-image tensor generator, and its derived equation ties
that map to the existing concrete tau. In particular choosing a different natural
isomorphism with the same endpoints would not make the new conjunct automatic.
It states the normalization in the node's proof Step 2, equivalent to specializing
`proEtaleCanonicalTensorComparison` at (K,B_Y), in the authorized one-sided
K-flat scalar-extension coordinates. It needs no resolution or flatness of B.

Consumers checked against the return:

- `det-sp-reduction-direct-image`: the transpose identity is available as `.2.1`
  and the canonical normalization as `.1`, so its proper projection map uses the
  actual counit-tensor canonical map. No modification of the citer is required.
- `lem-coef-finite-adjunction-transition`: the same normalization identifies the
  coefficient transition with the canonical projection map, while `.2.2` supplies
  naturality. No change of its mathematical use is required.

## Repair self-check

I reread the item and its four proof steps, the actual blueprint direct-image
proof Step 1, the returned diagnostic, the complete repaired signature and the
helper predicate. I checked the square's source and target through the actual
restriction, extension and pullback quotient factorization maps; s is an arbitrary
LOCAL coefficient section, not just a global constant. The ring-section map is
adjoint to c_B, so it includes exactly the required coefficient transport. Since
the site-unit images locally generate inverse image and local pure tensors
generate sheaf tensor, the ordinary formula determines t; all flat K-flat models
are included and the exact localization square fixes its derived image.

The unchanged edge cases above remain allowed: zero object, empty source, zero
ring, identity coefficient map, identity scheme map, non-flat Z/ell^2 to F_ell,
and arbitrarily unbounded P and N. The K-flat/flat-term premises occur ONLY inside
the normalization conclusion's universal test on representatives; they impose
no extra hypothesis on N or B. There are no new category structures, choices of
an unspecified isomorphism, hollow definitions, or additional sorries.

Compared the sandbox node with the current shared node: only `lean` differs.
Its recorded signature is extracted verbatim from the file and its declaration
list includes the new predicate. The shared module is absent because this is a
returned, unlanded delivery; its retained source matches the returned mate-only
construction, which is now repaired rather than merely rebased or re-pushed.
No independent agent was started, as this worker's brief expressly forbids it.

Repair-specific searches: `msearch.py` LeanFinder query "Canonical derived scalar
extension pullback comparison characterized on flat K-flat representatives by
pure tensors and localization" returned eight ordinary-module/flatness hits,
with no matching pro-etale derived normalization (exact results in searches.jsonl).
`rg` of the project's Lean and upstream `WeilConjectures` found the existing
`scalarExtensionFunctorKFlatIso`, `scalarExtensionFunctorCounit`,
`proEtaleCanonicalTensorComparison`, `proEtaleTensorPair`, and ordinary canonical
comparison declarations; these were read and reused as the construction and
normalization interfaces. The retained search results above still cover all
three required search types for this same node. No new underlying notion is
introduced by packaging its Step-2 equation as a predicate.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
