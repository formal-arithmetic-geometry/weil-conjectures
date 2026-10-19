## Worker report

The module `Sheaf.Paper.IntegralTwistScalarCoherence` states
`WeilConjectures.integral_twist_scalar_coherence`, with proof `sorry`.
It retains the node's statement, statement dependencies and proof plan unchanged.
There are two helpers with real data: `integralTwistCoherenceObject` bundles the
actual derived twist using the existing membership proof, and
`integralTwistCoherenceModelMap` composes the published quotient-completion chain
map with the inverse published resolving comparison. Neither chooses a new
coefficient object, scalar functor, twist or natural comparison.

Hypothesis correspondence:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Scheme with ell invertible: `(S : Scheme.{u})` and
  `[∀ x : S, Invertible (l : S.residueField x)]`.
- Finite extensions E, F, G of Q_ell: each is `Type u`, with `Field`,
  `Algebra (Padic l)` and `FiniteDimensional (Padic l)` instances.
- Tower inclusions: `ι : E →ₐ[Padic l] F`, `κ : F →ₐ[Padic l] G`, composite
  `κ.comp ι`. Field algebra maps are injective; identity inclusions are allowed.
- Every integer twist: `(m : ℤ)` without a positivity restriction.
- C is in the specified full integral category:
  `C : sfIntegralConstructibleCategory l E S`. Its predicate includes actual
  derived completeness, constructibility of all positive reductions, and one
  finite support interval independent of the reduction level.
- Completed ring sheaves are the existing
  `completedIntegralCommRingSheafUnrestricted l H S`; their underlying ring
  sheaves and modules are the existing `integralTowerModules`.
- Ext is the existing `integralScalarExtensionOfUniverses`. Its restriction is
  `sfConstructibleIntegralScalarExtension`, which has definitionally the same
  ambient object and morphism maps. The old restricted API takes an otherwise
  unused characteristic parameter p and ell ≠ p: the statement supplies the
  fixed value `l + 1` and `ne_of_lt (Nat.lt_succ_self l)`. This adds no hypothesis,
  finite-field datum, characteristic condition, or structure map on S.

Conclusion correspondence, in order of the Lean conjunctions:

1. Ordinary associativity and its prescribed transport: `∃ μ` is a natural
   isomorphism of the actual ordinary derived scalar functors. For EVERY
   flat-term K-flat P its chain isomorphism `a` sends nested
   `completedScalarTensorSection`s with coefficients b,c to the direct tensor
   with coefficient `c * completedCoefficientMap(κ)(b)`. The counit equation
   determines μ on the localization, rather than allowing an arbitrary natural
   isomorphism. The following equation is `d_C ≫ a_C = μ_C ≫ χ_GE,C`, with
   `d_C = T_GF(χ_FE,C) ≫ χ_GF,B_FE(C)` and
   `a_C = (sfIntegralScalarComp ...).hom.app C`. Since the specified χ maps are
   invertible on complete objects, this is exactly the node's transport
   `a_C = χ_GE,C ∘ μ_C ∘ d_C⁻¹` in right-to-left notation.
2. The displayed completed square: Lean composition is left-to-right, so its
   left side is `B_GF.map β_FE,C ≫ β_GF,B_FE(C) ≫ W_G.map a_C` and its right side
   is `a_C(m) ≫ β_GE,C`. The `β`s are exactly `integralTwistCompletedBeta` from
   the recorded dependency. `integralTwistCoherenceObject` makes C(m) a bundled
   object of the same full subcategory, with no new membership assumption.
3. Common K-flat formula: for every C, every P in
   `(integralOperationsGoodComplex l E S).FullSubcategory` and every
   `e : DerivedCategory.Q.obj P.obj ≅ C.obj`, the chain isomorphism sends
   `(((x ⊗ y) ⊗ b) ⊗ c)` to
   `(x ⊗ κ(b)c) ⊗ twistScalarMaps_GE(y)` in EVERY degree i and over EVERY site
   object U. `siteSheafTensorTmul` and `completedScalarTensorSection` are the
   actual sheafified tensor generators; there is no assumption about global
   generation. Commutativity identifies c*κ(b) with the node's κ(b)c.
   `twistScalarMaps_GE(y)` is precisely the specified interpretation of y⊗1.
   The long equation after the formula identifies this chain map with the RIGHT
   completed path, using the two ordinary counits, the functor/complex
   comparisons, and the actual quotient-completion model map. Conjunct 2 then
   identifies the LEFT path with this same representative. Thus the formula is
   linked to both paths, not merely a freestanding chain isomorphism.
4. Identity scalar comparison is multiplication: on every good integral model,
   `χ_id ≫ sfIntegralScalarUnit = completedScalarCounit ≫ Q.map
   completedScalarIdentityMultiplication`. The latter is the dependency's
   uniquely prescribed map b⊗x ↦ b*x.
5. Identity twist comparison: `β_id,C ≫ W(unit_C) = unit_C(m)`.
6. Source identity associator: `a_id,FE = B_FE.map unit_E`.
7. Target identity associator: `a_FE,id = unit_F` at B_FE(C).
8. Rationalization: for every object of `sfRationalConstructibleCategory`,
   `sfRationalScalarComp` is `HEq` to the image under the actual
   `sfRationalConstructibleLocalization` of this same `sfIntegralScalarComp`.
   HEq records only the published endpoint object identifications of the raw
   localization; the maps are the specified maps, not arbitrary isomorphisms.

The ordinary associator's representative characterization is included to
identify the ordinary tensor map used to define a, not to replace the
completed square. Existing `sfIntegralScalarComp` and its rational image are
reused; the theorem asserts the equality with the newly named dependency beta.
The ambient equalities are equalities in the full integral category because
its inclusion is faithful and all endpoints have the existing membership proofs.

Dependency declarations read and used:

- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses`,
  `integralScalarExtensionComparisonOfUniverses`.
- `Sheaf.Paper.IntegralTwistDerivedScalarCanonical` (publicly retains
  `IntegralTwistDerivedScalar`): `integralTwistCompletedBeta`,
  `integral_twist_derived_scalar`; the first ordinary witness is also read.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfIntegralScalarComp`,
  `sfIntegralScalarUnit`, `sfRationalScalarComp` and their uniquely normalized
  existence theorems. Its legacy ordinary associator and unit were read in
  `ScalarExtensionComposition`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedCoefficientMap`, `completedOrdinaryScalarComplex`,
  `completedDerivedScalarExtension`, `completedScalarCounit`,
  `completedScalarComparison`, `completedScalarChainComparison`,
  `completedScalarTensorSection`, `completedScalarIdentityMultiplication`,
  `finiteFreeCompletedScalarComparison`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`:
  `SheafOfModules.tensorClosed`; tensor formulas use the recorded
  `SheafOfModules.siteSheafTensorTmul`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`,
  `Scheme.ProEt.topology`. The site retains object universe u+1 and Hom universe u.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, reexporting the
  completed coefficient sheaves: `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCoefficientSheafUnrestricted`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.IntegralTwistBaseChange`: `integral_twist_base_change` and the
  retained `twistScalarMaps`, including its tower and signed-dual clauses.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
  The actual representative predicate in `IntegralOperationsWellDefined`
  is exactly `IsKFlatIndependentCoefficients` plus `IsFlatOnSite` in each degree.
- `Sheaf.Paper.PbcCoefficientTwists` publicly retains
  `IntrinsicCoefficientTwists`/`CoefficientTwistsDetailed`: the actual
  `integralTwistLine` and `integralSheafTwist` are used. The primary Qbar
  interface `pbcTateTwist` was read but is not the integral object needed here.

All recorded proof-dependency modules are imported, through the statement imports
or explicitly as non-public imports. No import cycle is introduced.

Sources opened: the item's whole nine-step proof; the current blueprint
`main-20261015/.../prop-weil-twist-preserves.proof.md` and
`.../lem-weil-scalar-extension-composition.proof.md`; the full signatures and
docstrings of the interfaces above. The current blueprint's final sentence
uses integral reductions and common finite stages; the node supplies its
explicit tower-coherence refinement. No source-based correction was needed.

Edge cases checked before and after writing: m=0, m<0 (the signed actual twist
line and its tower map are retained), E=F, F=G, E=F=G (identity AlgHom is allowed,
with both unit equations), ramified inclusions (the image of b is explicitly
mapped by κ; no unramified assumption), C=0 and empty S (no nonempty site,
fibre, faithful-point, or nonzero-section assumption). P may be unbounded; the
line is degree zero. The field, scheme and indexing universes are explicitly
bound; the fixed common universe permits all these objects after the project's
size convention and does not equate site object and morphism universes.

Searches for an existing statement (2026-10-18):

- `msearch.py ... leanfinder "Completed scalar extension of derived complete
  sheaves commutes with Tate twist coherently in a tower of finite l-adic fields"`:
  eight hits, including `AdicCompletion.instIsScalarTower`, LightCondensed
  monoidal/closed instances and `AdicCompletion.ofTensorProduct_naturality`.
  None is this completed integral derived twist square.
- `msearch.py ... leansearch "The canonical Tate twist comparisons commute with
  the associator for completed scalar extension in a tower of finite l-adic
  coefficient fields"`: eight hits, including scalar-tower instances,
  `TensorProduct.AlgebraTensorModule.leftComm`, `Algebra.TensorProduct.assoc`.
  None states this assertion.
- `msearch.py ... loogle "ModuleCat.extendScalars_assoc, TensorProduct.assoc"`:
  zero hits.
- `msearch.py ... grep 'twist.*scalar.*coher|scalar.*twist.*coher|extendScalars_assoc'`:
  four ordinary `ModuleCat.extendScalars_assoc`/pseudofunctor hits; no completed
  sheaf-twist comparison.
- `rg` of the exact node id and twist/scalar/coherence names in
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no exact
  declaration. Upstream `ConstantTwistCohomology` concerns Frobenius constant
  twists and pushforward, not Tate lines and coefficient extension. Side
  `IntegralTwistDerivedScalar`, `IntegralTwistBaseChange` and scalar-composition
  modules supply the separate maps, and are used here instead of restated.

No disputed statement, dependency repair, additional node, or statement change.
Only the main theorem has a postponed proof, with its source and full nine-step
natural-language proof in its docstring.

## Second reading by N5

Reread the original node and the complete final Lean signature clause by clause.
This is the dispatcher's worker's own audit; no separate agent was started,
as instructed. The maintainer supplies the independent delivery review.

Checked the second conjunct's composition order against the node's displayed
right-to-left formula: it is exactly B_GF(β_FE), then β_GF, then W_G(a),
equal to a at C(m), then β_GE. Checked the ordinary normalization against
`a = χ_GE μ d⁻¹`: the first conjunct is precisely `d a = μ χ_GE`.
Checked all source and target objects of the representative equation: its
left side starts in T_GF T_FE(C(m)), reaches Q of the displayed common chain
map using e⁻¹ and the two counits, then reaches W_G B_GE(C) using the actual
completion map and e. Its right side is d at C(m) followed by a at C(m) and
β_GE. Together with the square this specifies BOTH paths. The formula is over
every U and every degree, not just global sections. Rechecked that scalar
multiplication is c*κ(b), so the formula works for genuine inclusions too.

The first compile exposed two syntax/name errors (a broken projection and an
unavailable natural-number lemma); these were repaired. Subsequent typechecking
passed the full coherence and chain-model statements. Long lines were wrapped;
the final verification includes the added identity-multiplication clause.
No hypothesis or clause was changed to repair elaboration.
