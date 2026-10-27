## Worker report

The delivery states the unchanged node in `Sheaf.Paper.IntegralCoefficientSquareNormalization`.
The main theorem is
`AlgebraicGeometry.ProEtale.IntegralCoefficientSquare.integral_coefficient_square_normalization`.
Its proof is `sorry`; every other declaration is a concrete abbreviation or a Prop-valued
packaging of the clauses of this node, with no postponed data. There are no new DAG nodes,
dependency replacements, or statement corrections.

The earlier worker's reported refusal concerned the already accepted stage-1 split Q111.
This is stage 2: the current node has `status: split`, a reviewed eight-step proof plan,
and no `lean` record. This packet retains that split and changes only `lean`.

Hypotheses and objects:

- The prime ell is `l : ℕ` with `[Fact l.Prime]`.
- The field k of positive characteristic p different from ell is `k : Type u`,
  `[Field k]`, `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]`, `_hp : p ≠ l`.
  A field of positive characteristic has prime characteristic, so this is the same setting.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`. `IntegralAssertions` fixes the recorded extending absolute
  value topology, `Padic.coefficientExtensionIntegers l E`, and the recorded chosen
  `Padic.coefficientExtensionUniformizer l E`; it asks for no additional topology or
  arbitrary coefficient presentation.
- X and Y are `Over (Spec (.of k))` with `LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated` on each structure morphism. These are precisely separated finite-type
  k-schemes. `g : X ⟶ Y` is a k-morphism, used as `g.left` on the pro-etale sites.
- The site is always `Scheme.ProEt.topology T`, with object universe u+1 and arrow
  universe u; abelian coefficients and section modules have universe u+1. No equality
  between the site object and morphism universes is imposed.
- `constantPoint A` is the recorded `constantSheaf` on Profinite applied to lifted A;
  its pullback `condensedRingObj (constantPoint A) T` is C_T. The existing monoidal
  `constantSchemeIso T` identifies it canonically with the constant sheaf on T.
- R_T is `condensedRingObj (Profinite.continuousCoefficientRingObj A) T`;
  `sectionRingSheaf` gives the commutative ring-sheaf presentation of that same ring.
- `scalar A T` is the recorded `AdmissibleScalarRealization.scalarMap A T`, the pullback
  of `FiniteConstantModel.scalarToContinuous A`. Under `constantSchemeIso` this is
  exactly `FiniteDiscreteOrdinary.canonicalAbelianMap A T`, not an arbitrary ring map.
- Restriction is `Mod.comap (scalar A T)` in the internal module presentation.
  The recorded general `SheafOfModules.restrictScalars` is the sectionwise realization
  of the same operation, as proved by the existing section-module equivalence APIs.
  Both preserve underlying abelian sheaves and restrict the scalar action through i_T.
- Both module pullbacks are the recorded `CondensedRing.upperStar`, i.e. inverse image
  followed by `Mod.extendScalars` along `condensedPullbackHom`. In particular the tensor
  extension has not been replaced with an independently chosen inverse-image lift.

Conclusions, in the order of `Assertions`:

- `RingAssertions A p X` and `RingAssertions A p Y` provide a ring-sheaf isomorphism e
  from the actual R_T to `Scheme.adicLisseCompletedRing T (span {ULift.up p})`.
  That target is the inverse limit of the actual positive constant quotient rings.
  The displayed equation on every object U, scalar a, and index n says the prescribed
  projection of i_T(a) is its residue modulo p^(n+1). This is the exact normalization
  of the canonical limit projections in the node.
- The second part of `RingAssertions` states `IsPushout` of C_T -> R_T and
  C_T -> constant(A/p^(n+1)), with R_T -> S_(n+1) equal to e followed by the prescribed
  limit projection and the fourth map the identity. A pushout of commutative rings
  over a quotient is R_T/p^(n+1)R_T; the same universal property in ring sheaves is
  the sheaf quotient. Thus this states the claimed quotient isomorphism with exactly
  its prescribed projection, rather than existence of an unspecified isomorphism.
  The top arrow is `CompletedConstantReduction.base ≫ e.inv`; the first clause's
  scalar equation identifies it with the actual constant-function map. This follows
  on all of C_T by the constant-sheafification universal property.
- Flatness is `SheafOfModules.IsFlatOnSite` on the section-module presentation of
  `restriction A T` applied to the regular R_T module, for T=X and T=Y.
  The restricted module has precisely the C_T-action through i_T.
- The coefficient square is the equality
  `(upperStar Ab g).map (scalar A Y) ≫ condensedPullbackHom R g =
   condensedPullbackHom C g ≫ scalar A X`.
  Category-theoretic composition runs left to right, so this is exactly
  a_R g^{-1}i_Y = i_X a_C.
- `GeneratorNormalization` for R and C states the two requested formulas on all
  scalar-extension generators as equalities of abelian-sheaf morphisms.
  Composing `Mod.extendπ` with `underlyingIso.hom` equals inverse(alpha) tensor the
  identity followed by the transported module action. This is r tensor h -> alpha^-1(r)h.
  `underlyingIso.inv = Mod.extendUnitHom ...` is h -> 1 tensor h.
  The existing `cartesianCoefficientPullbackIso` fixes which isomorphism is normalized.
- The existential `d` is an isomorphism of functors on `CochainComplex ... ℤ` from
  g_R^* followed by r_X to r_Y followed by g_C^*. Consequently it includes naturality,
  a chain inverse and compatibility with every differential, for arbitrary H.
  Its equation in every q says its underlying map, followed by the C-side
  `underlyingIso.hom`, is the R-side `underlyingIso.hom`. Therefore it is the identity
  on g^{-1}H under those specified identifications. Together with the two generator
  normalizations this fixes d on all scalar-extension generators, including its inverse,
  and entails agreement of the C_X-actions through the commuting square.
- The two `exactFunctor` clauses state exactness on all module sheaves of g_R^*, g_C^*.
- `FlatKFlat` is precisely the conjunction of the recorded
  `CochainComplex.IsKFlatIndependentCoefficients` on the section-equivalence image and
  `∀ q : ℤ, SheafOfModules.IsFlatOnSite` on its terms. The existing
  `InternalAbelianSheafModule.internal_section_tensor_comparison` identifies this
  encoding with the internal total-tensor/acyclic-complex definition, including
  unbounded direct-sum totalization.
  The last clause quantifies over every P and asserts, assuming P flat K-flat over R_Y,
  all three required results: r_YP over C_Y, g_R^*P over R_X, and g_C^*r_YP over C_X.
  There is no boundedness, constructibility, or completeness assumption anywhere.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  and its public `CoefficientExtension` data: `coefficientExtensionAbsoluteValue`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its explicit
  separated finite-type over-field setting. No compactification is needed for this lemma.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `condensedPullbackHom`, `coefficientPullbackIso`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`;
  internal presentation uses the existing `Mod.comap` with the same section action.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.upperStar`, `upperStar_obj`, and its additive/exactness interfaces.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`
  and `CategoryTheory.exactFunctor`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the
  recorded total tensor used by the K-flat predicate.

Every stated proof dependency is imported, with plain imports when only the proof
uses it. The helper `underlyingIso` uses the existing Cartesian comparison and has
real data. The eight-step proof docstring records the node's complete proof plan,
including scalar normalization, tensor balancing, chain naturality, exactness and
both applications of the general ringed-topos K-flat pullback theorem.

Sources opened: the entire current blueprint proof
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-pullback.proof.md`,
Stacks `sites-modules.tex` lemma-completion-flat (Tag 093M), and
`sites-cohomology.tex` lemma-pullback-K-flat (Tag 0G7E).

Edge cases checked before writing: n=1 is index zero in the positive tower, so no
positive quotient is omitted; there is no n=0 quotient claim. The identity morphism
uses the canonical coefficient comparison, with no arbitrary automorphism. Empty
schemes still have the specified coefficient sheaves, limits and quotient pushouts;
there is no nonempty-site or geometric-point assumption. Zero H and P satisfy the
chain and K-flat clauses. Arbitrarily unbounded complexes are allowed, and every
normalization is degreewise for all q in ℤ, not restricted to cohomology degrees.
Uniformizer is the dependency's chosen uniformizer, as specified by that dependency.

Searches performed on 2026-10-22:

- `msearch.py ... leanfinder`: “Constant and completed integral coefficient ring sheaves
  form a commuting pullback square and restriction of scalars commutes with exact
  pullback preserving K-flat complexes”. Eight hits, including
  `SheafOfModules.pullbackComp`, `pullbackObjFreeIso`, and free-pullback normalization
  lemmas. None states this coefficient-square/quotient/unbounded-complex assertion.
- `msearch.py ... loogle "SheafOfModules.restrictScalars"`: four hits, the restriction
  functor, its additive instance, and its object/map equations; reused rather than copied.
- `msearch.py ... grep "(restrictScalars|pullback).*(KFlat|[Ff]lat)|[Cc]oefficient.*[Ss]quare"
  CategoryTheory`: no matches.
- `rg` of the exact node id in `lean/WeilConjectures` and `lean/Sheaf`: no declaration.
- `rg` of constant/integral/square, scalarToContinuous and normalized coefficient
  expressions in both roots located the existing scalar, Cartesian and completed
  coefficient interfaces used above. None gives the combined node statement.
- Targeted `rg` and source reads in pinned Mathlib located the exact constant-sheaf,
  restriction, cochain, total tensor and ring-sheaf pushout definitions; no private
  replacements were introduced.

No `STATEMENT-DISPUTED` flag or mathematical node fault remains. Compilation through
scompile.py succeeds for the sandbox module and its actual library module name,
with no error or non-sorry warning. The dry run and delivery are recorded below.

Validation: deliver2.py --no-push printed OK: commit 37518f64afa passes the preflight
and compiles; nothing pushed. Direct delivery follows the successful dry run.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
