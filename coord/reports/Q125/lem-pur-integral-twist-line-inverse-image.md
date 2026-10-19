## Worker report

Item: `lem-pur-integral-twist-line-inverse-image`. The module
`Sheaf.Paper.PurIntegralTwistLineInverseImage` states all four clauses in
`AlgebraicGeometry.Scheme.pur_integral_twist_line_inverse_image`, with `sorry` as its
only theorem proof. The five auxiliary declarations have concrete data: they expose
an existing underlying sheaf and scalar map, and spell out three predicates for the
projection and section formulas. There are no new independent notions, no dependency
repairs, and no statement correction. The original node changes only in `lean`.

Source read: current main-20261015 blueprint,
`sec-smooth-purity/sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.proof.md`,
especially “Roots of unity” and “The integral twist”, and the target node's five proof
steps. The module docstring carries their limit, compatible-basis, tensor and
field-inclusion arguments, naming all proof dependencies. The still-unstated proof
nodes are cited in that docstring but cannot yet be imported:
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`det-prop-sfb-qlbar-colimit-x-pullback`,
`det-def-sp-tate-twist-locally-free`, and
`det-prop-sfb-cartesian-coefficients-twists`. All recorded proof modules are imported,
with proof-only dependencies imported non-publicly.

Hypothesis and clause correspondence:

- `h : X ⟶ Y` is the arbitrary scheme morphism `S' → S`; there is no restriction on
  the morphism. `l : ℕ` and `[Fact l.Prime]` give the prime. The two instances
  `[∀ x : X, Invertible (l : X.residueField x)]` and the analogous instance on `Y`
  give invertibility on both schemes, including the empty scheme.
- `E F : Type u`, their `Field`, `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]`
  instances give arbitrary finite coefficient extensions. `ι : E →ₐ[ℚ_[l]] F`
  expresses the specified inclusion, without imposing a tower of chosen field
  models. Algebra homomorphisms of these fields are injective. The valuation rings,
  uniformizer quotient ideals, and quotient rings are the recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionIdeal`, and
  `coefficientExtensionRing`. Uniformizer powers occur at exponent `n+1`.
- The theorem presents the comparisons for an arbitrary pair `E → F` together.
  Taking `E = F = H` and `ι = AlgHom.id ℚ_[l] H` gives clauses 1–3 for every finite
  extension `H`, so the pair formulation adds no hypothesis to those clauses.
- Clause 1: the first two conjuncts say `IsIso αE`/`IsIso αF` and
  `IsPurIntegralCoefficientComparison h l E αE` (respectively `F`). This predicate
  states for every `n` exactly `α ≫ π_n = h⁻¹(π_n) ≫ γ`. The finite constant map is
  `proEtaleConstantInverseImageMap` in `CommRingCat`, the recorded constant-section
  adjunct with commutativity retained. It is the same map as the finite-ring
  dependency under its unique constant-preserving identifications. The actual
  completed sheaf is `completedIntegralCommRingSheafUnrestricted`; its underlying
  ring sheaf is the recorded inverse limit, not a discrete constant sheaf.
- Clause 2: `IsIso τ ∧ IsPurRootLimitComparison h l τ`. The predicate uses every
  projection `limit.π (proEtaleRootsOfUnityTower ... l ...) (op n)` and the recorded
  `proEtaleRootsOfUnityInverseImageMap h (l^(n+1))`. Thus its equation is precisely
  `pr_r ∘ τ = c_mu ∘ h⁻¹(pr_r)` with all positive `r` present. The root tower has
  exactly the prescribed power transitions.
- Clause 3: `IsIso ρE` and `IsIso ρF` are isomorphisms of underlying abelian sheaves;
  their additional predicate `IsPurIntegralTwistComparison` specifies the tensor
  formula and completed semilinearity. `purIntegralTwistAb` is merely
  `SheafOfModules.toSheaf` applied to the existing `purTwistIntegralModule`; its
  underlying object is exactly the prescribed `purTwistIntegralOne`, equipped with
  the existing completed action. It is not a new line.
- The first part of `IsPurIntegralTwistComparison` applies the actual adjunction
  `proEtaleSheafAdjunction.homEquiv` to `ρ` and `τ`. At every `V` on `Y`, it sends
  `purTwistIntegralTensor Y l H V b t` to the tensor of the constant-sheaf
  direct-image comparison applied to `b` and the adjunct of `τ` applied to `t`,
  evaluated at `(proEtaleBaseChange h).op.obj V`. For a constant `a ∈ O_H` the
  first factor is the same `a`. This is the node's local pure-tensor formula,
  expressed on the defining local generators of inverse image. We quantify over
  all local scalar sections `b`; these are locally constant scalars by
  sheafification, so this is equivalent to the constant-section formula.
- The second part of that predicate says the adjunct of `ρ` sends `a • t` to
  `adjunct(α)(a) • adjunct(ρ)(t)`, with the *recorded completed action* on each side.
  This is the adjoint formulation of semilinearity over `α`: inverse image is the
  sheafified colimit of these local generators, its action is induced from the
  source action, and it preserves finite products. Hence semilinearity of the
  adjunct on these generators is equivalent to semilinearity of `ρ` on the actual
  inverse-image module. No arbitrary module action or comparison is assumed.
  Explicit `@id` terms only expose the target ring/module types for instance
  synthesis; they do not cast between different mathematical objects.
- Clause 4, coefficient square: the penultimate conjunct is
  `h⁻¹(integralCompletedScalarMap ... Y) ≫ αF =
   αE ≫ integralCompletedScalarMap ... X`. This uses the existing completed
  inclusion determined by its finite quotient maps. Those maps use a sufficiently
  large source exponent; agreement for all other allowable exponents follows by
  quotient compatibility. No same-uniformizer or unramified hypothesis is added.
- Clause 4, twist square: the last conjunct is
  `h⁻¹(purIntegralTwistScalarMap Y ...) ≫ ρF =
   ρE ≫ purIntegralTwistScalarMap X ...`. The helper only forgets scalar linearity
  from the *existing* `twistScalarMaps ... 1`, whose normalization is
  `t ⊗ a ↦ t ⊗ ι(a)`. It contains no new map choice. Both squares use the very
  same `α`, `τ`, and `ρ` from the preceding clauses.

The existential comparisons are not arbitrary maps: their projection and local-tensor
conditions determine them uniquely by the inverse-limit universal property and local
pure-tensor generation. No definition chooses data from the new theorem. An underlying
abelian isomorphism semilinear over a ring isomorphism has the corresponding semilinear
inverse, so clause 3 is the specified semilinear isomorphism.

Dependency declarations read and used (including docstrings and full signatures):

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology`; site objects stay in universe `u+1` and morphisms in `u`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleConstantDirectImageMap`, `proEtaleConstantInverseImageMap`. These are
  the recorded Kan-extension/sheafification inverse image, actual adjunction, and
  normalized constant-section maps; no replacement inverse image is introduced.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its reexported
  `CompletedIntegralCoefficients`: `integralConstantToCompletionOfUniverses`,
  `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`,
  `integralCoefficientCommRingSheaf`. The recorded constant map is not needed in
  the signature; its actual quotient/completion objects are used unchanged.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityTower`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.limit` and
  `limit.π`, rather than a second limit construction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` and the
  reexported tensor/scalar-extension constructions used by the recorded twist line.
- `Sheaf.Paper.CoefficientTwistsDetailed`: `integralTwistLine`,
  `twistScalarMaps`, `IsCanonicalTwistScalarMaps`; its imported
  `IntegralScalarExtension` supplies `integralCompletedScalarMap`. At twist one
  `integralTwistLine` is definitionally the existing integral module.
- `Sheaf.Paper.PurTwistSheafLocallyFree`: `purTwistZlOne`,
  `purTwistZlModule`, `purTwistIntegralOne`, `purTwistIntegralTensor`,
  `purTwistIntegralModule`, and their actual completed scalar actions.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `finiteCoefficientInverseImageMap_isIso`,
  `finiteCoefficientInverseImageMap_constant`, giving the constant-preserving
  identification of its comparison with the one in the projection equation.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`:
  `proEtaleRootsOfUnityInverseImageMap`, the adjunct of the pullback-of-roots map.

Edge cases checked before writing and again against the signature: empty schemes
(no `Nonempty` assumption; all section formulas reduce to the singleton sheaves),
identity scheme maps, identity and nontrivial field inclusions, ramified extensions
(the existing completed scalar map allows different quotient indices), `l=2`,
level `n=0` (means exponent one, not exponent zero), and the full positive root
tower. In characteristic `l`, the stated invertibility hypothesis correctly fails
on a nonempty scheme. No field-characteristic condition on schemes other than the
node's invertibility is imposed. The coefficient/module size is `u+1`; the small
site's distinct object/morphism universes are retained. Every variable and universe
is bound explicitly with `autoImplicit false`.

Searches (no exact existing theorem found):

- `msearch.py`, LeanFinder: “Inverse image of completed integral Tate twist line
  compatible with finite coefficient field inclusions”: eight completion/p-adic
  ring hits, including `AdicCompletion.piEquivFin`; no sheaf Tate-twist comparison.
- `msearch.py`, Loogle: `IsIso, CategoryTheory.Limits.limit`: zero hits, service
  reported unknown identifier `IsIso`; no match was inferred from this failure.
- `msearch.py`, grep: `TateTwist|purTwist|integralTwist` in Mathlib
  `AlgebraicGeometry`: zero hits.
- `msearch.py`, LeanSearch: “The inverse image of the completed integral Tate twist
  line is canonically isomorphic to the twist line after base change, compatibly
  with coefficient embeddings”: eight generic root-system, completion, dual base
  change and lattice hits; none is a pro-etale sheaf comparison.
- `rg` over upstream `WeilConjectures` and side `lean/Sheaf` for the node id and
  `purTwist.*Inverse|integral.*[Ii]nverse.*[Tt]wist`: no whole theorem match.
- `rg` over upstream Mathlib, upstream `WeilConjectures`, side `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `purIntegralTwist` and
  `pur_integral_twist_line_inverse_image`: no existing declarations with these
  names. The side-source inspection did locate all the reused root, tensor,
  completed-action and scalar-inclusion constructions listed above.

No `STATEMENT-DISPUTED` issue or node fault was found. Compilation is exclusively
through `scompile.py`, followed by the prescribed `deliver2.py --no-push` preflight
and final delivery. The initial compile diagnosed a missing invertibility binder on
the helper using `twistScalarMaps` and an ambiguous target scalar action; both were
repaired without changing the mathematical statement.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
