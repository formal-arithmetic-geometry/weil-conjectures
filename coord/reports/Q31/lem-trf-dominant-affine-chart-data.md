## Worker report

The delivery states `AlgebraicGeometry.dominant_affine_chart_data` in
`Sheaf.AlgebraicGeometry.DominantAffineChartData`. Its sole proof is `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` field changes. The declaration docstring contains all seven
steps of the DAG proof, with their cited nodes and the germ/localization argument.

Hypotheses and clauses, checked against the node and Stacks Morphisms 0CC1
(`lemma-dominant-between-integral`, lines 1408ff) and 02JU
(`lemma-dimension-formula`, lines 13582ff):

| Informal hypothesis or clause | Lean rendering |
| --- | --- |
| Morphism of integral schemes | `{X S : Scheme.{u}} [IsIntegral X] [IsIntegral S] (f : X ⟶ S)` |
| Image dense in S | `hf : DenseRange f` |
| Locally of finite type | `[LocallyOfFiniteType f]` |
| S locally Noetherian | `[IsLocallyNoetherian S]` |
| Any prescribed affine covering with Noetherian coordinates | Arbitrary `{I : Type v}`, `U : I → S.Opens`, `hU : ∀ i, IsAffineOpen (U i)`, `hN : ∀ i, IsNoetherianRing Γ(S, U i)`, `hcover : iSup U = ⊤` |
| Every x, with s = f(x) | `(x : X)` and the expression `f x` |
| Choose U from the prescribed covering | Existential `i : I`, with base open `U i` throughout |
| Affine neighbourhood V of x inside inverse image of U | Existential `V : X.Opens`, `hV : IsAffineOpen V`, `e : V ≤ f ⁻¹ᵁ U i`; conjuncts `f x ∈ U i` and `x ∈ V` |
| Both neighbourhoods nonempty | `Set.Nonempty (U i : Set S)` and `Set.Nonempty (V : Set X)` |
| A and B are exactly the coordinate section rings | `Γ(S, U i)` and `Γ(X, V)` throughout, without extra arbitrary rings |
| A Noetherian domain, B domain | `IsNoetherianRing Γ(S, U i)`, `IsDomain Γ(S, U i)`, `IsDomain Γ(X, V)` |
| Induced coordinate map, finite type A-algebra, injectivity | Actual map `f.appLE (U i) V e`; `.hom.FiniteType` and `Function.Injective` on this same map |
| Generic points in the chosen opens | `hηS : genericPoint S ∈ U i`, `hηX : genericPoint X ∈ V` |
| Their affine primes are zero | `((hU i).primeIdealOf ⟨genericPoint S, hηS⟩).asIdeal = ⊥` and the analogous formula for `hV` |
| f sends generic point to generic point | `hη : f (genericPoint X) = genericPoint S` |
| R(S), R(X) are the generic stalk fields | Mathlib `S.functionField`, `X.functionField`, definitionally `S.presheaf.stalk (genericPoint S)` and `X.presheaf.stalk (genericPoint X)` |
| The identifications use g_S and g_X | `@IsFractionRing ...` with the Algebra instance explicitly `(presheaf.germ ...).hom.toAlgebra` in each case |
| Fractions have nonzero denominators | `IsFractionRing` is localization at `nonZeroDivisors`; with the two domain conclusions this is precisely the set of nonzero denominators |
| Actual generic stalk map, including its domain transport | `(S.presheaf.stalkCongr (.of_eq hη)).inv ≫ f.stalkMap (genericPoint X)`; the inverse transports the generic target stalk to the stalk at `f (genericPoint X)` |
| Displayed fraction formula for every a,b with b nonzero | The quantified `∀ (a b : Γ(S, U i)), b ≠ 0 → ...` equality, with each quotient using the actual germ maps and `f.appLE` |
| The map extends φ | The quotient formula with b=1 is the commuting germ square, hence specifies the extension on all a |
| Fraction-field embedding, not an unspecified embedding | `Function.Injective` of the actual transported stalk map, and the final `∀ ψ` clause asserting that any ring map agreeing on all base germs equals its `.hom` |

The covering formulation includes the unprescribed existence assertion by applying
it to the affine covering supplied by local Noetherianity. It does not require a
finite covering, a quasi-compact morphism, a perfect base field, or separability.
The index universe `v` is arbitrary; the family consists of opens of the same S,
so no universe-dependent restriction on test objects is hidden here.
`genericPoint` is Mathlib's canonical generic point; the recorded `IsGenericPoint`
interface ensures it is the point of the node, since integral schemes are
irreducible and sober. No extra generic-point hypothesis is imposed.

Dependency declarations read and used (all exact existing notions):

- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`; its `component_integral` and
  `nonempty` fields give the domain/nonempty convention.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; its `finiteType_appLE` is
  exactly the coordinate map used here. Finite type is not assumed globally.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian` (all affine section rings Noetherian,
  equivalent to the node's covering definition).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; the chart primes use the existing
  `IsAffineOpen.primeIdealOf` chart identification, not a new affine model.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  `Mathlib.RingTheory.FiniteType`; the structural map is explicitly specified.
- `def-sc-generic-point`: `IsGenericPoint`, `genericPoint`, `genericPoint_spec`,
  `Mathlib.Topology.Sober`.
- `def-weil-pbc-module-stalk`: `PresheafOfModules.moduleStalkFunctor`,
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`. The full source was read;
  this dependency is usable and is not repaired. The item uses its ring-presheaf
  stalk/germ specialization, the existing `TopCat.Presheaf.stalk` and `germ`
  described by this node's `mathlib_match`; it does not use module stalks here.

The proof-dependency interfaces were also read: `irreducibleComponents`,
`StructureSheaf.IsLocalization.to_stalk`, `functionField_isFractionRing_of_affine`,
`LocallyRingedSpace.Hom`, `Scheme.localRingHom_comp_stalkIso`, and
`Spec.algebraMap_stalkIso_inv`. Their Mathlib modules are already in the public
import closure. `Mathlib.AlgebraicGeometry.FunctionField` supplies the existing
field structures and `functionField_isFractionRing_of_isAffineOpen`; neither is
redefined. The raw germ-map Algebra instance in the signature prevents any
arbitrary identification from entering the fraction-ring assertion.

Edge cases checked before drafting:

- Identity on an integral locally Noetherian scheme: choose the prescribed U
  containing x and an affine V inside it; the generic field map is the identity.
- `Spec k[t] → Spec k`, including the closed and generic points: finite type does
  not mean finite field extension; the map is k into k(t).
- `Spec Z[1/p] → Spec Z` and `Spec k[t,1/t] → Spec k[t]`: dominant need not mean
  surjective; preimages and the canonical fraction-field inclusion are correct.
- Frobenius on the affine line in characteristic p: inseparability is allowed.
- Empty schemes and zero coordinate rings are excluded by integrality, as the
  node requires, rather than by an added nonempty axiom. The empty prescribed
  index set cannot cover the nonempty S; individual empty members are allowed
  but cannot be the chosen member containing f(x).
- A general non-finite-type generic-point inclusion is not covered; the locally
  finite-type hypothesis is retained, not silently replaced by dominance alone.

Searches for existing statements (2026-10-24; prescribed msearch wrapper):

- LeanFinder: `A dominant locally finite type morphism of integral schemes admits
  affine neighborhoods with injective finite type coordinate ring map and
  compatible function field maps` — 8 hits, on rational maps, normalization,
  spreading out and injectivity of germs. No complete match.
- Loogle: `AlgebraicGeometry.LocallyOfFiniteType, AlgebraicGeometry.IsDominant` —
  0 hits.
- LeanSearch: `dominant integral schemes finite type affine neighborhoods fraction
  field germ map` — 8 hits including `germ_injective_of_isIntegral`,
  `functionField_isFractionRing_of_isAffineOpen`, and affine integrality. These
  are ingredients and omit the prescribed covering and canonical stalk-map formula.
- Mathlib grep via msearch: `functionFieldMap|germToFunctionField|genericPoint.*dominant`
  in `AlgebraicGeometry` — 10 hits on germs and order of vanishing, no match.
- Direct rg of `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry`: `dominant.*[Aa]ffine|[Aa]ffine.*[Cc]hart|functionFieldMap|germToFunctionField`;
  the nearby Noether normalization, rational-map and chart results do not state
  this item. More focused `dominant.*affine|affine.*dominant` likewise finds
  normalization, generic fibre and approximation results, not the full assertion.
- Direct rg of `lem-trf-dominant-affine-chart-data` in `lean/WeilConjectures`:
  no match. Direct rg of `dominant_affine_chart_data` in Mathlib,
  `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json`: no match.

No node fault or STATEMENT-DISPUTED issue was found. The item is unchanged.

Validation: `scompile.py Q31 lem-trf-dominant-affine-chart-data
lean/Sheaf/AlgebraicGeometry/DominantAffineChartData.lean` passed both sandbox
and module compilation cleanly. The first draft had a precedence error caused
by a pipeline in the zero-prime conjunct; replacing it with ordinary parentheses
resolved the error. There are no diagnostic commands, file-local notation,
local instances, implicit universes, or hidden auxiliary assumptions.

## Second reading by Q31

With the JSON statement, the final Lean file, and Stacks 0CC1/02JU open, I checked
the hypothesis/clauses table above again. Integrality, density, local finite type
and the locally Noetherian base are all present. The arbitrary supplied covering
is a family of actual affine opens, not arbitrary affine schemes or maps. The
selected i and V contain the required points, and e records precisely f(V) ⊆ U.
A and B are actual sections, and the same `appLE` occurs in finite type,
injectivity, and the quotient formula. The two primes are zero. Both fraction
structures are explicitly tied to the generic germ maps. The `.inv` transport
has domain S's generic stalk and codomain its stalk at f(eta_X), so composition
with the actual stalk map has the direction R(S) → R(X) required by the node.
The b≠0 condition is present, and the uniqueness clause compares against that
canonical map. There is exactly one theorem and one sorry. No mismatch remains.

This is the worker's second pass, not a claim of independent review: the brief
forbids starting other agents and assigns independent review to the maintainer.
