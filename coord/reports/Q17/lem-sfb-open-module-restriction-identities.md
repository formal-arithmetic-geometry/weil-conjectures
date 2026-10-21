## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.open_module_restriction_identities`
in `Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities`. Its sole proof is `sorry`.
It asserts the existence of two natural isomorphisms of the specified internal coefficient
module functors. There are no definitions, new nodes, dependency repairs, statement
corrections, or disputed statements.

The source read was
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/lem-sfb-dc-open-lower-shriek-preserves.proof.md`.
Its open-restriction and closed-complement sentences are exactly the two clauses isolated
by this node. The complete five-step node proof is included in the theorem docstring.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| A commutative condensed ring Λ | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ]`, `[IsCommMonObj Λ]` |
| Coefficients Λ_T = p_T^*Λ | Existing `condensedRingObj Λ T`, defined by `upperStarFromPoint` in ModuleObject.Basic |
| Module objects over Λ_U | `Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)` |
| Schemes X, U, Z | `{X U Z : Scheme.{u}}` with explicitly declared `universe u` |
| Quasi-compact open immersion j: U → X | `(j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]` |
| Closed immersion i: Z → X | `(i : Z ⟶ X) [IsClosedImmersion i]` |
| Image of i equals X minus j(U) | `hij : Set.range i = (Set.range j)ᶜ` |
| Actual coefficient module pullbacks | Existing `CondensedRing.upperStar Λ j` and `upperStar Λ i`: `mapMod` followed by `Mod.extendScalars (condensedPullbackHom Λ _)` |
| Coefficient-linear extension by zero j_! | Existing `CondensedRing.openImmersionLowerShriek Λ j`: scalar restriction along the coefficient morphism followed by `linearOpenImmersionLowerShriek` |
| j^*j_!M ≅ M, naturally for every M | First conjunct `Nonempty (openImmersionLowerShriek Λ j ⋙ upperStar Λ j ≅ 𝟭 (...))`; a functor isomorphism is a natural isomorphism whose component at each M is the stated isomorphism |
| i^*j_!M ≅ 0, naturally for every M | Second conjunct is a natural isomorphism from `openImmersionLowerShriek Λ j ⋙ upperStar Λ i` to the constant functor with value the zero object of the internal module category on Z |
| No coefficient finiteness or scheme Noetherian condition | No such binder appears; Λ is arbitrary and the three schemes have only the immersion assumptions shown above |

`Nonempty` records existence of the natural isomorphisms in a proposition, without making
a definition or an arbitrary choice of a functor. The functors themselves are exactly
the recorded canonical constructions. The chosen zero object is the standard categorical
zero object from the existing internal-module category, with the `ZeroObject` scope open.

Dependency declarations read and used:

- `sk-def-sfb-module-objects`: `CategoryTheory.Mod` and its `ModObj` action axioms in
  `Mathlib.CategoryTheory.Monoidal.Mod`; the node's generic definition is instantiated
  at the existing coefficient ring objects, with no duplicate module notion.
- `sk-def-sfb-module-pushforward-pullback`:
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
  Its full definition and docstring were read: transport of abelian inverse image
  followed by extension of scalars along the forward coefficient map.
- `sk-def-sfb-module-lower-shriek`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
  The linearization, scalar restriction, and lifted open adjunction were read.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-finite-type-morphism`: its recorded `AlgebraicGeometry.QuasiCompact`,
  reexported by `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; the quasi-compactness
  class itself and its docstring were read in Morphisms.QuasiCompact.
  No locally-of-finite-type assumption is inserted.
- Proof import `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`:
  `AlgebraicGeometry.ProEtale.InternalModuleOperations.internal_module_operations_transport`,
  `equivalence`, `upperComparison`, `openComparison`, `extension`, and `openAdjunction`.
  These give the comparisons for the actual functors and their adjunctions.
- Proof import `Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed`:
  `AlgebraicGeometry.Scheme.proEtaleIdentifiedOpenClosed`, with its exact signature and
  docstring read: arbitrary coefficient sheaves, complementary closed and quasi-compact
  open immersions, invertible open unit, and zero closed restriction of open extension.
- `WeilConjectures.CategoryTheory.ModuleObjects.Abelian` supplies the existing
  internal-module zero object and its `HasZeroObject` instance; it introduces no new
  mathematical assumption.

Edge cases checked before writing: U empty (extension and both restrictions are zero);
U = X and Z empty (the open composite is the identity and the closed target category is
zero); M = 0; the zero condensed coefficient ring; arbitrary non-Noetherian schemes;
nonreduced closed complements (only their image is prescribed). The universe pattern is
that of the existing small pro-etale module-object framework: Scheme.{u}, site objects
in u+1, and abelian groups in u+1. No independent smaller site or coefficient universe
is imposed. Functor isomorphisms include all objects and morphisms, so naturality is
not replaced by pointwise existence.

Searches performed through the prescribed msearch wrapper, Q17 and this item:

- LeanFinder: `For modules over a commutative condensed ring on the pro etale site extension
  by zero restricts to identity on the open and zero on its closed complement`.
  Eight hits: ModuleCat.Tilde.toOpen_res/res_apply/res_const,
  Scheme.Modules.restrictFunctorId_hom_app_app, and Condensed.profiniteSolid/free helpers.
  None is the two internal coefficient-module restriction identities.
- Loogle: `"openImmersionLowerShriek", "upperStar"`. Zero hits.
- Mathlib grep: `(lowerShriek|extensionByZero).*(restrict|upperStar)|(restrict|upperStar).*(lowerShriek|extensionByZero)`.
  Zero hits.
- LeanSearch: `Extension by zero of internal module objects over a condensed coefficient
  ring restricts to the identity on the open and zero on the complementary closed subscheme`.
  Eight hits, including RingedSpace.res_zero, ContinuousLinearMap.extend_zero,
  Finsupp/DFinsupp, and ContMDiff.extend_zero. None states the item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for extension-by-zero, upperStar,
  restriction and unit names. Read LowerShriek.Defs, UpperLowerStar.Defs,
  LowerShriek.Constructible and the relevant parts of the existing recollement and
  ExchangeMono modules. These contain individual ingredients (and private vanishing
  helpers), but no exact public declaration asserting both natural isomorphisms.
- `rg` for `open_module_restriction_identities`, `OpenModuleRestrictionIdentities`, and
  the node id in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`:
  no existing declaration/name collision or node attachment.

Validation: the prescribed server single-file compile was used. Its first pass required
opening the standard `ZeroObject` scope, which was fixed; no interface repair was needed.
All variables and the universe are explicitly bound, with `autoImplicit false`.

## Second reading by Q17

Author's second pass, performed with the node and complete Lean module open; this is
not represented as an independent review. The dispatcher forbids starting another
agent and assigns independent review to the maintainer.

I rechecked every row above against the final signature. In particular, the closed
image hypothesis has the orientation in the node, both composites use the actual
internal module pullbacks, and the second target is the zero object of the Z-module
category. The two `Nonempty` functor-isomorphism assertions encode naturality, not just
individual object isomorphisms. The three schemes and the condensed ring have no extra
Noetherian, nonempty, nonzero, torsion, finite-type, or coefficient-finiteness restrictions.
Both proof dependencies are imported without `public`; all statement definitions use
recorded declarations. No mismatch or statement correction was found. The only
implementation adjustment was enabling the standard zero-object notation scope.
